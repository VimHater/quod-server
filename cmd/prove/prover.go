package main

import (
	"context"
	"crypto/sha256"
	"encoding/hex"
	"fmt"
	"io"
	"log/slog"
	"os"
	"path/filepath"
	"strings"
	"sync/atomic"
	"time"

	"mathprover/internal/daemon"
	"mathprover/internal/lean"
	"mathprover/internal/llm"
	"mathprover/internal/pipeline"
)

// leanSettings are fixed for the lifetime of a prover (changing them needs
// a restart): which Lean project, how many workers, what they import, how
// they are isolated.
type leanSettings struct {
	Dir          string
	Workers      int
	Imports      []string
	StartTimeout time.Duration
	CmdTimeout   time.Duration
	Sandbox      lean.Sandbox
	// Verify re-checks finished proofs independently (lean.Verifier).
	Verify bool
}

func (ls leanSettings) config() lean.Config {
	return lean.Config{
		ProjectDir: ls.Dir, StartTimeout: ls.StartTimeout, CmdTimeout: ls.CmdTimeout,
		Imports: ls.Imports, Sandbox: ls.Sandbox,
	}
}

// prover is a warm Lean pool plus an LLM client; it runs jobs with per-job
// settings (models, attempts, ...). Used directly in local mode and behind
// the socket in -serve mode. Every job gets its own lease on fresh
// workers, discarded when it ends, so jobs cannot affect each other.
type prover struct {
	lean        leanSettings
	client      *llm.Client
	pool        *lean.Pool
	verifier    pipeline.Verifier // nil without -verify
	leanVersion string
	names       atomic.Pointer[lean.NameIndex] // nil until loaded
}

func startProver(ctx context.Context, ls leanSettings) (*prover, error) {
	client, err := llm.NewClientFromEnv()
	if err != nil {
		return nil, err
	}
	leanVersion := "Lean 4 + Mathlib"
	if tc, err := os.ReadFile(filepath.Join(ls.Dir, "lean-toolchain")); err == nil {
		v := strings.TrimSpace(string(tc))
		v = v[strings.LastIndex(v, ":")+1:]
		leanVersion = fmt.Sprintf("Lean %s, Mathlib %s", v, v)
	}
	if ls.Sandbox.Kind == lean.SandboxNone {
		progress("warning: -sandbox none runs model-written Lean code unconfined; use it only with trusted input")
	}

	progress("starting %d Lean worker(s) (imports %s)...", ls.Workers, strings.Join(ls.Imports, ", "))
	t0 := time.Now()
	pool, err := lean.NewPool(ctx, lean.PoolConfig{
		Config:      ls.config(),
		Size:        ls.Workers,
		MaxCommands: 500,
		Logger:      slog.New(slog.NewTextHandler(io.Discard, nil)),
	})
	if err != nil {
		return nil, fmt.Errorf("lean: %w", err)
	}
	progress("Lean ready in %s", time.Since(t0).Round(100*time.Millisecond))
	p := &prover{lean: ls, client: client, pool: pool, leanVersion: leanVersion}
	if ls.Verify {
		v, err := lean.NewVerifier(ctx, lean.VerifierConfig{Config: ls.config()})
		if err != nil {
			pool.Close()
			return nil, fmt.Errorf("verifier: %w", err)
		}
		p.verifier = v
	}
	go p.loadNames()
	return p, nil
}

// loadNames builds the declaration-name index used for "did you mean"
// hints, from a cache file keyed by the Lean setup, or by asking Lean.
// Until it is ready (or if it fails) proofs simply get no hints.
func (p *prover) loadNames() {
	path, err := p.namesCachePath()
	if err == nil {
		if idx, err := lean.LoadNameIndex(path); err == nil && idx.Len() > 0 {
			p.names.Store(idx)
			progress("name hints ready: %d declarations (cached)", idx.Len())
			return
		}
	}
	if err != nil {
		progress("name hints disabled: %v", err)
		return
	}
	ctx, cancel := context.WithTimeout(context.Background(), 15*time.Minute)
	defer cancel()
	t0 := time.Now()
	tmp := path + ".tmp"
	// A one-shot Lean process of its own (see lean.DumpNames): a sandboxed
	// worker cannot write the file, and jobs keep every worker.
	_, err = lean.DumpNames(ctx, p.lean.config(), tmp)
	if err == nil {
		err = os.Rename(tmp, path)
	}
	var idx *lean.NameIndex
	if err == nil {
		idx, err = lean.LoadNameIndex(path)
	}
	if err != nil {
		os.Remove(tmp)
		progress("name hints disabled: %v", err)
		return
	}
	p.names.Store(idx)
	progress("name hints ready: %d declarations indexed in %s", idx.Len(), time.Since(t0).Round(100*time.Millisecond))
}

// namesCachePath is ~/.quod/names/<hash of Lean dir, imports, toolchain
// and dependency pins>.txt, so any change to those makes a new dump.
func (p *prover) namesCachePath() (string, error) {
	home, err := os.UserHomeDir()
	if err != nil {
		return "", err
	}
	dir, err := filepath.Abs(p.lean.Dir)
	if err != nil {
		return "", err
	}
	h := sha256.New()
	fmt.Fprintf(h, "%s\n%s\n", dir, strings.Join(p.lean.Imports, ","))
	for _, f := range []string{"lean-toolchain", "lake-manifest.json", "Harness/Names.lean"} {
		b, _ := os.ReadFile(filepath.Join(dir, f))
		h.Write(b)
	}
	cache := filepath.Join(home, ".quod", "names")
	if err := os.MkdirAll(cache, 0o700); err != nil {
		return "", err
	}
	return filepath.Join(cache, hex.EncodeToString(h.Sum(nil))[:16]+".txt"), nil
}

// Suggest implements pipeline.Suggester: similar existing names with their
// signatures, for each identifier Lean did not know. The signatures come
// from the job's own worker.
func (p *prover) Suggest(ctx context.Context, c pipeline.Checker, unknown []string) string {
	idx := p.names.Load()
	if idx == nil {
		return ""
	}
	var b strings.Builder
	for _, id := range unknown {
		if idx.Has(id) {
			continue // exists; the problem is elsewhere (e.g. a missing `open`)
		}
		cands := idx.Similar(id, 5)
		if len(cands) == 0 {
			continue
		}
		sigs, _ := lean.Signatures(cands, func(code string) (*lean.Result, error) {
			return c.Query(ctx, nil, code, time.Minute)
		})
		fmt.Fprintf(&b, "`%s` does not exist. Existing declarations with similar names:\n", id)
		for _, name := range cands {
			sig := sigs[name]
			if sig == "" {
				sig = name
			}
			if r := []rune(sig); len(r) > 400 {
				sig = string(r[:400]) + " ..."
			}
			fmt.Fprintf(&b, "  - %s\n", sig)
		}
	}
	if b.Len() == 0 {
		return ""
	}
	return b.String() + "Use one of these if it states what you need (check its arguments), otherwise prove the fact another way.\n"
}

func (p *prover) Close() { p.pool.Close() }

// jobStages is the proof-search ladder for job: a single stage at
// job.Effort if set, else the named presets (default ladder if none).
func jobStages(job daemon.Job) ([]pipeline.Stage, error) {
	if job.Effort != "" {
		return []pipeline.Stage{{Name: job.Effort, Spec: llm.ModelSpec{Model: job.Model, Effort: llm.Effort(job.Effort)}, Sessions: 1, Attempts: 6}}, nil
	}
	names := job.Stages
	if len(names) == 0 {
		names = pipeline.DefaultStageNames
	}
	return pipeline.NamedStages(job.Model, names)
}

// run proves job.Input with the job's settings.
func (p *prover) run(ctx context.Context, job daemon.Job, hooks pipeline.Hooks) (*pipeline.Result, error) {
	if job.Timeout > 0 {
		var cancel context.CancelFunc
		ctx, cancel = context.WithTimeout(ctx, job.Timeout)
		defer cancel()
	}
	stages, err := jobStages(job)
	if err != nil {
		return nil, err
	}
	models := llm.DefaultModels()
	// The outline stage talks to Prove; the ladder's stages set their own.
	models.Prove = llm.ModelSpec{Model: job.Model, Effort: llm.EffortHigh}
	if job.Effort != "" {
		models.Prove.Effort = llm.Effort(job.Effort)
	}
	for _, s := range []*llm.ModelSpec{&models.Split, &models.Formalize, &models.Back, &models.Judge, &models.Explain} {
		s.Model = job.AuxModel
		if s.Effort == llm.EffortNone {
			s.Effort = llm.Effort(job.AuxEffort)
		}
	}
	client := p.client
	if job.BaseURL != "" {
		client = llm.NewClient(job.APIKey)
		client.BaseURL = strings.TrimRight(job.BaseURL, "/")
	}
	agent := llm.NewAgent(client, llm.Options{
		Models: models, LeanVersion: p.leanVersion, BudgetUSD: job.BudgetUSD, Imports: p.lean.Imports,
	})
	checker, release, err := pipeline.PoolSource{Pool: p.pool}.JobChecker(ctx)
	if err != nil {
		return nil, err
	}
	defer release() // the job's workers are discarded, never reused
	pl := pipeline.New(agent, checker, pipeline.Options{
		Stages:              stages,
		MaxProofAttempts:    job.Attempts,
		ParallelSessions:    job.Parallel,
		NoAutomation:        job.NoAuto,
		SkipSplit:           job.NoSplit,
		NoExplain:           job.NoExplain,
		LeanHeader:          "import " + strings.Join(p.lean.Imports, "\nimport "),
		Verifier:            p.verifier,
		Suggester:           p,
		NoFaithfulnessCheck: job.NoFaithCheck,
		NoDisprove:          job.NoDisprove,
		NoPlan:              job.NoPlan,
		PlanAttempts:        job.PlanAttempts,
		StepAttempts:        job.StepAttempts,
		PlanAfter:           job.PlanAfter,
	})
	return pl.Run(ctx, job.Input, hooks)
}

package pipeline

import (
	"context"
	"errors"
	"fmt"
	"regexp"
	"sort"
	"strings"
	"sync"
	"time"

	"mathprover/internal/lean"
	"mathprover/internal/llm"
)

// Options tunes a Pipeline. Zero values get defaults.
type Options struct {
	MaxFormalizeAttempts int // Lean-rejected formalizations before giving up; default 3
	MaxRevisions         int // user corrections per statement; default 3
	// Stages is the escalation ladder for proof search; nil means
	// DefaultStages(the agent's prover model).
	Stages []Stage
	// MaxProofAttempts and ParallelSessions, if > 0, override every
	// stage's Attempts and Sessions.
	MaxProofAttempts int
	ParallelSessions int
	// Automation tactics are tried directly in Lean before any LLM call;
	// nil means DefaultAutomation. NoAutomation skips this step.
	Automation    []string
	NoAutomation  bool
	SkipSplit     bool // treat the whole input as one statement
	NoExplain     bool
	MaxStatements int // reject inputs that split into more; 0 = unlimited
	// LeanHeader starts LeanFile; default "import Mathlib\nimport Harness".
	LeanHeader string
	Feedback   lean.FeedbackOptions
	// Verifier, if set, re-checks every proved statement independently at
	// the end of the job; a statement only stays "proved" if it passes.
	Verifier Verifier
	// Suggester, if set, adds similar existing names to the feedback for
	// "unknown identifier" errors.
	Suggester Suggester
	// KeepSearchTactics leaves exact?/apply?/simp? in verified proofs
	// instead of replacing them with Lean's "Try this" suggestions.
	KeepSearchTactics bool
	// NoFaithfulnessCheck skips the independent check that the Lean
	// statement says what the text says. FaithfulnessFixes is how many
	// times a mismatch sends the statement back to be re-formalized
	// (default 1; negative = never).
	NoFaithfulnessCheck bool
	FaithfulnessFixes   int
	// NoDisprove skips looking for evidence that a statement is false: a
	// counterexample before proving, and proving the negation after the
	// proof attempts fail (DisproveAttempts, default 3).
	NoDisprove       bool
	DisproveAttempts int
	// ClaimDisproveAttempts is how many negation attempts follow a FALSE
	// reply (default 1). A right claim has always been confirmed on the
	// first try; a wrong one should cost little before proving resumes.
	ClaimDisproveAttempts int
	// NoPlan skips the outline stage (A3) after direct proof attempts fail:
	// the model writes have-steps and a proof from them, each step is then
	// proved on its own. PlanAttempts bounds the outlines (default 4),
	// StepAttempts the proof attempts per step (default 4).
	NoPlan       bool
	PlanAttempts int
	StepAttempts int
	// PlanAfter caps the direct proof attempts while the outline stage is on
	// (default 3): problems solved directly are solved within the first few
	// attempts, and later direct attempts rarely help where an outline does.
	// Negative: no direct attempts, start with the outline.
	PlanAfter int
}

func (o Options) withDefaults() Options {
	if o.MaxFormalizeAttempts <= 0 {
		o.MaxFormalizeAttempts = 3
	}
	if o.MaxRevisions <= 0 {
		o.MaxRevisions = 3
	}
	if o.LeanHeader == "" {
		o.LeanHeader = "import Mathlib\nimport Harness"
	}
	if o.FaithfulnessFixes == 0 {
		o.FaithfulnessFixes = 1
	}
	if o.DisproveAttempts <= 0 {
		o.DisproveAttempts = 3
	}
	if o.ClaimDisproveAttempts <= 0 {
		o.ClaimDisproveAttempts = 1
	}
	if o.PlanAttempts <= 0 {
		o.PlanAttempts = 4
	}
	if o.StepAttempts <= 0 {
		o.StepAttempts = 4
	}
	if o.PlanAfter == 0 {
		o.PlanAfter = 3
	}
	return o
}

// Stage is one rung of the proof-search ladder.
type Stage struct {
	Name     string        `json:"name"`
	Spec     llm.ModelSpec `json:"spec"`
	Sessions int           `json:"sessions"` // parallel sessions racing
	Attempts int           `json:"attempts"` // propose→check rounds per session
	// Tools lets the model look up lemmas and test proofs in Lean while it
	// works (search_lemmas, check_name, find_lemma, check_proof).
	Tools        bool `json:"tools,omitempty"`
	MaxToolCalls int  `json:"max_tool_calls,omitempty"` // per attempt; default 16
}

// StagePresets are the named stages for model. "fast" is many cheap,
// non-thinking attempts (Lean's fast feedback does the checking); "tools"
// lets a non-thinking model look up lemmas and test proofs in Lean; "think"
// and "deep" are slower, deliberate attempts ("deep" with tools too).
// Measured on easy Mathlib goals, thinking time is dominated by the model
// second-guessing lemma names it cannot look up, not by the mathematics.
func StagePresets(model string) map[string]Stage {
	if model == "" {
		model = llm.ModelFlash
	}
	spec := func(e llm.Effort) llm.ModelSpec { return llm.ModelSpec{Model: model, Effort: e} }
	fast := spec(llm.EffortNone)
	fast.MaxTokens = 4096
	return map[string]Stage{
		"fast":       {Name: "fast", Spec: fast, Sessions: 4, Attempts: 3},
		"tools":      {Name: "tools", Spec: spec(llm.EffortNone), Sessions: 2, Attempts: 3, Tools: true},
		"tools-low":  {Name: "tools-low", Spec: spec(llm.EffortLow), Sessions: 2, Attempts: 3, Tools: true},
		"think":      {Name: "think", Spec: spec(llm.EffortLow), Sessions: 2, Attempts: 3},
		"deep":       {Name: "deep", Spec: spec(llm.EffortHigh), Sessions: 2, Attempts: 4},
		"deep-tools": {Name: "deep-tools", Spec: spec(llm.EffortHigh), Sessions: 2, Attempts: 3, Tools: true},
	}
}

// DefaultStageNames is the default ladder.
var DefaultStageNames = []string{"fast", "tools", "deep-tools"}

// DefaultStages is the default ladder on model.
func DefaultStages(model string) []Stage {
	st, _ := NamedStages(model, DefaultStageNames)
	return st
}

// NamedStages builds a ladder from preset names (see StagePresets).
func NamedStages(model string, names []string) ([]Stage, error) {
	presets := StagePresets(model)
	var out []Stage
	for _, n := range names {
		n = strings.TrimSpace(n)
		if n == "" {
			continue
		}
		st, ok := presets[n]
		if !ok {
			var known []string
			for k := range presets {
				known = append(known, k)
			}
			sort.Strings(known)
			return nil, fmt.Errorf("unknown stage %q (known: %s)", n, strings.Join(known, ", "))
		}
		out = append(out, st)
	}
	if len(out) == 0 {
		return nil, errors.New("no stages given")
	}
	return out, nil
}

func (p *Pipeline) stages() []Stage {
	st := p.opts.Stages
	if st == nil {
		st = DefaultStages(p.agent.Models().Prove.Model)
	}
	out := make([]Stage, len(st))
	for i, s := range st {
		if p.opts.ParallelSessions > 0 {
			s.Sessions = p.opts.ParallelSessions
		}
		if p.opts.MaxProofAttempts > 0 {
			s.Attempts = p.opts.MaxProofAttempts
		}
		s.Sessions, s.Attempts = max(s.Sessions, 1), max(s.Attempts, 1)
		if !p.opts.NoPlan {
			// Direct attempts per session before the outline stage; 0 skips
			// the direct attempts (ladder leaves such stages out).
			s.Attempts = max(0, min(s.Attempts, p.opts.PlanAfter))
		}
		if s.Tools && s.MaxToolCalls <= 0 {
			s.MaxToolCalls = 16
		}
		if s.Name == "" {
			s.Name = fmt.Sprintf("stage%d", i+1)
		}
		out[i] = s
	}
	return out
}

// ErrTooManyStatements is returned when the input exceeds MaxStatements.
var ErrTooManyStatements = errors.New("too many statements")

// Pipeline is reusable and safe for concurrent jobs.
type Pipeline struct {
	agent *llm.Agent
	check Checker
	opts  Options
}

// New builds a pipeline.
func New(agent *llm.Agent, check Checker, opts Options) *Pipeline {
	return &Pipeline{agent: agent, check: check, opts: opts.withDefaults()}
}

// Job hooks. Both optional.
type Hooks struct {
	OnEvent func(Event) // called synchronously; keep it fast
	Confirm ConfirmFunc // nil = accept every formalization
}

// job is the state of one Run.
type job struct {
	p     *Pipeline
	hooks Hooks
	mu    sync.Mutex // guards statement results and event emission
	res   *Result
	// failed holds rejected proofs per theorem name (see failedFor);
	// sessions numbers proof sessions per statement. Both guarded by mu.
	failed   map[string]*failedSet
	sessions map[int]int
}

// Run processes the input. It returns a Result even on error (with what
// was done so far); err is set for fatal problems such as an exhausted
// budget, cancellation or a broken Lean worker pool.
func (p *Pipeline) Run(ctx context.Context, input string, hooks Hooks) (*Result, error) {
	start := time.Now()
	usd0, calls0 := p.agent.Spent()
	j := &job{p: p, hooks: hooks, res: &Result{}}
	defer func() {
		usd, calls := p.agent.Spent()
		j.res.CostUSD, j.res.LLMCalls = usd-usd0, calls-calls0
		j.res.Duration = time.Since(start)
	}()

	texts, err := j.split(ctx, input)
	if err != nil {
		j.emit(Event{Type: EvError, Message: err.Error()})
		return j.res, err
	}
	if limit := p.opts.MaxStatements; limit > 0 && len(texts) > limit {
		err := fmt.Errorf("%w: input has %d statements, limit is %d", ErrTooManyStatements, len(texts), limit)
		j.emit(Event{Type: EvError, Message: err.Error()})
		return j.res, err
	}
	for i, t := range texts {
		j.res.Statements = append(j.res.Statements, &StatementResult{
			Index: i + 1, Name: fmt.Sprintf("stmt_%d", i+1), Text: t, Status: StatusPending,
		})
	}
	j.emit(Event{Type: EvSplit, Message: fmt.Sprintf("%d statement(s)", len(texts))})

	var base *lean.Snapshot // environment with every proved statement so far
	var lemmas []llm.Lemma  // earlier statements, for the model's context
	var fatal error
	for _, sr := range j.res.Statements {
		if fatal != nil {
			j.setStatus(sr, StatusCanceled, fatal.Error())
			continue
		}
		snap, err := j.statement(ctx, sr, base, lemmas)
		if err != nil {
			fatal = err
			j.setStatus(sr, StatusCanceled, err.Error())
			j.emit(Event{Type: EvError, Stmt: sr.Index, Message: err.Error()})
			continue
		}
		if snap != nil {
			base = snap
		}
		if sr.Signature != "" {
			lemmas = append(lemmas, llm.Lemma{Name: sr.Name, Signature: sr.Signature, Text: sr.Text, Proved: sr.Status == StatusProved})
		}
	}
	if p.opts.Verifier != nil && fatal == nil {
		if err := j.verify(ctx, base); err != nil {
			fatal = err
		}
	}
	j.res.LeanFile = j.leanFile(base)
	j.emit(Event{Type: EvDone, Message: j.summary()})
	return j.res, fatal
}

func (j *job) split(ctx context.Context, input string) ([]string, error) {
	input = strings.TrimSpace(input)
	if input == "" {
		return nil, errors.New("empty input")
	}
	if j.p.opts.SkipSplit {
		return []string{input}, nil
	}
	texts, err := j.p.agent.SplitStatements(ctx, input)
	if err != nil {
		if fatalErr(ctx, err) {
			return nil, err
		}
		// Splitting is a convenience; fall back to one statement.
		j.emit(Event{Type: EvError, Message: "split failed, treating input as one statement: " + err.Error()})
		return []string{input}, nil
	}
	return texts, nil
}

// statement formalizes and proves one statement. It returns the new base
// snapshot if proved, and an error only for fatal conditions.
func (j *job) statement(ctx context.Context, sr *StatementResult, base *lean.Snapshot, lemmas []llm.Lemma) (*lean.Snapshot, error) {
	j.setStatus(sr, StatusFormalizing, "")
	stmt, ok, err := j.formalize(ctx, sr, base, lemmas)
	if err != nil || !ok {
		return nil, err
	}

	// A counterexample (cheap: Lean only, a few seconds) saves the proof
	// attempts on a statement that is false as formalized.
	if !j.p.opts.NoDisprove {
		if done, err := j.counterexample(ctx, sr, stmt, base); err != nil || done {
			return nil, err
		}
	}

	j.setStatus(sr, StatusProving, "")
	o, claimAt, err := j.prove(ctx, sr, stmt, base, lemmas)
	if err != nil {
		return nil, err
	}
	claimed := claimAt != noClaim
	if o == nil && claimed && !j.p.opts.NoDisprove {
		// A FALSE reply gets ClaimDisproveAttempts at the negation; repeating
		// the claim after proving resumed earns the rest of the
		// DisproveAttempts budget.
		why, tries := "the model says the statement is false", min(j.p.opts.ClaimDisproveAttempts, j.p.opts.DisproveAttempts)
		budget := j.p.opts.DisproveAttempts - tries
		if done, err := j.disprove(ctx, sr, stmt, base, lemmas, why, tries); err != nil || done {
			return nil, err
		}
		// The negation could not be proved, so the claim may be wrong: climb
		// the rest of the ladder after all, from the stage that stopped.
		for claimAt != noClaim {
			stages := j.p.stages()
			j.emit(Event{Type: EvResuming, Stmt: sr.Index, Message: fmt.Sprintf("the negation could not be proved; resuming the proof at stage %d/%d %q",
				claimAt+1, len(stages), stages[claimAt].Name)})
			in := llm.ProveInput{Name: stmt.Name, Signature: stmt.Signature, Context: lemmas,
				Text: sr.Text + " (An earlier claim that this statement is false could not be confirmed: its negation could not be proved yet. Prove the statement, or reply FALSE again only if you are sure.)"}
			o, claimAt, err = j.ladder(ctx, sr, stmt, base, in, claimAt, budget > 0)
			if err != nil {
				return nil, err
			}
			if claimAt == noClaim {
				break
			}
			// FALSE again: the model insists, so give it the rest of the budget.
			tries, budget = budget, 0
			if done, err := j.disprove(ctx, sr, stmt, base, lemmas, "the model insists the statement is false", tries); err != nil || done {
				return nil, err
			}
		}
	}
	// Direct attempts failed: try an outline whose steps are proved one by one.
	if o == nil && !j.p.opts.NoPlan {
		if o, err = j.plan(ctx, sr, stmt, base, lemmas); err != nil {
			return nil, err
		}
	}
	// Failing to prove the statement outright gets the whole disproof budget.
	if o == nil && !claimed && !j.p.opts.NoDisprove {
		if done, err := j.disprove(ctx, sr, stmt, base, lemmas, "no proof found", j.p.opts.DisproveAttempts); err != nil || done {
			return nil, err
		}
	}
	if o == nil {
		msg := fmt.Sprintf("no proof found in %d attempt(s)", proofAttempts(sr))
		if n := planAttempts(sr); n > 0 {
			msg = fmt.Sprintf("no proof found in %d direct attempt(s) and %d outline(s)", proofAttempts(sr), n)
		}
		j.setStatus(sr, StatusFailed, msg)
		j.emit(Event{Type: EvFailed, Stmt: sr.Index, Statement: j.copyOf(sr)})
		return nil, nil
	}

	j.mu.Lock()
	sr.Status = StatusProved
	sr.Proof = o.Attempt.Body
	sr.LeanCode = o.Attempt.Code
	sr.Axioms = o.Verdict.Axioms
	j.mu.Unlock()
	j.emit(Event{Type: EvProved, Stmt: sr.Index, Statement: j.copyOf(sr)})

	if !j.p.opts.NoExplain {
		exp, err := j.p.agent.Explain(ctx, sr.Text, sr.Name, sr.Signature, sr.Proof)
		if err != nil {
			if fatalErr(ctx, err) {
				return o.Snapshot(), err
			}
			j.emit(Event{Type: EvError, Stmt: sr.Index, Message: "explanation failed: " + err.Error()})
		} else {
			j.mu.Lock()
			sr.Explanation = exp
			j.mu.Unlock()
			j.emit(Event{Type: EvExplained, Stmt: sr.Index, Message: exp})
		}
	}
	return o.Snapshot(), nil
}

// fcandidate is a formalization Lean accepted, with its check results.
type fcandidate struct {
	stmt    lean.Statement
	notes   string
	back    string
	backOK  bool
	issues  []string // from the faithfulness check
	checked bool
}

// formalize loops: LLM proposes a signature, Lean checks it, an
// independent call checks that it says what the text says, the user
// optionally confirms or corrects it.
//
// A formalization the faithfulness check objects to is sent back once to
// be fixed. The fix is kept only if the check finds fewer problems with it;
// otherwise (or if Lean rejects the fix) the first one stands, so a wrong
// objection can never make the statement worse.
func (j *job) formalize(ctx context.Context, sr *StatementResult, base *lean.Snapshot, lemmas []llm.Lemma) (lean.Statement, bool, error) {
	var prev *llm.FormalizeRetry
	var first *fcandidate // sent back by the faithfulness check
	leanFails, revisions, faithFixes := 0, 0, 0
	for {
		j.emit(Event{Type: EvFormalizing, Stmt: sr.Index, Message: fmt.Sprintf("attempt %d", leanFails+revisions+faithFixes+1)})
		c, failed, err := j.formalizeOnce(ctx, sr, base, lemmas, prev)
		if err != nil {
			return lean.Statement{}, false, err
		}
		switch {
		case c == nil && first != nil:
			j.emit(Event{Type: EvFaithfulness, Stmt: sr.Index, Message: "the re-formalization failed; keeping the first formalization"})
			c = first
			j.show(sr, c)
		case c == nil:
			leanFails++
			if leanFails >= j.p.opts.MaxFormalizeAttempts {
				msg := failed.Problem
				if failed.Signature != "" {
					msg = "Lean rejected every formalization; last error:\n" + strings.TrimPrefix(msg, "Lean error:\n")
				}
				j.setStatus(sr, StatusUnformal, msg)
				return lean.Statement{}, false, nil
			}
			if failed.Signature != "" {
				prev = failed
			}
			continue
		default:
			j.show(sr, c)
			if c.backOK && !j.p.opts.NoFaithfulnessCheck {
				c.issues, c.checked, err = j.faithfulness(ctx, sr, c.stmt.Signature, c.back, lemmas)
				if err != nil {
					return lean.Statement{}, false, err
				}
			}
			if c.checked && len(c.issues) > 0 && faithFixes < j.p.opts.FaithfulnessFixes {
				if first == nil {
					first = c
				}
				faithFixes++
				prev = &llm.FormalizeRetry{Signature: c.stmt.Signature, Problem: "An independent check found that this formalization may not say exactly what the statement says:\n- " +
					strings.Join(c.issues, "\n- ") +
					"\nFix only real differences in meaning and keep everything else. Do not add or strengthen hypotheses, and do not change the statement to make it true or easier to prove: a false statement must stay false. Ignore any remark that the statement itself is false; if the formalization already says exactly what the text says, return it unchanged."}
				continue
			}
			if first != nil && first != c && len(c.issues) >= len(first.issues) {
				j.emit(Event{Type: EvFaithfulness, Stmt: sr.Index, Message: "the re-formalization was not better; keeping the first formalization"})
				c = first
				j.show(sr, c)
			}
		}
		first = nil

		if j.hooks.Confirm == nil {
			return c.stmt, true, nil
		}
		d, err := j.hooks.Confirm(ctx, Proposal{
			Index: sr.Index, Text: sr.Text, Name: sr.Name, Signature: c.stmt.Signature,
			Notes: c.notes, BackTranslation: c.back, Issues: append([]string(nil), c.issues...),
		})
		if err != nil {
			return lean.Statement{}, false, fmt.Errorf("confirm: %w", err)
		}
		if d.Accept {
			return c.stmt, true, nil
		}
		if strings.TrimSpace(d.Correction) == "" || revisions >= j.p.opts.MaxRevisions {
			j.setStatus(sr, StatusUnformal, "formalization rejected by user")
			return lean.Statement{}, false, nil
		}
		revisions++
		j.emit(Event{Type: EvRevising, Stmt: sr.Index, Message: d.Correction})
		prev = &llm.FormalizeRetry{Signature: c.stmt.Signature, Problem: "The user says this does not match the intended statement:\n" + d.Correction}
	}
}

// formalizeOnce asks for one formalization, has Lean check it and
// back-translates it. On a model or Lean failure c is nil and failed says
// why (failed.Signature is empty when the reply had no usable theorem).
func (j *job) formalizeOnce(ctx context.Context, sr *StatementResult, base *lean.Snapshot, lemmas []llm.Lemma, prev *llm.FormalizeRetry) (c *fcandidate, failed *llm.FormalizeRetry, err error) {
	f, err := j.p.agent.Formalize(ctx, llm.FormalizeInput{Name: sr.Name, Statement: sr.Text, Context: lemmas, Previous: prev})
	if err != nil {
		if fatalErr(ctx, err) {
			return nil, nil, err
		}
		return nil, &llm.FormalizeRetry{Problem: err.Error()}, nil
	}
	stmt := lean.Statement{Name: sr.Name, Signature: f.Signature}
	problem := ""
	if err := stmt.Validate(); err != nil {
		problem = err.Error()
	} else {
		sc, err := j.p.check.CheckStatement(ctx, base, stmt)
		if err != nil {
			return nil, nil, fmt.Errorf("lean: %w", err)
		}
		if !sc.OK {
			problem = renderStatementErrors(sc)
		}
	}
	if problem != "" {
		j.emit(Event{Type: EvStatementError, Stmt: sr.Index, Message: problem})
		return nil, &llm.FormalizeRetry{Signature: f.Signature, Problem: "Lean error:\n" + problem}, nil
	}

	back, err := j.p.agent.BackTranslate(ctx, sr.Name, f.Signature, lemmas)
	backOK := err == nil
	if err != nil {
		if fatalErr(ctx, err) {
			return nil, nil, err
		}
		back = "(back-translation unavailable: " + err.Error() + ")"
	}
	return &fcandidate{stmt: stmt, notes: f.Notes, back: back, backOK: backOK}, nil, nil
}

// show makes c the statement's current formalization.
func (j *job) show(sr *StatementResult, c *fcandidate) {
	j.mu.Lock()
	sr.Signature, sr.FormalizationNotes, sr.BackTranslation = c.stmt.Signature, c.notes, c.back
	sr.FaithfulnessIssues, sr.FaithfulnessChecked = append([]string(nil), c.issues...), c.checked
	j.mu.Unlock()
	j.emit(Event{Type: EvFormalized, Stmt: sr.Index, Statement: j.copyOf(sr)})
}

// faithfulness runs the independent check and records its verdict. checked
// is false if the check could not run (a non-fatal error was reported).
func (j *job) faithfulness(ctx context.Context, sr *StatementResult, sig, back string, lemmas []llm.Lemma) (issues []string, checked bool, err error) {
	fc, err := j.p.agent.CheckFaithfulness(ctx, sr.Text, sr.Name, sig, back, lemmas)
	if err != nil {
		if fatalErr(ctx, err) {
			return nil, false, err
		}
		j.emit(Event{Type: EvError, Stmt: sr.Index, Message: "faithfulness check failed: " + err.Error()})
		return nil, false, nil
	}
	j.mu.Lock()
	sr.FaithfulnessChecked = true
	if !fc.Match {
		sr.FaithfulnessIssues = fc.Issues
	}
	j.mu.Unlock()
	msg := "formalization matches the statement"
	if !fc.Match {
		msg = "formalization may differ from the statement: " + strings.Join(fc.Issues, "; ")
		issues = fc.Issues
	}
	j.emit(Event{Type: EvFaithfulness, Stmt: sr.Index, Message: msg})
	return issues, true, nil
}

// counterexample tests the statement before any proof attempt. done is true
// if the statement was disproved.
func (j *job) counterexample(ctx context.Context, sr *StatementResult, stmt lean.Statement, base *lean.Snapshot) (done bool, err error) {
	cf, ok := j.p.check.(CounterexampleFinder)
	if !ok {
		return false, nil
	}
	ce, err := cf.FindCounterexample(ctx, base, stmt)
	if err != nil {
		if ctx.Err() != nil {
			return false, ctx.Err()
		}
		return false, fmt.Errorf("lean: %w", err)
	}
	if ce == "" {
		return false, nil
	}
	j.mu.Lock()
	sr.Status = StatusDisproved
	sr.Counterexample = ce
	sr.Error = "the statement is false as formalized: Lean found a counterexample by testing"
	j.mu.Unlock()
	j.emit(Event{Type: EvDisproved, Stmt: sr.Index, Message: "counterexample: " + oneLine(ce), Statement: j.copyOf(sr)})
	return true, nil
}

// disprove tries to prove the negation after the proof attempts failed.
// done is true if Lean verified a proof of the negation.
func (j *job) disprove(ctx context.Context, sr *StatementResult, stmt lean.Statement, base *lean.Snapshot, lemmas []llm.Lemma, why string, tries int) (done bool, err error) {
	negSig, ok := lean.NegatedSignature(stmt.Signature)
	if !ok {
		return false, nil
	}
	neg := lean.Statement{Name: stmt.Name + "_false", Signature: negSig}
	if neg.Validate() != nil {
		return false, nil
	}
	if tries <= 0 {
		return false, nil
	}
	j.emit(Event{Type: EvDisproving, Stmt: sr.Index, Message: fmt.Sprintf("%s; trying to prove the negation (%d attempt(s))", why, tries)})
	in := llm.ProveInput{
		Name: neg.Name, Signature: neg.Signature, Context: lemmas,
		Text: "This is the NEGATION of: " + sr.Text + " — prove that the statement is false (for example by exhibiting a counterexample).",
	}
	st := j.p.lastStage()
	o, err := j.session(ctx, j.nextSession(sr), st, sr, neg, base, in, j.failedFor(neg.Name), sessionOpts{max: tries, disproof: true})
	if err != nil || o == nil {
		return false, err
	}
	j.mu.Lock()
	sr.Status = StatusDisproved
	sr.Proof = o.Attempt.Body
	sr.LeanCode = o.Attempt.Code
	sr.Axioms = o.Verdict.Axioms
	sr.Error = "the statement is false as formalized: Lean verified a proof of its negation"
	j.mu.Unlock()
	j.emit(Event{Type: EvDisproved, Stmt: sr.Index, Message: "Lean verified a proof of the negation", Statement: j.copyOf(sr)})
	return true, nil
}

// proofAttempts counts the charged attempts at the statement itself (not
// disproofs, not free repeats).
func proofAttempts(sr *StatementResult) int {
	n := 0
	for _, a := range sr.Attempts {
		if !a.Disproof && !a.Free && !a.Plan && a.Step == "" {
			n++
		}
	}
	return n
}

func oneLine(s string) string { return strings.Join(strings.Fields(s), " ") }

func renderStatementErrors(sc *lean.StatementCheck) string {
	var b strings.Builder
	for _, d := range sc.Errors {
		fmt.Fprintf(&b, "line %d (%s): %s\n", d.Pos.Line, d.Kind, d.Data)
	}
	return strings.TrimSpace(b.String())
}

// errClaimsFalse ends a proof session whose model replied FALSE.
var errClaimsFalse = errors.New("the model says the statement is false")

// noClaim is ladder's claimedAt when no session replied FALSE.
const noClaim = -1

// prove first tries automation tactics directly in Lean, then climbs the
// stage ladder (see ladder). Returns a nil outcome if all failed;
// claimedAt is the stage whose sessions stopped because the model said
// FALSE, or noClaim.
func (j *job) prove(ctx context.Context, sr *StatementResult, stmt lean.Statement, base *lean.Snapshot, lemmas []llm.Lemma) (win *lean.Outcome, claimedAt int, err error) {
	if !j.p.opts.NoAutomation {
		o, err := j.automate(ctx, sr, stmt, base)
		if err != nil || o != nil {
			return o, noClaim, err
		}
	}
	in := llm.ProveInput{Name: stmt.Name, Signature: stmt.Signature, Text: sr.Text, Context: lemmas}
	return j.ladder(ctx, sr, stmt, base, in, 0, !j.p.opts.NoDisprove)
}

// ladder climbs the stages from stage `from` on: each stage races its
// sessions, the first verified outcome wins and cancels the rest, and the
// next (more expensive) stage only runs if the current one found nothing.
// With allowFalse, a stage in which a session replied FALSE (and none
// found a proof) ends the climb with claimedAt set to that stage, so the
// caller can try the negation first and resume there.
func (j *job) ladder(ctx context.Context, sr *StatementResult, stmt lean.Statement, base *lean.Snapshot,
	in llm.ProveInput, from int, allowFalse bool) (*lean.Outcome, int, error) {
	failed := j.failedFor(stmt.Name)
	stages := j.p.stages()
	for i := from; i < len(stages); i++ {
		st := stages[i]
		if st.Attempts <= 0 {
			continue // -plan-after 0: straight to the outline
		}
		j.emit(Event{Type: EvStage, Stmt: sr.Index, Message: fmt.Sprintf("stage %d/%d %q: %s effort %s, %d session(s) × %d attempt(s)",
			i+1, len(stages), st.Name, st.Spec.Model, effortName(st.Spec.Effort), st.Sessions, st.Attempts)})
		o, claimed, err := j.runStage(ctx, sr, stmt, base, in, st, failed, sessionOpts{max: st.Attempts, allowFalse: allowFalse})
		if err != nil || o != nil {
			return o, noClaim, err
		}
		if claimed {
			return nil, i, nil
		}
	}
	return nil, noClaim, nil
}

// lastStage is the most capable stage of the ladder. Proofs of a negation
// and of outline steps run on it.
func (p *Pipeline) lastStage() Stage {
	st := p.stages()
	return st[len(st)-1]
}

// DefaultAutomation is tried, in order, before any LLM call. Each runs as
// its own check, so one tactic's failure (or timeout) never hides another.
var DefaultAutomation = []string{
	"omega", "decide", "norm_num", "simp", "positivity",
	"linarith", "nlinarith", "aesop", "exact?",
}

var reTryThis = regexp.MustCompile(`(?s)^Try this:\s*(?:\[apply\]\s*)?(.+)$`)

// automate tries each automation tactic as a complete proof.
func (j *job) automate(ctx context.Context, sr *StatementResult, stmt lean.Statement, base *lean.Snapshot) (*lean.Outcome, error) {
	tactics := j.p.opts.Automation
	if tactics == nil {
		tactics = DefaultAutomation
	}
	t0 := time.Now()
	for i, tac := range tactics {
		t1 := time.Now()
		o, err := j.p.check.CheckProof(ctx, base, stmt, tac)
		if err != nil {
			if ctx.Err() != nil {
				return nil, ctx.Err()
			}
			return nil, fmt.Errorf("lean: %w", err)
		}
		if !o.Verdict.Verified {
			continue
		}
		// `exact?` closes the goal by search; keep the term it found instead,
		// so the final file is fast to re-check and readable.
		if o.Result != nil {
			for _, m := range o.Result.Messages {
				if mm := reTryThis.FindStringSubmatch(strings.TrimSpace(m.Data)); mm != nil && m.Severity == "info" {
					if o2, err := j.p.check.CheckProof(ctx, base, stmt, mm[1]); err == nil && o2.Verdict.Verified {
						o, tac = o2, mm[1]
					}
					break
				}
			}
		}
		j.record(sr, AttemptRecord{Stage: "auto", N: i + 1, Body: tac, Verified: true, LeanTime: time.Since(t1)})
		j.emit(Event{Type: EvAutomation, Stmt: sr.Index, Message: fmt.Sprintf("closed by automation: %s", tac)})
		return o, nil
	}
	j.emit(Event{Type: EvAutomation, Stmt: sr.Index, Message: fmt.Sprintf("automation: none of %d tactics closed the goal (%s)",
		len(tactics), time.Since(t0).Round(10*time.Millisecond))})
	return nil, nil
}

// failedSet holds proofs already rejected for one goal, shared by all
// sessions and stages, so repeats are not re-checked.
type failedSet struct {
	mu sync.Mutex
	m  map[string]string // normalized body -> feedback given
}

func newFailedSet() *failedSet { return &failedSet{m: map[string]string{}} }

// failedFor is the job's failedSet for the theorem name: every session,
// stage and resumed proof of one statement (or of its negation) shares it.
func (j *job) failedFor(name string) *failedSet {
	j.mu.Lock()
	defer j.mu.Unlock()
	if j.failed == nil {
		j.failed = map[string]*failedSet{}
	}
	f := j.failed[name]
	if f == nil {
		f = newFailedSet()
		j.failed[name] = f
	}
	return f
}

func (f *failedSet) get(body string) (string, bool) {
	f.mu.Lock()
	defer f.mu.Unlock()
	fb, ok := f.m[body]
	return fb, ok
}

func (f *failedSet) add(body, feedback string) {
	f.mu.Lock()
	f.m[body] = feedback
	f.mu.Unlock()
}

// runStage races st.Sessions sessions; the first verified outcome wins.
// claimed reports that a session stopped because the model said FALSE.
func (j *job) runStage(ctx context.Context, sr *StatementResult, stmt lean.Statement, base *lean.Snapshot,
	in llm.ProveInput, st Stage, failed *failedSet, so sessionOpts) (win *lean.Outcome, claimed bool, err error) {
	ctx, cancel := context.WithCancel(ctx)
	defer cancel()
	type res struct {
		o   *lean.Outcome
		err error
	}
	ch := make(chan res, st.Sessions)
	for range st.Sessions {
		sn := j.nextSession(sr)
		go func() {
			o, err := j.session(ctx, sn, st, sr, stmt, base, in, failed, so)
			ch <- res{o, err}
		}()
	}
	var firstErr error
	for range st.Sessions {
		r := <-ch
		switch {
		case r.o != nil && win == nil:
			win = r.o
			cancel()
		case errors.Is(r.err, errClaimsFalse):
			claimed = true
		case r.err != nil && firstErr == nil && !errors.Is(r.err, context.Canceled):
			firstErr = r.err
		}
	}
	if win != nil {
		return win, false, nil
	}
	if err := ctx.Err(); err != nil && firstErr == nil {
		// parent canceled (our own cancel only fires after a win)
		return nil, false, err
	}
	return nil, claimed, firstErr
}

// nextSession numbers proof sessions per statement, across stages,
// resumed proofs, disproofs and outline steps.
func (j *job) nextSession(sr *StatementResult) int {
	j.mu.Lock()
	defer j.mu.Unlock()
	if j.sessions == nil {
		j.sessions = map[int]int{}
	}
	j.sessions[sr.Index]++
	return j.sessions[sr.Index]
}

// sessionOpts tunes one proof session.
type sessionOpts struct {
	max        int    // attempts
	disproof   bool   // proving the statement's negation
	allowFalse bool   // a FALSE reply ends the session with errClaimsFalse
	step       string // proving this outline step (recorded in AttemptRecord.Step)
}

// thinkingEvery throttles "thinking…" progress events per attempt.
const thinkingEvery = 10 * time.Second

// session runs one propose → check → feedback loop of so.max attempts on
// st's model. In tool stages the model may also look things up and test
// proofs (check_proof) inside an attempt; every check_proof is recorded as
// an attempt of its own. failed is shared with the other sessions on the
// same goal. A session stuck on one approach is restarted with a summary
// (see stuck.go).
func (j *job) session(ctx context.Context, sn int, st Stage, sr *StatementResult, stmt lean.Statement,
	base *lean.Snapshot, in llm.ProveInput, failed *failedSet, so sessionOpts) (*lean.Outcome, error) {
	sess := j.p.agent.NewProofSessionWith(in, st.Spec)
	n := 0 // attempt records so far
	// acc collects LLM usage until the next record.
	var acc AttemptRecord
	newRec := func(body string) AttemptRecord {
		n++
		r := acc
		acc = AttemptRecord{}
		r.Stage, r.Session, r.N, r.Model, r.Effort, r.Body = st.Name, sn, n, st.Spec.Model, effortName(st.Spec.Effort), body
		r.Disproof, r.Step = so.disproof, so.step
		return r
	}
	addUsage := func(resp *llm.Response) {
		acc.CostUSD += resp.CostUSD
		acc.LLMTime += resp.Latency
		acc.CompletionTokens += resp.Usage.CompletionTokens
		acc.ReasoningTokens += resp.Usage.ReasoningTokens()
	}

	var tried []AttemptRecord // Lean-rejected attempts since the last restart
	var last *AttemptRecord   // the previous Lean-rejected attempt
	free, stuck, restarts := 0, 0, 0
	// next gives the model its feedback, or restarts the conversation once
	// it has been stuck on one approach stuckLimit times.
	next := func(rec AttemptRecord, round int) {
		// (No restart after the last attempt: nothing would use it.)
		if stuck >= stuckLimit && restarts < maxRestarts && len(tried) > 0 && round < so.max {
			restarts++
			stuck, last = 0, nil
			j.mu.Lock()
			sr.Restarts++
			j.mu.Unlock()
			sess.Restart(restartSummary(tried))
			tried = nil
			j.emit(Event{Type: EvRestarted, Stmt: sr.Index, Message: fmt.Sprintf("stuck on one approach; restarted the conversation with a summary (%d of %d)", restarts, maxRestarts)})
			return
		}
		sess.Feedback(rec.Feedback)
	}

	for round := 1; round <= so.max; round++ {
		if err := ctx.Err(); err != nil {
			return nil, err
		}
		t0 := time.Now()
		lastEmit := t0
		var progMu sync.Mutex
		progress := func(p llm.Progress) {
			progMu.Lock()
			defer progMu.Unlock()
			if time.Since(lastEmit) < thinkingEvery {
				return
			}
			lastEmit = time.Now()
			j.emit(Event{Type: EvThinking, Stmt: sr.Index, Message: fmt.Sprintf("session %d attempt %d (%s): thinking… %d tokens after %s",
				sn, round, st.Name, p.ReasoningChunks+p.ContentChunks, time.Since(t0).Round(time.Second))})
		}

		var body string
		var err error
		if st.Tools {
			tools := &leanTools{j: j, sr: sr, stmt: stmt, base: base, failed: failed}
			lastCalls := 0
			tools.rec = func(b string, o *lean.Outcome, leanTime time.Duration, repeated, feedback string) {
				r := newRec(b)
				r.ToolCalls, lastCalls = tools.calls-lastCalls, tools.calls
				r.LeanTime = leanTime
				switch {
				case repeated != "":
					r.ErrorKinds, r.Feedback = []string{"repeated"}, repeated
				case o != nil:
					r.Verified = o.Verdict.Verified
					for _, d := range o.Verdict.Errors {
						r.ErrorKinds = append(r.ErrorKinds, string(d.Kind))
					}
					r.Feedback = feedback
				}
				j.record(sr, r)
			}
			var stopped bool
			body, stopped, err = sess.NextTools(ctx, tools, st.MaxToolCalls, progress, addUsage)
			if stopped && tools.win != nil {
				return j.resolveSearch(ctx, sr, stmt, base, tools.win), nil
			}
			if err != nil && !fatalErr(ctx, err) && (errors.Is(err, llm.ErrNoAnswer) || errors.Is(err, llm.ErrTruncated)) {
				r := newRec("")
				r.ToolCalls = tools.calls - lastCalls
				r.ErrorKinds = []string{map[bool]string{true: "no_answer", false: "truncated"}[errors.Is(err, llm.ErrNoAnswer)]}
				j.record(sr, r)
				continue // no pending reply; start the next round fresh
			}
		} else {
			var resp *llm.Response
			body, resp, err = sess.NextProgress(ctx, progress)
			if resp != nil {
				addUsage(resp)
			}
			if err != nil && !fatalErr(ctx, err) && errors.Is(err, llm.ErrTruncated) {
				r := newRec("")
				r.ErrorKinds = []string{"truncated"}
				j.record(sr, r)
				continue // the session has no pending reply; just ask again
			}
		}
		if err != nil {
			return nil, err // fatal, or non-transient API error after client retries
		}

		rec := newRec(body)
		if llm.ClaimsFalse(body) {
			rec.ErrorKinds = []string{"claims_false"}
			if so.allowFalse {
				j.record(sr, rec)
				return nil, errClaimsFalse
			}
			rec.Feedback = "FALSE is not accepted here: reply with a tactic proof."
			if so.disproof {
				rec.Feedback = "You are proving the NEGATION of the original statement, so FALSE is not an answer here: reply with a tactic proof of the negation."
			}
			j.record(sr, rec)
			sess.Feedback(rec.Feedback)
			continue
		}

		norm := lean.NormalizeBody(body)
		if fb, seen := failed.get(norm); seen {
			rec.ErrorKinds = []string{"repeated"}
			rec.Feedback = "This proof is identical to an earlier attempt that already failed with:\n\n" + fb +
				"\n\nUse a different approach."
			if free < freeRepeats { // not checked by Lean, so not charged as an attempt
				free++
				rec.Free = true
				round--
			}
			stuck++
			j.record(sr, rec)
			next(rec, round)
			continue
		}
		t1 := time.Now()
		o, err := j.p.check.CheckProof(ctx, base, stmt, body)
		rec.LeanTime = time.Since(t1)
		if err != nil {
			if ctx.Err() != nil {
				return nil, ctx.Err()
			}
			return nil, fmt.Errorf("lean: %w", err)
		}
		rec.Verified = o.Verdict.Verified
		for _, d := range o.Verdict.Errors {
			rec.ErrorKinds = append(rec.ErrorKinds, string(d.Kind))
		}
		if !rec.Verified {
			rec.Feedback = j.feedback(ctx, o)
		}
		j.record(sr, rec)
		if rec.Verified {
			return j.resolveSearch(ctx, sr, stmt, base, o), nil
		}
		failed.add(norm, rec.Feedback)
		// Nearly the same proof failing the same way = stuck. A small edit
		// that changes the errors is progress and does not count.
		if last != nil && similarity(last.Body, body) >= nearDuplicate && sameKinds(last.ErrorKinds, rec.ErrorKinds) {
			stuck++
		}
		tried = append(tried, rec)
		last = &tried[len(tried)-1]
		next(rec, round)
	}
	return nil, nil
}

func effortName(e llm.Effort) string {
	if e == llm.EffortDefault {
		return "default"
	}
	return string(e)
}

// feedback renders Lean's verdict on a failed proof for the model, with
// name suggestions for unknown identifiers.
func (j *job) feedback(ctx context.Context, o *lean.Outcome) string {
	fb := lean.RenderFeedback(o, j.p.opts.Feedback)
	if hint := j.suggest(ctx, o); hint != "" {
		fb += "\n" + hint
	}
	return fb
}

// suggest asks the Suggester about the attempt's unknown identifiers.
func (j *job) suggest(ctx context.Context, o *lean.Outcome) string {
	if j.p.opts.Suggester == nil {
		return ""
	}
	ids := lean.UnknownIdents(o.Verdict.Errors)
	if len(ids) == 0 {
		return ""
	}
	return j.p.opts.Suggester.Suggest(ctx, j.p.check, ids)
}

// resolveSearch replaces search tactics (exact? ...) in a verified proof
// with the tactics Lean found, if the rewritten proof also verifies;
// otherwise the original outcome is kept.
func (j *job) resolveSearch(ctx context.Context, sr *StatementResult, stmt lean.Statement, base *lean.Snapshot, o *lean.Outcome) *lean.Outcome {
	if j.p.opts.KeepSearchTactics || !lean.HasSearchTactic(o.Attempt.Body) {
		return o
	}
	body, n := lean.ApplyTryThis(o)
	if n == 0 {
		j.emit(Event{Type: EvSimplified, Stmt: sr.Index, Message: "kept search tactic(s): Lean gave no single suggestion"})
		return o
	}
	o2, err := j.p.check.CheckProof(ctx, base, stmt, body)
	if err != nil || !o2.Verdict.Verified {
		j.emit(Event{Type: EvSimplified, Stmt: sr.Index, Message: fmt.Sprintf("kept search tactic(s): the %d suggestion(s) did not re-check", n)})
		return o
	}
	j.emit(Event{Type: EvSimplified, Stmt: sr.Index, Message: fmt.Sprintf("replaced %d search tactic(s) with the lemmas Lean found", n)})
	return o2
}

// fatalErr reports errors that should stop the whole job.
func fatalErr(ctx context.Context, err error) bool {
	if ctx.Err() != nil || errors.Is(err, llm.ErrBudget) {
		return true
	}
	var ae *llm.APIError
	// 401 bad key, 402 no balance: nothing will work until fixed.
	return errors.As(err, &ae) && (ae.Status == 401 || ae.Status == 402)
}

func (j *job) record(sr *StatementResult, rec AttemptRecord) {
	j.mu.Lock()
	sr.Attempts = append(sr.Attempts, rec)
	j.mu.Unlock()
	r := rec
	j.emit(Event{Type: EvAttempt, Stmt: sr.Index, Attempt: &r})
}

func (j *job) setStatus(sr *StatementResult, s Status, msg string) {
	j.mu.Lock()
	sr.Status = s
	if msg != "" {
		sr.Error = msg
	}
	j.mu.Unlock()
}

func (j *job) copyOf(sr *StatementResult) *StatementResult {
	j.mu.Lock()
	defer j.mu.Unlock()
	c := *sr
	c.Attempts = append([]AttemptRecord(nil), sr.Attempts...)
	return &c
}

func (j *job) emit(e Event) {
	if j.hooks.OnEvent == nil {
		return
	}
	if e.Time.IsZero() {
		e.Time = time.Now()
	}
	j.mu.Lock()
	defer j.mu.Unlock()
	j.hooks.OnEvent(e)
}

// verify re-checks all proved statements, and the Lean-proved negations of
// disproved ones (theorem <name>_false), in fresh processes. Statements it
// rejects become failed; if it cannot run, proved ones become unverified
// (a disproof keeps its status, with the error noted). Only cancellation
// is returned as an error.
func (j *job) verify(ctx context.Context, base *lean.Snapshot) error {
	var checked []*StatementResult
	var items []lean.VerifyItem
	for _, sr := range j.res.Statements {
		switch {
		case sr.Status == StatusProved:
			checked = append(checked, sr)
			items = append(items, lean.VerifyItem{Name: sr.Name, Signature: sr.Signature})
		case sr.Status == StatusDisproved && sr.LeanCode != "":
			if neg, ok := lean.NegatedSignature(sr.Signature); ok {
				checked = append(checked, sr)
				items = append(items, lean.VerifyItem{Name: sr.Name + "_false", Signature: neg})
			}
		}
	}
	if len(items) == 0 {
		return nil
	}
	j.emit(Event{Type: EvVerifying, Message: fmt.Sprintf("independently re-checking %d proof(s)", len(items))})
	// The final file: every proof in base plus the proofs of negations.
	rep, err := j.p.opts.Verifier.Verify(ctx, j.leanFile(base), items)
	if err != nil {
		if ctx.Err() != nil {
			return ctx.Err()
		}
		for _, sr := range checked {
			if sr.Status == StatusProved {
				j.setStatus(sr, StatusUnverified, "independent verification could not run: "+err.Error())
			} else {
				j.setStatus(sr, sr.Status, sr.Error+" (independent verification could not run: "+err.Error()+")")
			}
		}
		j.emit(Event{Type: EvError, Message: "independent verification could not run: " + err.Error()})
		return nil
	}
	j.mu.Lock()
	j.res.Verification = rep
	rejected := 0
	for i, sr := range checked {
		name := items[i].Name
		it, ok := rep.Item(name)
		if !ok {
			it = lean.VerifiedItem{Name: name, Error: "missing from verification report"}
		}
		sr.Verification = &it
		if !it.OK {
			rejected++
			what := "proof"
			if sr.Status == StatusDisproved {
				what = "proof of the negation"
				sr.Proof, sr.LeanCode, sr.Axioms = "", "", ""
			}
			sr.Status = StatusFailed
			sr.Error = "independent verification rejected the " + what + ": " + it.Error
			if rep.Log != "" {
				sr.Error += "\n" + rep.Log
			}
		}
	}
	j.mu.Unlock()
	msg := fmt.Sprintf("%d/%d proof(s) confirmed by kernel re-check and axiom audit (%s)",
		len(checked)-rejected, len(checked), rep.Duration.Round(100*time.Millisecond))
	j.emit(Event{Type: EvVerified, Message: msg})
	return nil
}

func (j *job) leanFile(base *lean.Snapshot) string {
	var b strings.Builder
	b.WriteString(j.p.opts.LeanHeader + "\n\n")
	if code := base.Code(); code != "" {
		b.WriteString(code + "\n")
	}
	for _, sr := range j.res.Statements {
		switch {
		case sr.Status == StatusProved || sr.Signature == "":
		case sr.Status == StatusDisproved && sr.LeanCode != "":
			fmt.Fprintf(&b, "\n/- %s is FALSE as formalized:\ntheorem %s %s\n   Lean-checked proof of its negation: -/\n%s", sr.Name, sr.Name, sr.Signature, sr.LeanCode)
		case sr.Status == StatusDisproved:
			fmt.Fprintf(&b, "\n/- %s is FALSE as formalized (counterexample found by `plausible`):\ntheorem %s %s\n%s\n-/\n", sr.Name, sr.Name, sr.Signature, sr.Counterexample)
		default:
			fmt.Fprintf(&b, "\n/- Not proved (%s):\ntheorem %s %s := by\n  sorry\n-/\n", sr.Status, sr.Name, sr.Signature)
		}
	}
	return b.String()
}

func (j *job) summary() string {
	counts := map[Status]int{}
	for _, sr := range j.res.Statements {
		counts[sr.Status]++
	}
	s := fmt.Sprintf("%d/%d proved", counts[StatusProved], len(j.res.Statements))
	if n := counts[StatusDisproved]; n > 0 {
		s += fmt.Sprintf(", %d disproved", n)
	}
	return s
}

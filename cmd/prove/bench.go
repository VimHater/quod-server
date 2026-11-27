package main

import (
	"bufio"
	"context"
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
	"sort"
	"strings"
	"time"

	"mathprover/internal/daemon"
	"mathprover/internal/pipeline"
)

// benchProblem is one line of a bench file:
//
//	true  | number | For every prime p > 3, p^2 - 1 is divisible by 24.
//	false | number | For every natural number n, n^2 >= 2n.
type benchProblem struct {
	ID         int    `json:"id"` // 1-based, in file order
	ExpectTrue bool   `json:"expect_true"`
	Category   string `json:"category"`
	Text       string `json:"text"`
}

// Outcomes of one bench job.
const (
	outCorrect    = "correct"     // true → proved, false → disproved
	outMiss       = "miss"        // neither proved nor disproved
	outFalseAlarm = "false_alarm" // true statement reported false
	outUnsound    = "unsound"     // false statement "proved": the formalization changed its meaning
	outError      = "error"       // the job did not finish
)

type benchRecord struct {
	Model          string          `json:"model"`
	Run            int             `json:"run"`
	Problem        int             `json:"problem"`
	Category       string          `json:"category"`
	ExpectTrue     bool            `json:"expect_true"`
	Outcome        string          `json:"outcome"`
	Status         pipeline.Status `json:"status,omitempty"`
	FirstTry       bool            `json:"first_try"` // correct with no failed attempt
	Seconds        float64         `json:"seconds"`
	LLMCalls       int             `json:"llm_calls"`
	Attempts       int             `json:"attempts"`
	Restarts       int             `json:"restarts,omitempty"`     // stuck → conversation restarted (A4)
	FreeRepeats    int             `json:"free_repeats,omitempty"` // exact repeats not charged (A4)
	ErrorKinds     map[string]int  `json:"error_kinds,omitempty"`
	FaithWarning   bool            `json:"faith_warning,omitempty"`
	Signature      string          `json:"signature,omitempty"`
	Proof          string          `json:"proof,omitempty"`
	Counterexample string          `json:"counterexample,omitempty"`
	Error          string          `json:"error,omitempty"`
	// Per-attempt timings, and the rest of the job's time (formalization,
	// back-translation, faithfulness check, counterexample search, ...).
	AttemptTimes []benchAttempt `json:"attempt_times,omitempty"`
	OtherSeconds float64        `json:"other_seconds"`
}

type benchAttempt struct {
	Stage       string   `json:"stage,omitempty"` // ladder stage, "auto" or "outline"
	Session     int      `json:"session"`
	N           int      `json:"n"`
	Disproof    bool     `json:"disproof,omitempty"`
	Free        bool     `json:"free,omitempty"`
	Plan        bool     `json:"plan,omitempty"`
	Step        string   `json:"step,omitempty"`
	Verified    bool     `json:"verified,omitempty"`
	Kinds       []string `json:"kinds,omitempty"`
	LLMSeconds  float64  `json:"llm_seconds"`
	LeanSeconds float64  `json:"lean_seconds"`
}

func loadBench(path string) ([]benchProblem, error) {
	f, err := os.Open(path)
	if err != nil {
		return nil, err
	}
	defer f.Close()
	var ps []benchProblem
	sc := bufio.NewScanner(f)
	for n := 1; sc.Scan(); n++ {
		line := strings.TrimSpace(sc.Text())
		if line == "" || strings.HasPrefix(line, "#") {
			continue
		}
		parts := strings.SplitN(line, "|", 3)
		if len(parts) != 3 {
			return nil, fmt.Errorf("%s:%d: want `true|false | category | statement`", path, n)
		}
		var expect bool
		switch strings.ToLower(strings.TrimSpace(parts[0])) {
		case "true", "t", "yes":
			expect = true
		case "false", "f", "no":
		default:
			return nil, fmt.Errorf("%s:%d: expected answer must be true or false, got %q", path, n, parts[0])
		}
		text := strings.TrimSpace(parts[2])
		if text == "" {
			return nil, fmt.Errorf("%s:%d: empty statement", path, n)
		}
		ps = append(ps, benchProblem{ID: len(ps) + 1, ExpectTrue: expect, Category: strings.TrimSpace(parts[1]), Text: text})
	}
	if err := sc.Err(); err != nil {
		return nil, err
	}
	if len(ps) == 0 {
		return nil, fmt.Errorf("%s: no problems", path)
	}
	return ps, nil
}

// runBench proves every problem with every model, runs times each, then
// prints a report and saves it (report.md, results.json) under outDir.
func runBench(ctx context.Context, run runner, base daemon.Job, problems []benchProblem, models []modelRef, runs int, outDir string) error {
	started := time.Now()
	total := len(models) * runs * len(problems)
	var recs []benchRecord
	k := 0
loop:
	for _, m := range models {
		for r := 1; r <= runs; r++ {
			for _, p := range problems {
				if ctx.Err() != nil {
					break loop
				}
				k++
				job := base
				job.Input, job.NoSplit, job.NoExplain = p.Text, true, true
				job.Model, job.AuxModel = m.Model, m.Model
				job.BaseURL, job.APIKey = m.URL, m.Key
				t0 := time.Now()
				res, err := run(ctx, job)
				rec := classify(m.String(), r, p, res, err, time.Since(t0))
				recs = append(recs, rec)
				mark := map[string]string{outCorrect: "✓", outMiss: "✗", outFalseAlarm: "✗✗", outUnsound: "✗✗", outError: "!"}[rec.Outcome]
				progress("[%d/%d] %s run %d · #%d %s (expect %v): %s %s %s, %.1fs, %d LLM calls",
					k, total, m, r, p.ID, p.Category, p.ExpectTrue, orDash(string(rec.Status)), mark, rec.Outcome, rec.Seconds, rec.LLMCalls)
			}
		}
	}

	report := benchReport(problems, models, runs, recs, time.Since(started), ctx.Err() != nil)
	fmt.Print("\n" + report)

	dir := filepath.Join(outDir, started.Format("20060102-150405"))
	if err := os.MkdirAll(dir, 0o755); err != nil {
		return err
	}
	if err := os.WriteFile(filepath.Join(dir, "report.md"), []byte(report), 0o644); err != nil {
		return err
	}
	raw, _ := json.MarshalIndent(map[string]any{
		"started": started, "runs": runs, "models": modelNames(models),
		"problems": problems, "records": recs,
	}, "", "  ")
	if err := os.WriteFile(filepath.Join(dir, "results.json"), raw, 0o644); err != nil {
		return err
	}
	progress("bench report saved in %s", dir)
	return ctx.Err()
}

func classify(model string, run int, p benchProblem, res *pipeline.Result, err error, wall time.Duration) benchRecord {
	rec := benchRecord{Model: model, Run: run, Problem: p.ID, Category: p.Category, ExpectTrue: p.ExpectTrue, Seconds: wall.Seconds()}
	if res != nil {
		rec.LLMCalls = res.LLMCalls
		if res.Duration > 0 {
			rec.Seconds = res.Duration.Seconds()
		}
	}
	if res == nil || len(res.Statements) == 0 {
		rec.Outcome = outError
		if err != nil {
			rec.Error = err.Error()
		}
		return rec
	}
	s := res.Statements[0]
	rec.Status, rec.Signature, rec.Proof, rec.Counterexample = s.Status, s.Signature, s.Proof, s.Counterexample
	rec.FaithWarning = len(s.FaithfulnessIssues) > 0
	rec.Restarts = s.Restarts
	if err != nil {
		rec.Error = err.Error()
	} else if s.Status != pipeline.StatusProved && s.Status != pipeline.StatusDisproved {
		rec.Error = s.Error
	}
	failed := 0
	spent := 0.0
	for _, a := range s.Attempts {
		rec.Attempts++
		if a.Free {
			rec.FreeRepeats++
		}
		at := benchAttempt{Stage: a.Stage, Session: a.Session, N: a.N, Disproof: a.Disproof, Free: a.Free, Plan: a.Plan, Step: a.Step, Verified: a.Verified,
			Kinds: a.ErrorKinds, LLMSeconds: a.LLMTime.Seconds(), LeanSeconds: a.LeanTime.Seconds()}
		rec.AttemptTimes = append(rec.AttemptTimes, at)
		spent += at.LLMSeconds + at.LeanSeconds
		for _, k := range a.ErrorKinds {
			if rec.ErrorKinds == nil {
				rec.ErrorKinds = map[string]int{}
			}
			rec.ErrorKinds[k]++
		}
		if !a.Verified && !(len(a.ErrorKinds) == 1 && a.ErrorKinds[0] == "claims_false") {
			failed++
		}
	}
	rec.OtherSeconds = max(rec.Seconds-spent, 0)
	switch {
	case s.Status == pipeline.StatusCanceled:
		rec.Outcome = outError
	case p.ExpectTrue && s.Status == pipeline.StatusProved, !p.ExpectTrue && s.Status == pipeline.StatusDisproved:
		rec.Outcome = outCorrect
		rec.FirstTry = failed == 0
	case p.ExpectTrue && s.Status == pipeline.StatusDisproved:
		rec.Outcome = outFalseAlarm
	case !p.ExpectTrue && s.Status == pipeline.StatusProved:
		rec.Outcome = outUnsound
	default:
		rec.Outcome = outMiss
	}
	return rec
}

func benchReport(problems []benchProblem, models []modelRef, runs int, recs []benchRecord, took time.Duration, partial bool) string {
	var b strings.Builder
	fmt.Fprintf(&b, "# Bench report\n\n%d problem(s) × %d model(s) × %d run(s), %s", len(problems), len(models), runs, took.Round(time.Second))
	if partial {
		b.WriteString(" — INTERRUPTED, partial results")
	}
	b.WriteString("\n\n")

	byModel := map[string][]benchRecord{}
	for _, r := range recs {
		byModel[r.Model] = append(byModel[r.Model], r)
	}

	b.WriteString("## Summary\n\n")
	b.WriteString("| model | correct | first try | miss | false alarm | unsound | error | ⚠ faith | avg time | avg LLM calls | restarts / free repeats |\n")
	b.WriteString("|---|---|---|---|---|---|---|---|---|---|---|\n")
	for _, m := range models {
		rs := byModel[m.String()]
		if len(rs) == 0 {
			continue
		}
		c := map[string]int{}
		var secs float64
		var calls, first, faith, restarts, free int
		for _, r := range rs {
			c[r.Outcome]++
			secs += r.Seconds
			calls += r.LLMCalls
			restarts += r.Restarts
			free += r.FreeRepeats
			if r.FirstTry {
				first++
			}
			if r.FaithWarning {
				faith++
			}
		}
		n := len(rs)
		fmt.Fprintf(&b, "| %s | %d/%d (%.0f%%) | %d/%d | %d | %d | %d | %d | %d | %.1fs | %.1f | %d / %d |\n",
			m, c[outCorrect], n, 100*float64(c[outCorrect])/float64(n), first, n,
			c[outMiss], c[outFalseAlarm], c[outUnsound], c[outError], faith, secs/float64(n), float64(calls)/float64(n), restarts, free)
	}
	b.WriteString("\n`unsound` = a false statement was proved, i.e. the formalization changed its meaning; it should always be 0.\n")

	// per category
	var cats []string
	seen := map[string]bool{}
	for _, p := range problems {
		if !seen[p.Category] {
			seen[p.Category] = true
			cats = append(cats, p.Category)
		}
	}
	b.WriteString("\n## By category (correct / jobs)\n\n| model | " + strings.Join(cats, " | ") + " | expected false |\n|---|")
	b.WriteString(strings.Repeat("---|", len(cats)+1) + "\n")
	for _, m := range models {
		rs := byModel[m.String()]
		if len(rs) == 0 {
			continue
		}
		fmt.Fprintf(&b, "| %s |", m)
		for _, cat := range cats {
			ok, n := 0, 0
			for _, r := range rs {
				if r.Category == cat {
					n++
					if r.Outcome == outCorrect {
						ok++
					}
				}
			}
			fmt.Fprintf(&b, " %d/%d |", ok, n)
		}
		ok, n := 0, 0
		for _, r := range rs {
			if !r.ExpectTrue {
				n++
				if r.Outcome == outCorrect {
					ok++
				}
			}
		}
		fmt.Fprintf(&b, " %d/%d |\n", ok, n)
	}

	// per problem
	b.WriteString("\n## By problem (one mark per run: ✓ correct, ✗ miss, ✗✗ wrong verdict, ! error)\n\n| # | expect | category | statement |")
	for _, m := range models {
		fmt.Fprintf(&b, " %s |", m)
	}
	b.WriteString("\n|---|---|---|---|" + strings.Repeat("---|", len(models)) + "\n")
	var unstable []string
	for _, p := range problems {
		fmt.Fprintf(&b, "| %d | %v | %s | %s |", p.ID, p.ExpectTrue, p.Category, truncateText(p.Text, 60))
		for _, m := range models {
			var marks []string
			var secs float64
			outs := map[string]bool{}
			for _, r := range byModel[m.String()] {
				if r.Problem == p.ID {
					marks = append(marks, map[string]string{outCorrect: "✓", outMiss: "✗", outFalseAlarm: "✗✗", outUnsound: "✗✗", outError: "!"}[r.Outcome])
					secs += r.Seconds
					outs[r.Outcome] = true
				}
			}
			if len(marks) == 0 {
				b.WriteString(" – |")
				continue
			}
			fmt.Fprintf(&b, " %s %.0fs |", strings.Join(marks, ""), secs/float64(len(marks)))
			if len(outs) > 1 {
				unstable = append(unstable, fmt.Sprintf("#%d with %s", p.ID, m))
			}
		}
		b.WriteString("\n")
	}
	if runs > 1 {
		if len(unstable) == 0 {
			b.WriteString("\nStable: every problem had the same outcome in all runs.\n")
		} else {
			b.WriteString("\nUnstable (outcome changed between runs): " + strings.Join(unstable, ", ") + "\n")
		}
	}

	// error kinds
	b.WriteString("\n## Failed-attempt kinds\n\n")
	for _, m := range models {
		kinds := map[string]int{}
		total := 0
		for _, r := range byModel[m.String()] {
			for k, n := range r.ErrorKinds {
				kinds[k] += n
				total += n
			}
		}
		if total == 0 {
			fmt.Fprintf(&b, "- %s: none\n", m)
			continue
		}
		type kv struct {
			k string
			n int
		}
		var list []kv
		for k, n := range kinds {
			list = append(list, kv{k, n})
		}
		sort.Slice(list, func(i, j int) bool { return list[i].n > list[j].n || list[i].n == list[j].n && list[i].k < list[j].k })
		var parts []string
		for _, e := range list {
			parts = append(parts, fmt.Sprintf("%s %d (%.0f%%)", e.k, e.n, 100*float64(e.n)/float64(total)))
		}
		fmt.Fprintf(&b, "- %s: %s\n", m, strings.Join(parts, ", "))
	}

	// per-attempt timings
	b.WriteString("\n## Attempt timings\n\nPer job: time outside the proof attempts (formalization, checks, counterexample search), then each attempt as `n: LLM + Lean = total result`.\n\n")
	for _, r := range recs {
		if len(r.AttemptTimes) == 0 {
			fmt.Fprintf(&b, "- #%d %s run %d: other %.1fs, no attempts (%s)\n", r.Problem, r.Model, r.Run, r.OtherSeconds, orDash(string(r.Status)))
			continue
		}
		var parts []string
		for _, a := range r.AttemptTimes {
			label := fmt.Sprint(a.N)
			if a.Stage != "" && a.Stage != "outline" {
				label = a.Stage + ":" + label
			}
			switch {
			case a.Disproof:
				label = "¬" + label
			case a.Plan:
				label = "outline " + label
			case a.Step != "":
				label = a.Step + "." + label
			}
			res := "✓"
			if !a.Verified {
				res = "✗ " + strings.Join(a.Kinds, ",")
			}
			if a.Free {
				res += " (free)"
			}
			parts = append(parts, fmt.Sprintf("%s: %.1f + %.1f = %.1fs %s", label, a.LLMSeconds, a.LeanSeconds, a.LLMSeconds+a.LeanSeconds, res))
		}
		fmt.Fprintf(&b, "- #%d %s run %d: other %.1fs | %s\n", r.Problem, r.Model, r.Run, r.OtherSeconds, strings.Join(parts, " | "))
	}

	// what went wrong
	var bad []string
	for _, r := range recs {
		if r.Outcome != outCorrect {
			line := fmt.Sprintf("- #%d %s run %d: **%s** (%s)", r.Problem, r.Model, r.Run, r.Outcome, orDash(string(r.Status)))
			if r.Signature != "" {
				line += " — `theorem " + truncateText(oneLine(r.Signature), 120) + "`"
			}
			if r.Error != "" {
				line += " — " + truncateText(oneLine(r.Error), 160)
			}
			bad = append(bad, line)
		}
	}
	if len(bad) > 0 {
		b.WriteString("\n## Not correct\n\n" + strings.Join(bad, "\n") + "\n")
	}
	return b.String()
}

func modelNames(ms []modelRef) []string {
	var out []string
	for _, m := range ms {
		out = append(out, m.String())
	}
	return out
}

func orDash(s string) string {
	if s == "" {
		return "-"
	}
	return s
}

func truncateText(s string, n int) string {
	r := []rune(s)
	if len(r) <= n {
		return s
	}
	return string(r[:n-1]) + "…"
}

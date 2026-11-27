package pipeline

import (
	"context"
	"errors"
	"fmt"
	"strings"
	"sync"
	"testing"
	"time"

	"mathprover/internal/lean"
	"mathprover/internal/llm"
)

// fakeLLM routes requests by system prompt to per-task reply scripts.
type fakeLLM struct {
	mu      sync.Mutex
	split   string
	formal  []string // consumed in order
	proofs  []string
	plans   []string            // outline replies
	steps   map[string][]string // proofs of outline steps, by step name
	judge   []string            // faithfulness verdicts; default: match
	reqs    []llm.Request
	costPer float64
	failAll error
}

func (f *fakeLLM) Chat(_ context.Context, r llm.Request) (*llm.Response, error) {
	f.mu.Lock()
	defer f.mu.Unlock()
	f.reqs = append(f.reqs, r)
	if f.failAll != nil {
		return nil, f.failAll
	}
	sys := r.Messages[0].Content
	pop := func(q *[]string) string {
		if len(*q) == 0 {
			return "```lean\nnothing_left\n```"
		}
		s := (*q)[0]
		*q = (*q)[1:]
		return s
	}
	var c string
	switch {
	case strings.Contains(sys, "split a user's"):
		c = f.split
	case strings.Contains(sys, "translate natural-language"):
		c = pop(&f.formal)
	case strings.Contains(sys, "say in plain mathematical English"):
		c = "back-translated"
	case strings.Contains(sys, "write tactic proofs") && f.steps != nil && strings.Contains(r.Messages[1].Content, "is the step `"):
		_, rest, _ := strings.Cut(r.Messages[1].Content, "is the step `")
		name, _, _ := strings.Cut(rest, "`")
		q := f.steps[name]
		c = pop(&q)
		f.steps[name] = q
	case strings.Contains(sys, "write tactic proofs"):
		c = pop(&f.proofs)
	case strings.Contains(sys, "proof OUTLINE"):
		c = pop(&f.plans)
	case strings.Contains(sys, "explain a formally verified"):
		c = "explanation"
	case strings.Contains(sys, "says exactly what an informal"):
		c = `{"match": true, "issues": []}`
		if len(f.judge) > 0 {
			c = pop(&f.judge)
		}
	default:
		return nil, fmt.Errorf("unrouted request: %.60s", sys)
	}
	return &llm.Response{Content: c, CostUSD: f.costPer}, nil
}

func formal(name, sig string) string {
	return fmt.Sprintf("```lean\ntheorem %s %s := by sorry\n```\nNone.", name, sig)
}

func proof(body string) string { return "```lean\n" + body + "\n```" }

// fakeLean: signatures containing BAD fail to elaborate; proofs equal to
// "good" (or "use_<name>" when <name> is in the base snapshot) verify.
type fakeLean struct {
	mu      sync.Mutex
	proofs  []string
	bases   []string // base Code() seen per CheckProof
	queries []string // tool queries
}

func (f *fakeLean) CheckStatement(_ context.Context, base *lean.Snapshot, s lean.Statement) (*lean.StatementCheck, error) {
	code := lean.StatementCode(s)
	if strings.Contains(s.Signature, "BAD") {
		return &lean.StatementCheck{Code: code, Errors: []lean.Diagnostic{{Message: lean.Message{Severity: "error", Pos: lean.Pos{Line: 1}, Data: "unknown identifier 'BAD'"}, Kind: lean.KindUnknownIdent}}}, nil
	}
	return &lean.StatementCheck{OK: true, Code: code, Snapshot: base.Extend(code)}, nil
}

func (f *fakeLean) ExploreProof(ctx context.Context, base *lean.Snapshot, s lean.Statement, body string) (*lean.Outcome, error) {
	return f.CheckProof(ctx, base, s, body)
}

func (f *fakeLean) Query(_ context.Context, base *lean.Snapshot, code string, _ time.Duration) (*lean.Result, error) {
	f.mu.Lock()
	f.queries = append(f.queries, code)
	f.mu.Unlock()
	return &lean.Result{Messages: []lean.Message{{Severity: "info", Data: "result of " + code}}}, nil
}

func (f *fakeLean) CheckProof(_ context.Context, base *lean.Snapshot, s lean.Statement, body string) (*lean.Outcome, error) {
	f.mu.Lock()
	f.proofs = append(f.proofs, body)
	f.bases = append(f.bases, base.Code())
	f.mu.Unlock()
	a := lean.NewAttempt(s, body)
	// "exact?" verifies and Lean suggests "exact found_term"; proofs starting
	// with "exact found" verify too.
	ok := a.Body == "good" || a.Body == "exact?" || strings.HasPrefix(a.Body, "exact found") || assembledOK(a.Body)
	if dep, found := strings.CutPrefix(a.Body, "use_"); found {
		ok = strings.Contains(base.Code(), "theorem "+dep+" ")
	}
	res := &lean.Result{Snapshot: base.Extend(a.Code)}
	switch {
	case ok:
		res.Messages = []lean.Message{{Severity: "info", Pos: lean.Pos{Line: a.AxiomsLine}, Data: "HARNESS_AXIOMS_OK " + s.Name + ": []"}}
		if a.Body == "exact?" {
			res.Messages = append(res.Messages, lean.Message{Severity: "info", Pos: lean.Pos{Line: a.BodyLine, Column: 2}, Data: "Try this: exact found_term"})
		}
	case a.Body == "unknown_id":
		res.Messages = []lean.Message{{Severity: "error", Pos: lean.Pos{Line: a.BodyLine, Column: 2}, Data: "Unknown identifier `Foo.baz`"}}
	default:
		res.Messages = []lean.Message{{Severity: "error", Pos: lean.Pos{Line: a.BodyLine}, Data: "linarith failed"}}
	}
	return &lean.Outcome{Attempt: a, Result: res, Verdict: lean.Judge(a, res)}, nil
}

func run(t *testing.T, fl *fakeLLM, fk *fakeLean, opts Options, hooks Hooks, input string) (*Result, error, []Event) {
	t.Helper()
	var events []Event
	user := hooks.OnEvent
	hooks.OnEvent = func(e Event) {
		events = append(events, e)
		if user != nil {
			user(e)
		}
	}
	if opts.PlanAttempts == 0 {
		opts.NoPlan = true // tests of the outline stage set PlanAttempts
	}
	p := New(llm.NewAgent(fl, llm.Options{}), fk, legacy(opts))
	res, err := p.Run(context.Background(), input, hooks)
	return res, err, events
}

// legacy makes older tests deterministic: one stage, 6 attempts, no
// automation, unless the test configures those itself.
func legacy(o Options) Options {
	if o.Stages == nil {
		o.Stages = []Stage{{Name: "test", Sessions: 1, Attempts: 6}}
	}
	if o.Automation == nil {
		o.NoAutomation = true
	}
	return o
}

func TestHappyPathWithChaining(t *testing.T) {
	fl := &fakeLLM{
		split:  `{"statements": ["first", "second"]}`,
		formal: []string{formal("stmt_1", ": 1 = 1"), formal("stmt_2", ": 2 = 2")},
		proofs: []string{proof("wrong"), proof("good"), proof("use_stmt_1")},
	}
	fk := &fakeLean{}
	res, err, events := run(t, fl, fk, Options{}, Hooks{}, "first. second.")
	if err != nil {
		t.Fatal(err)
	}
	s1, s2 := res.Statements[0], res.Statements[1]
	if s1.Status != StatusProved || s1.Proof != "good" || len(s1.Attempts) != 2 || s1.Explanation != "explanation" {
		t.Errorf("stmt_1 = %+v", s1)
	}
	if s2.Status != StatusProved || s2.Proof != "use_stmt_1" {
		t.Errorf("stmt_2 should prove using stmt_1 in its base: %+v", s2)
	}
	// second feedback round must contain the Lean error for the first attempt
	if !strings.Contains(s1.Attempts[0].Feedback, "linarith failed") {
		t.Errorf("feedback = %q", s1.Attempts[0].Feedback)
	}
	if !strings.Contains(res.LeanFile, "import Mathlib") || !strings.Contains(res.LeanFile, "theorem stmt_1 : 1 = 1 := by\n  good") ||
		!strings.Contains(res.LeanFile, "theorem stmt_2") {
		t.Errorf("lean file:\n%s", res.LeanFile)
	}
	if last := events[len(events)-1]; last.Type != EvDone || last.Message != "2/2 proved" {
		t.Errorf("last event = %+v", last)
	}
	// the prover for stmt_2 was told stmt_1 is available
	var stmt2Intro string
	for _, r := range fl.reqs {
		if strings.Contains(r.Messages[0].Content, "write tactic proofs") && strings.Contains(r.Messages[1].Content, "stmt_2") {
			stmt2Intro = r.Messages[1].Content
		}
	}
	if !strings.Contains(stmt2Intro, "theorem stmt_1 : 1 = 1") {
		t.Errorf("stmt_2 prompt lacks stmt_1:\n%s", stmt2Intro)
	}
}

func TestFormalizationRepairAndGiveUp(t *testing.T) {
	fl := &fakeLLM{
		split:  `{"statements": ["a", "b"]}`,
		formal: []string{formal("stmt_1", ": BAD"), formal("stmt_1", ": 1 = 1"), formal("stmt_2", ": BAD"), formal("stmt_2", ": BAD"), formal("stmt_2", ": BAD")},
		proofs: []string{proof("good")},
	}
	res, err, _ := run(t, fl, &fakeLean{}, Options{NoExplain: true}, Hooks{}, "a b")
	if err != nil {
		t.Fatal(err)
	}
	if res.Statements[0].Status != StatusProved {
		t.Errorf("stmt_1 should be repaired and proved: %+v", res.Statements[0])
	}
	if s := res.Statements[1]; s.Status != StatusUnformal || !strings.Contains(s.Error, "unknown identifier") {
		t.Errorf("stmt_2 = %+v", s)
	}
	// the repair request carried the Lean error
	found := false
	for _, r := range fl.reqs {
		for _, m := range r.Messages {
			if strings.Contains(m.Content, "rejected") && strings.Contains(m.Content, "unknown identifier 'BAD'") {
				found = true
			}
		}
	}
	if !found {
		t.Error("formalization retry did not include the Lean error")
	}
}

func TestProofGivesUpAndDetectsRepeats(t *testing.T) {
	fl := &fakeLLM{
		formal: []string{formal("stmt_1", ": 1 = 1")},
		proofs: []string{proof("bad1"), proof("bad1"), proof("bad2")},
	}
	fk := &fakeLean{}
	res, err, _ := run(t, fl, fk, Options{SkipSplit: true, MaxProofAttempts: 3, NoDisprove: true}, Hooks{}, "x")
	if err != nil {
		t.Fatal(err)
	}
	s := res.Statements[0]
	// bad1, bad1 (exact repeat: not sent to Lean and not charged), bad2,
	// then a 3rd charged attempt (the fake has no proofs left).
	if s.Status != StatusFailed || len(s.Attempts) != 4 || proofAttempts(s) != 3 {
		t.Fatalf("stmt = %+v", s)
	}
	if s.Attempts[1].ErrorKinds[0] != "repeated" || !s.Attempts[1].Free || len(fk.proofs) != 3 {
		t.Errorf("repeat should skip Lean and be free: kinds=%v free=%v lean calls=%d", s.Attempts[1].ErrorKinds, s.Attempts[1].Free, len(fk.proofs))
	}
	if !strings.Contains(res.LeanFile, "/- Not proved (failed):\ntheorem stmt_1 : 1 = 1") {
		t.Errorf("lean file:\n%s", res.LeanFile)
	}
}

func TestParallelSessionsFirstWins(t *testing.T) {
	fl := &fakeLLM{
		formal: []string{formal("stmt_1", ": 1 = 1")},
		proofs: []string{proof("good"), proof("bad"), proof("bad"), proof("bad")},
	}
	res, err, _ := run(t, fl, &fakeLean{}, Options{SkipSplit: true, ParallelSessions: 3, NoExplain: true}, Hooks{}, "x")
	if err != nil || res.Statements[0].Status != StatusProved {
		t.Fatalf("err=%v stmt=%+v", err, res.Statements[0])
	}
}

func TestConfirmRevision(t *testing.T) {
	fl := &fakeLLM{
		formal: []string{formal("stmt_1", "(x : ℕ) : x ≥ 0"), formal("stmt_1", "(x : ℝ) : x ^ 2 ≥ 0")},
		proofs: []string{proof("good")},
	}
	var proposals []Proposal
	confirm := func(_ context.Context, p Proposal) (Decision, error) {
		proposals = append(proposals, p)
		if len(proposals) == 1 {
			return Decision{Correction: "x is real and it is x squared"}, nil
		}
		return Decision{Accept: true}, nil
	}
	res, err, _ := run(t, fl, &fakeLean{}, Options{SkipSplit: true, NoExplain: true}, Hooks{Confirm: confirm}, "x^2 >= 0")
	if err != nil {
		t.Fatal(err)
	}
	if len(proposals) != 2 || proposals[0].BackTranslation != "back-translated" || res.Statements[0].Signature != "(x : ℝ) : x ^ 2 ≥ 0" {
		t.Fatalf("proposals=%+v stmt=%+v", proposals, res.Statements[0])
	}
	// the correction reached the formalizer
	found := false
	for _, r := range fl.reqs {
		for _, m := range r.Messages {
			if strings.Contains(m.Content, "x is real and it is x squared") {
				found = true
			}
		}
	}
	if !found {
		t.Error("user correction not sent to formalizer")
	}

	// rejecting without a correction skips the statement
	fl2 := &fakeLLM{formal: []string{formal("stmt_1", ": 1 = 1")}}
	res2, _, _ := run(t, fl2, &fakeLean{}, Options{SkipSplit: true}, Hooks{Confirm: func(context.Context, Proposal) (Decision, error) {
		return Decision{}, nil
	}}, "x")
	if res2.Statements[0].Status != StatusUnformal {
		t.Errorf("status = %s", res2.Statements[0].Status)
	}
}

func TestFatalErrorsStopJob(t *testing.T) {
	fl := &fakeLLM{split: `{"statements": ["a", "b"]}`}
	fl.failAll = &llm.APIError{Status: 402, Message: "Insufficient Balance"}
	res, err, _ := run(t, fl, &fakeLean{}, Options{}, Hooks{}, "a b")
	var ae *llm.APIError
	if !errors.As(err, &ae) || ae.Status != 402 {
		t.Fatalf("err = %v", err)
	}
	_ = res

	// budget exhausted mid-job: later statements are canceled
	fl2 := &fakeLLM{
		split:   `{"statements": ["a", "b"]}`,
		formal:  []string{formal("stmt_1", ": 1 = 1"), formal("stmt_2", ": 2 = 2")},
		proofs:  []string{proof("bad"), proof("bad"), proof("bad")},
		costPer: 1,
	}
	p := New(llm.NewAgent(fl2, llm.Options{BudgetUSD: 2.5}), &fakeLean{}, legacy(Options{NoExplain: true}))
	res2, err := p.Run(context.Background(), "a b", Hooks{})
	if !errors.Is(err, llm.ErrBudget) {
		t.Fatalf("err = %v", err)
	}
	if res2.Statements[1].Status != StatusCanceled || res2.CostUSD < 2.5 {
		t.Errorf("stmts=%+v cost=%g", res2.Statements, res2.CostUSD)
	}
}

func TestContextCanceled(t *testing.T) {
	fl := &fakeLLM{formal: []string{formal("stmt_1", ": 1 = 1")}, proofs: []string{proof("good")}}
	ctx, cancel := context.WithCancel(context.Background())
	cancel()
	p := New(llm.NewAgent(fl, llm.Options{}), &fakeLean{}, legacy(Options{SkipSplit: true}))
	if _, err := p.Run(ctx, "x", Hooks{}); !errors.Is(err, context.Canceled) {
		t.Fatalf("err = %v", err)
	}
}

type fakeVerifier struct {
	reject map[string]bool
	err    error
	code   string
	items  []lean.VerifyItem
}

func (f *fakeVerifier) Verify(_ context.Context, code string, items []lean.VerifyItem) (*lean.VerifyReport, error) {
	f.code, f.items = code, items
	if f.err != nil {
		return nil, f.err
	}
	rep := &lean.VerifyReport{KernelOK: true, OK: true}
	for _, it := range items {
		v := lean.VerifiedItem{Name: it.Name, OK: !f.reject[it.Name], Axioms: []string{"propext"}}
		if !v.OK {
			v.Error = "type differs from the confirmed statement"
			rep.OK = false
		}
		rep.Items = append(rep.Items, v)
	}
	return rep, nil
}

func TestIndependentVerification(t *testing.T) {
	script := func() *fakeLLM {
		return &fakeLLM{
			split:  `{"statements": ["a", "b"]}`,
			formal: []string{formal("stmt_1", ": 1 = 1"), formal("stmt_2", ": 2 = 2")},
			proofs: []string{proof("good"), proof("good")},
		}
	}

	// accepted: statuses stay proved, verdicts attached, file passed through
	fv := &fakeVerifier{}
	res, err, events := run(t, script(), &fakeLean{}, Options{NoExplain: true, Verifier: fv}, Hooks{}, "a b")
	if err != nil {
		t.Fatal(err)
	}
	if len(fv.items) != 2 || fv.items[1].Signature != ": 2 = 2" || !strings.HasPrefix(fv.code, "import Mathlib\nimport Harness\n\ntheorem stmt_1") {
		t.Errorf("verifier input: items=%+v code=%q", fv.items, fv.code)
	}
	for _, s := range res.Statements {
		if s.Status != StatusProved || s.Verification == nil || !s.Verification.OK {
			t.Errorf("%s = %+v", s.Name, s)
		}
	}
	var sawVerified bool
	for _, e := range events {
		sawVerified = sawVerified || (e.Type == EvVerified && strings.Contains(e.Message, "2/2"))
	}
	if !sawVerified || res.Verification == nil {
		t.Error("missing verified event or report")
	}

	// one rejected: it becomes failed, the other stays proved
	res, _, events = run(t, script(), &fakeLean{}, Options{NoExplain: true, Verifier: &fakeVerifier{reject: map[string]bool{"stmt_2": true}}}, Hooks{}, "a b")
	if res.Statements[0].Status != StatusProved || res.Statements[1].Status != StatusFailed ||
		!strings.Contains(res.Statements[1].Error, "independent verification rejected") {
		t.Errorf("statements: %+v / %+v", res.Statements[0], res.Statements[1])
	}
	if last := events[len(events)-1]; last.Message != "1/2 proved" {
		t.Errorf("summary = %q", last.Message)
	}

	// verifier cannot run: fail closed as unverified, never proved
	res, err, _ = run(t, script(), &fakeLean{}, Options{NoExplain: true, Verifier: &fakeVerifier{err: errors.New("bwrap missing")}}, Hooks{}, "a b")
	if err != nil {
		t.Fatal(err)
	}
	for _, s := range res.Statements {
		if s.Status != StatusUnverified || !strings.Contains(s.Error, "bwrap missing") {
			t.Errorf("%s = %+v", s.Name, s)
		}
	}
}

func TestAutomationFirst(t *testing.T) {
	fl := &fakeLLM{formal: []string{formal("stmt_1", ": 1 = 1")}, proofs: []string{proof("good")}}
	fk := &fakeLean{}
	// "good" is the only body fakeLean accepts, so automation list ["omega", "good"]
	// stands in for a tactic that closes the goal.
	res, err, events := run(t, fl, fk, Options{SkipSplit: true, NoExplain: true, Automation: []string{"omega", "good"}}, Hooks{}, "x")
	if err != nil {
		t.Fatal(err)
	}
	s := res.Statements[0]
	if s.Status != StatusProved || s.Proof != "good" || len(s.Attempts) != 1 || s.Attempts[0].Stage != "auto" {
		t.Fatalf("stmt = %+v", s)
	}
	for _, r := range fl.reqs {
		if strings.Contains(r.Messages[0].Content, "write tactic proofs") {
			t.Fatal("LLM prover called although automation succeeded")
		}
	}
	var saw bool
	for _, e := range events {
		saw = saw || (e.Type == EvAutomation && strings.Contains(e.Message, "good"))
	}
	if !saw {
		t.Error("no automation event")
	}

	// nothing closes it: falls through to the LLM
	fl2 := &fakeLLM{formal: []string{formal("stmt_1", ": 1 = 1")}, proofs: []string{proof("good")}}
	res, _, _ = run(t, fl2, &fakeLean{}, Options{SkipSplit: true, NoExplain: true, Automation: []string{"omega", "simp"}}, Hooks{}, "x")
	if s := res.Statements[0]; s.Status != StatusProved || s.Attempts[len(s.Attempts)-1].Stage != "test" {
		t.Fatalf("stmt = %+v", s)
	}
}

// tryThisLean accepts "exact?" (reporting a suggestion) and the suggested term.
type tryThisLean struct{ fakeLean }

func (f *tryThisLean) CheckProof(ctx context.Context, base *lean.Snapshot, s lean.Statement, body string) (*lean.Outcome, error) {
	a := lean.NewAttempt(s, body)
	res := &lean.Result{Snapshot: base.Extend(a.Code)}
	switch a.Body {
	case "exact?", "exact Nat.le_refl 1":
		res.Messages = []lean.Message{{Severity: "info", Pos: lean.Pos{Line: a.AxiomsLine}, Data: "HARNESS_AXIOMS_OK " + s.Name + ": []"}}
		if a.Body == "exact?" {
			res.Messages = append(res.Messages, lean.Message{Severity: "info", Pos: lean.Pos{Line: a.BodyLine}, Data: "Try this: exact Nat.le_refl 1"})
		}
	default:
		res.Messages = []lean.Message{{Severity: "error", Pos: lean.Pos{Line: a.BodyLine}, Data: "nope"}}
	}
	return &lean.Outcome{Attempt: a, Result: res, Verdict: lean.Judge(a, res)}, nil
}

func TestAutomationKeepsExactSuggestion(t *testing.T) {
	fl := &fakeLLM{formal: []string{formal("stmt_1", ": 1 ≤ 1")}}
	p := New(llm.NewAgent(fl, llm.Options{}), &tryThisLean{}, Options{SkipSplit: true, NoExplain: true, Automation: []string{"omega", "exact?"}})
	res, err := p.Run(context.Background(), "x", Hooks{})
	if err != nil {
		t.Fatal(err)
	}
	if s := res.Statements[0]; s.Status != StatusProved || s.Proof != "exact Nat.le_refl 1" {
		t.Fatalf("want the suggested term as proof, got %+v", s)
	}
}

func TestStageLadder(t *testing.T) {
	// Stage 1 (1 session x 2 attempts) fails, stage 2 succeeds on its first try.
	fl := &fakeLLM{
		formal: []string{formal("stmt_1", ": 1 = 1")},
		proofs: []string{proof("bad1"), proof("bad2"), proof("good")},
	}
	stages := []Stage{
		{Name: "cheap", Spec: llm.ModelSpec{Model: "m", Effort: llm.EffortNone}, Sessions: 1, Attempts: 2},
		{Name: "deep", Spec: llm.ModelSpec{Model: "m", Effort: llm.EffortHigh}, Sessions: 1, Attempts: 2},
	}
	res, err, events := run(t, fl, &fakeLean{}, Options{SkipSplit: true, NoExplain: true, Stages: stages}, Hooks{}, "x")
	if err != nil {
		t.Fatal(err)
	}
	s := res.Statements[0]
	if s.Status != StatusProved || len(s.Attempts) != 3 {
		t.Fatalf("stmt = %+v", s)
	}
	if a := s.Attempts[2]; a.Stage != "deep" || a.Effort != "high" || a.Session != 2 || a.N != 1 {
		t.Errorf("winning attempt = %+v", a)
	}
	// each stage's requests used that stage's effort
	var efforts []llm.Effort
	for _, r := range fl.reqs {
		if strings.Contains(r.Messages[0].Content, "write tactic proofs") {
			efforts = append(efforts, r.Effort)
		}
	}
	if len(efforts) != 3 || efforts[0] != llm.EffortNone || efforts[2] != llm.EffortHigh {
		t.Errorf("efforts = %v", efforts)
	}
	var stageEvents int
	for _, e := range events {
		if e.Type == EvStage {
			stageEvents++
		}
	}
	if stageEvents != 2 {
		t.Errorf("stage events = %d", stageEvents)
	}
}

func TestRepeatsSharedAcrossSessions(t *testing.T) {
	// Two stages; the second stage repeats a body that failed in the first.
	fl := &fakeLLM{
		formal: []string{formal("stmt_1", ": 1 = 1")},
		proofs: []string{proof("bad"), proof("bad"), proof("good")},
	}
	fk := &fakeLean{}
	stages := []Stage{{Name: "a", Sessions: 1, Attempts: 1}, {Name: "b", Sessions: 1, Attempts: 2}}
	res, _, _ := run(t, fl, fk, Options{SkipSplit: true, NoExplain: true, Stages: stages}, Hooks{}, "x")
	s := res.Statements[0]
	if s.Status != StatusProved || s.Attempts[1].ErrorKinds[0] != "repeated" || !strings.Contains(s.Attempts[1].Feedback, "linarith failed") {
		t.Fatalf("stmt = %+v", s)
	}
	if len(fk.proofs) != 2 { // "bad" once, "good" once
		t.Errorf("lean checks = %d", len(fk.proofs))
	}
}

// toolChat scripts a tool-using prover: each reply is either tool calls or
// final content. Other tasks (formalize etc.) are answered like fakeLLM.
type toolChat struct {
	fakeLLM
	turns []llm.Response
	seen  [][]llm.Message // messages of each prover request
}

func (c *toolChat) Chat(ctx context.Context, r llm.Request) (*llm.Response, error) {
	if !strings.Contains(r.Messages[0].Content, "write tactic proofs") {
		return c.fakeLLM.Chat(ctx, r)
	}
	c.mu.Lock()
	defer c.mu.Unlock()
	if len(r.Tools) == 0 {
		return nil, errors.New("tool stage request without tools")
	}
	c.seen = append(c.seen, r.Messages)
	t := c.turns[0]
	c.turns = c.turns[1:]
	return &t, nil
}

func call(id, name, args string) llm.ToolCall {
	tc := llm.ToolCall{ID: id, Type: "function"}
	tc.Function.Name, tc.Function.Arguments = name, args
	return tc
}

func TestToolStage(t *testing.T) {
	tc := &toolChat{
		fakeLLM: fakeLLM{formal: []string{formal("stmt_1", "(n : ℕ) : 3 ∣ n ^ 3 - n")}},
		turns: []llm.Response{
			{ToolCalls: []llm.ToolCall{call("c1", "search_lemmas", `{"query":"pow mod","limit":5}`), call("c2", "check_name", `{"name":"Nat.pow_mod"}`)}, Reasoning: "look up"},
			{ToolCalls: []llm.ToolCall{call("c3", "check_proof", `{"tactics":"bad"}`)}},
			{ToolCalls: []llm.ToolCall{call("c4", "check_name", `{"name":"x y; #eval 1"}`), call("c5", "check_proof", `{"tactics":"good"}`)}},
		},
	}
	fk := &fakeLean{}
	stages := []Stage{{Name: "tools", Spec: llm.ModelSpec{Model: "m", Effort: llm.EffortNone}, Sessions: 1, Attempts: 2, Tools: true}}
	p := New(llm.NewAgent(tc, llm.Options{}), fk, Options{SkipSplit: true, NoExplain: true, NoAutomation: true, Stages: stages})
	res, err := p.Run(context.Background(), "x", Hooks{})
	if err != nil {
		t.Fatal(err)
	}
	s := res.Statements[0]
	if s.Status != StatusProved || s.Proof != "good" {
		t.Fatalf("stmt = %+v", s)
	}
	// both check_proof calls are attempts; the first carries Lean feedback
	if len(s.Attempts) != 2 || s.Attempts[0].Verified || !strings.Contains(s.Attempts[0].Feedback, "linarith failed") ||
		!s.Attempts[1].Verified || s.Attempts[0].ToolCalls != 3 || s.Attempts[1].ToolCalls != 2 {
		t.Fatalf("attempts = %+v", s.Attempts)
	}
	// queries reached Lean as safe single-line commands; the injection was refused
	if len(fk.queries) != 2 || fk.queries[0] != `#harness_search "pow mod" 5` || fk.queries[1] != "#check @Nat.pow_mod" {
		t.Errorf("queries = %q", fk.queries)
	}
	// the model saw tool results, Lean feedback, the refusal, and its own reasoning
	last := tc.seen[len(tc.seen)-1]
	var all string
	for _, m := range last {
		all += m.Role + ":" + m.ReasoningContent + "|" + m.Content + "\n"
	}
	for _, want := range []string{"tool:|result of #harness_search", "assistant:look up|", "linarith failed"} {
		if !strings.Contains(all, want) {
			t.Errorf("transcript missing %q:\n%s", want, all)
		}
	}
	if !strings.Contains(fmt.Sprint(len(fk.proofs)), "2") {
		t.Errorf("lean proof checks = %d", len(fk.proofs))
	}
}

func TestToolStageBudget(t *testing.T) {
	// model never stops calling tools: after the budget it is told to answer,
	// keeps calling, and the round is recorded as no_answer
	loop := llm.Response{ToolCalls: []llm.ToolCall{call("c", "check_name", `{"name":"Nat.add_comm"}`)}}
	tc := &toolChat{
		fakeLLM: fakeLLM{formal: []string{formal("stmt_1", ": 1 = 1")}},
		turns:   []llm.Response{loop, loop, loop},
	}
	stages := []Stage{{Name: "tools", Sessions: 1, Attempts: 1, Tools: true, MaxToolCalls: 2}}
	p := New(llm.NewAgent(tc, llm.Options{}), &fakeLean{}, Options{SkipSplit: true, NoExplain: true, NoAutomation: true, NoPlan: true, NoDisprove: true, Stages: stages})
	res, err := p.Run(context.Background(), "x", Hooks{})
	if err != nil {
		t.Fatal(err)
	}
	s := res.Statements[0]
	if s.Status != StatusFailed || len(s.Attempts) != 1 || s.Attempts[0].ErrorKinds[0] != "no_answer" {
		t.Fatalf("stmt = %+v", s)
	}
}

func TestLeanString(t *testing.T) {
	if got := leanString(`a "b" \ c`); got != `"a \"b\" \\ c"` {
		t.Errorf("got %s", got)
	}
}

type fakeSuggester struct {
	mu    sync.Mutex
	asked [][]string
}

func (f *fakeSuggester) Suggest(_ context.Context, _ Checker, unknown []string) string {
	f.mu.Lock()
	defer f.mu.Unlock()
	f.asked = append(f.asked, unknown)
	return "SUGGESTION: Foo.bar exists"
}

func TestUnknownIdentifierGetsSuggestions(t *testing.T) {
	fl := &fakeLLM{formal: []string{formal("stmt_1", ": 1 = 1")}, proofs: []string{proof("unknown_id"), proof("good")}}
	sug := &fakeSuggester{}
	res, err, _ := run(t, fl, &fakeLean{}, Options{SkipSplit: true, NoExplain: true, Suggester: sug}, Hooks{}, "x")
	if err != nil || res.Statements[0].Status != StatusProved {
		t.Fatalf("err=%v status=%s", err, res.Statements[0].Status)
	}
	if len(sug.asked) != 1 || len(sug.asked[0]) != 1 || sug.asked[0][0] != "Foo.baz" {
		t.Errorf("suggester asked %v, want [[Foo.baz]]", sug.asked)
	}
	if fb := res.Statements[0].Attempts[0].Feedback; !strings.Contains(fb, "SUGGESTION: Foo.bar exists") {
		t.Errorf("feedback lacks the suggestion:\n%s", fb)
	}
	// ...and the model saw it in its next request.
	var seen bool
	for _, r := range fl.reqs {
		for _, m := range r.Messages {
			seen = seen || strings.Contains(m.Content, "SUGGESTION: Foo.bar exists")
		}
	}
	if !seen {
		t.Error("suggestion never reached the model")
	}

	// Other errors do not ask the suggester.
	sug2 := &fakeSuggester{}
	fl2 := &fakeLLM{formal: []string{formal("stmt_1", ": 1 = 1")}, proofs: []string{proof("wrong"), proof("good")}}
	run(t, fl2, &fakeLean{}, Options{SkipSplit: true, NoExplain: true, Suggester: sug2}, Hooks{}, "x")
	if len(sug2.asked) != 0 {
		t.Errorf("suggester asked for a non-identifier error: %v", sug2.asked)
	}
}

func TestSearchTacticsReplacedInVerifiedProof(t *testing.T) {
	fl := &fakeLLM{formal: []string{formal("stmt_1", ": 1 = 1")}, proofs: []string{proof("exact?")}}
	fk := &fakeLean{}
	res, err, events := run(t, fl, fk, Options{SkipSplit: true, NoExplain: true}, Hooks{}, "x")
	if err != nil {
		t.Fatal(err)
	}
	sr := res.Statements[0]
	if sr.Status != StatusProved || sr.Proof != "exact found_term" || !strings.Contains(sr.LeanCode, "exact found_term") {
		t.Errorf("proof = %q, lean code:\n%s", sr.Proof, sr.LeanCode)
	}
	if !strings.Contains(res.LeanFile, "exact found_term") || strings.Contains(res.LeanFile, "exact?") {
		t.Errorf("Lean file not updated:\n%s", res.LeanFile)
	}
	var simplified bool
	for _, e := range events {
		simplified = simplified || (e.Type == EvSimplified && strings.Contains(e.Message, "replaced 1"))
	}
	if !simplified || len(fk.proofs) != 2 || fk.proofs[1] != "exact found_term" {
		t.Errorf("simplified event=%v, checked proofs=%q", simplified, fk.proofs)
	}

	// KeepSearchTactics leaves the proof alone.
	fl2 := &fakeLLM{formal: []string{formal("stmt_1", ": 1 = 1")}, proofs: []string{proof("exact?")}}
	res2, _, _ := run(t, fl2, &fakeLean{}, Options{SkipSplit: true, NoExplain: true, KeepSearchTactics: true}, Hooks{}, "x")
	if res2.Statements[0].Proof != "exact?" {
		t.Errorf("KeepSearchTactics: proof = %q", res2.Statements[0].Proof)
	}
}

// FindCounterexample makes fakeLean a CounterexampleFinder: signatures
// containing FALSE have a counterexample.
func (f *fakeLean) FindCounterexample(_ context.Context, _ *lean.Snapshot, s lean.Statement) (string, error) {
	if strings.Contains(s.Signature, "FALSE") {
		return "n := 1\nissue: 2 ≤ 1 does not hold", nil
	}
	return "", nil
}

func TestFaithfulnessMismatchIsFixedOnce(t *testing.T) {
	fl := &fakeLLM{
		formal: []string{formal("stmt_1", ": WEAK"), formal("stmt_1", ": 1 = 1")},
		judge:  []string{`{"match": false, "issues": ["the hypothesis \(x > 0\) is missing"]}`, `{"match": true, "issues": []}`},
		proofs: []string{proof("good")},
	}
	res, err, events := run(t, fl, &fakeLean{}, Options{SkipSplit: true, NoExplain: true}, Hooks{}, "x")
	if err != nil {
		t.Fatal(err)
	}
	s := res.Statements[0]
	if s.Signature != ": 1 = 1" || s.Status != StatusProved || !s.FaithfulnessChecked || len(s.FaithfulnessIssues) != 0 {
		t.Errorf("stmt = %+v", s)
	}
	var retried, warned bool
	for _, r := range fl.reqs {
		for _, m := range r.Messages {
			retried = retried || strings.Contains(m.Content, `the hypothesis \(x > 0\) is missing`)
		}
	}
	for _, e := range events {
		warned = warned || (e.Type == EvFaithfulness && strings.Contains(e.Message, "may differ"))
	}
	if !retried || !warned {
		t.Errorf("mismatch not sent back to the formalizer (retried=%v warned=%v)", retried, warned)
	}

	// A persisting mismatch is fixed once; the fix is no better, so the first
	// formalization is kept, its issue recorded, and it is proved anyway.
	bad := `{"match": false, "issues": ["uses natural-number subtraction"]}`
	fl2 := &fakeLLM{
		formal: []string{formal("stmt_1", ": 1 = 1"), formal("stmt_1", ": 2 = 2")},
		judge:  []string{bad, bad},
		proofs: []string{proof("good")},
	}
	res2, _, _ := run(t, fl2, &fakeLean{}, Options{SkipSplit: true, NoExplain: true}, Hooks{}, "x")
	s2 := res2.Statements[0]
	if s2.Status != StatusProved || s2.Signature != ": 1 = 1" || len(s2.FaithfulnessIssues) != 1 {
		t.Errorf("stmt = %+v", s2)
	}

	// Disabled: no judge request at all.
	fl3 := &fakeLLM{formal: []string{formal("stmt_1", ": 1 = 1")}, proofs: []string{proof("good")}}
	run(t, fl3, &fakeLean{}, Options{SkipSplit: true, NoExplain: true, NoFaithfulnessCheck: true}, Hooks{}, "x")
	for _, r := range fl3.reqs {
		if strings.Contains(r.Messages[0].Content, "says exactly what an informal") {
			t.Error("faithfulness check ran although disabled")
		}
	}
}

func TestCounterexampleSkipsProving(t *testing.T) {
	fl := &fakeLLM{formal: []string{formal("stmt_1", "(n : ℕ) : FALSE n")}, proofs: []string{proof("good")}}
	fk := &fakeLean{}
	res, err, events := run(t, fl, fk, Options{SkipSplit: true, NoExplain: true}, Hooks{}, "x")
	if err != nil {
		t.Fatal(err)
	}
	s := res.Statements[0]
	if s.Status != StatusDisproved || !strings.Contains(s.Counterexample, "n := 1") || len(s.Attempts) != 0 || len(fk.proofs) != 0 {
		t.Errorf("stmt = %+v, lean proofs = %v", s, fk.proofs)
	}
	if !strings.Contains(res.LeanFile, "FALSE as formalized (counterexample") {
		t.Errorf("lean file:\n%s", res.LeanFile)
	}
	if last := events[len(events)-1]; last.Message != "0/1 proved, 1 disproved" {
		t.Errorf("summary = %q", last.Message)
	}
}

func TestDisproveAfterProofsFail(t *testing.T) {
	fl := &fakeLLM{
		formal: []string{formal("stmt_1", "(n : ℕ) (h : 0 < n) : n ^ 2 ≥ 2 * n")},
		proofs: []string{proof("bad1"), proof("bad2"), proof("good")},
	}
	res, err, _ := run(t, fl, &fakeLean{}, Options{SkipSplit: true, NoExplain: true, MaxProofAttempts: 2}, Hooks{}, "x")
	if err != nil {
		t.Fatal(err)
	}
	s := res.Statements[0]
	if s.Status != StatusDisproved || s.Proof != "good" || !strings.Contains(s.LeanCode, "theorem stmt_1_false : ¬ (∀ (n : ℕ) (h : 0 < n), n ^ 2 ≥ 2 * n) := by") {
		t.Fatalf("stmt = %+v", s)
	}
	if len(s.Attempts) != 3 || s.Attempts[0].Disproof || !s.Attempts[2].Disproof {
		t.Errorf("attempts = %+v", s.Attempts)
	}
	var told bool
	for _, r := range fl.reqs {
		told = told || (len(r.Messages) > 1 && strings.Contains(r.Messages[1].Content, "NEGATION"))
	}
	if !told {
		t.Error("disproof prompt does not say it is the negation")
	}
	if !strings.Contains(res.LeanFile, "stmt_1 is FALSE as formalized") || !strings.Contains(res.LeanFile, "theorem stmt_1_false") {
		t.Errorf("lean file:\n%s", res.LeanFile)
	}
}

// The failure seen with gpt-6-luna: the check objected that a correctly
// formalized false statement is false, and the "fix" added a hypothesis to
// make it true. The first formalization must stand (and then be disproved).
func TestWrongFaithfulnessObjectionCannotWeakenStatement(t *testing.T) {
	fl := &fakeLLM{
		formal: []string{formal("stmt_1", "(n : ℕ) : FALSE n"), formal("stmt_1", "(n : ℕ) (h : n ≠ 1) : FALSE n")},
		judge: []string{
			`{"match": false, "issues": ["The inequality fails at n = 1."]}`,
			`{"match": false, "issues": ["The Lean statement adds the hypothesis n ≠ 1."]}`,
		},
	}
	res, err, events := run(t, fl, &fakeLean{}, Options{SkipSplit: true, NoExplain: true}, Hooks{}, "n^2 >= 2n")
	if err != nil {
		t.Fatal(err)
	}
	s := res.Statements[0]
	if s.Signature != "(n : ℕ) : FALSE n" || s.Status != StatusDisproved {
		t.Fatalf("stmt = %+v", s)
	}
	var kept bool
	for _, e := range events {
		kept = kept || (e.Type == EvFaithfulness && strings.Contains(e.Message, "keeping the first"))
	}
	if !kept {
		t.Error("no event saying the first formalization was kept")
	}
	// The fix request forbids weakening.
	var warned bool
	for _, r := range fl.reqs {
		for _, m := range r.Messages {
			warned = warned || strings.Contains(m.Content, "a false statement must stay false")
		}
	}
	if !warned {
		t.Error("fix request does not forbid making the statement true")
	}
}

func TestFaithfulnessFixRejectedByLeanKeepsFirst(t *testing.T) {
	fl := &fakeLLM{
		formal: []string{formal("stmt_1", ": 1 = 1"), formal("stmt_1", ": BAD")},
		judge:  []string{`{"match": false, "issues": ["something"]}`},
		proofs: []string{proof("good")},
	}
	res, err, _ := run(t, fl, &fakeLean{}, Options{SkipSplit: true, NoExplain: true}, Hooks{}, "x")
	if err != nil {
		t.Fatal(err)
	}
	if s := res.Statements[0]; s.Status != StatusProved || s.Signature != ": 1 = 1" || len(s.FaithfulnessIssues) != 1 {
		t.Errorf("stmt = %+v", s)
	}
}

func TestFalseClaimJumpsToDisproof(t *testing.T) {
	fl := &fakeLLM{
		formal: []string{formal("stmt_1", "(x : ℝ) : x ^ 2 ≥ x")},
		// attempt 1 fails, attempt 2 says FALSE, the disproof succeeds
		proofs: []string{proof("bad"), "FALSE\ncounterexample: x = 1/2", proof("good")},
	}
	fk := &fakeLean{}
	res, err, events := run(t, fl, fk, Options{SkipSplit: true, NoExplain: true}, Hooks{}, "x^2 >= x")
	if err != nil {
		t.Fatal(err)
	}
	s := res.Statements[0]
	if s.Status != StatusDisproved || len(s.Attempts) != 3 {
		t.Fatalf("stmt = %+v", s)
	}
	if k := s.Attempts[1].ErrorKinds; len(k) != 1 || k[0] != "claims_false" || s.Attempts[1].Disproof || !s.Attempts[2].Disproof {
		t.Errorf("attempts = %+v", s.Attempts)
	}
	if len(fk.proofs) != 2 { // the FALSE reply never reaches Lean
		t.Errorf("Lean checked %q", fk.proofs)
	}
	var why bool
	for _, e := range events {
		why = why || (e.Type == EvDisproving && strings.Contains(e.Message, "model says the statement is false"))
	}
	if !why {
		t.Error("disproving event does not say why")
	}
}

func TestWrongFalseClaimResumesProof(t *testing.T) {
	fl := &fakeLLM{
		formal: []string{formal("stmt_1", ": 1 = 1")},
		// FALSE at attempt 1; the single disproof attempt after a claim
		// fails; the resumed proof (no second claim) succeeds.
		proofs: []string{"FALSE.", proof("bad1"), proof("bad2"), proof("good")},
	}
	res, err, events := run(t, fl, &fakeLean{}, Options{SkipSplit: true, NoExplain: true, MaxProofAttempts: 4}, Hooks{}, "1 = 1")
	if err != nil {
		t.Fatal(err)
	}
	s := res.Statements[0]
	if s.Status != StatusProved || s.Proof != "good" {
		t.Fatalf("stmt = %+v", s)
	}
	disproofs := 0
	var resumed, told bool
	refused := true // nothing to refuse in this scenario
	for _, a := range s.Attempts {
		if a.Disproof {
			disproofs++
		}
	}
	if disproofs != 1 {
		t.Errorf("%d disproof attempts after a FALSE claim, want 1", disproofs)
	}
	for _, e := range events {
		resumed = resumed || (e.Type == EvResuming && strings.Contains(e.Message, `resuming the proof at stage 1/1 "test"`))
	}
	for _, r := range fl.reqs {
		told = told || (len(r.Messages) > 1 && strings.Contains(r.Messages[1].Content, "could not be confirmed"))
	}
	if !refused || !resumed || !told {
		t.Errorf("refused=%v resumed=%v told=%v; attempts=%+v", refused, resumed, told, s.Attempts)
	}
}

// The Fermat-number case: the claim is right but the negation needs more
// than one attempt. Repeating FALSE after proving resumed earns the rest of
// the disproof budget (1 + 2 = DisproveAttempts).
func TestInsistentFalseClaimGetsTheFullBudget(t *testing.T) {
	fl := &fakeLLM{
		formal: []string{formal("stmt_1", ": 1 = 1")},
		proofs: []string{"FALSE", proof("bad1"), "FALSE: still false, n = 5", proof("bad2"), proof("good")},
	}
	res, err, events := run(t, fl, &fakeLean{}, Options{SkipSplit: true, NoExplain: true}, Hooks{}, "x")
	if err != nil {
		t.Fatal(err)
	}
	s := res.Statements[0]
	disproofs := 0
	for _, a := range s.Attempts {
		if a.Disproof {
			disproofs++
		}
	}
	if s.Status != StatusDisproved || disproofs != 3 {
		t.Fatalf("status=%s disproofs=%d attempts=%+v", s.Status, disproofs, s.Attempts)
	}
	var insisted bool
	for _, e := range events {
		insisted = insisted || (e.Type == EvDisproving && strings.Contains(e.Message, "insists") && strings.Contains(e.Message, "2 attempt(s)"))
	}
	if !insisted {
		t.Error("no 'insists' disproving event with the remaining 2 attempts")
	}

	// After the whole budget is spent, a further FALSE is refused.
	fl2 := &fakeLLM{
		formal: []string{formal("stmt_1", ": 1 = 1")},
		proofs: []string{"FALSE", proof("b1"), "FALSE", proof("b2"), proof("b3"), "FALSE", proof("good")},
	}
	res2, err, _ := run(t, fl2, &fakeLean{}, Options{SkipSplit: true, NoExplain: true}, Hooks{}, "x")
	if err != nil {
		t.Fatal(err)
	}
	s2 := res2.Statements[0]
	var refused bool
	for _, a := range s2.Attempts {
		refused = refused || (!a.Disproof && strings.Contains(a.Feedback, "FALSE is not accepted here"))
	}
	if s2.Status != StatusProved || !refused {
		t.Errorf("status=%s refused=%v attempts=%+v", s2.Status, refused, s2.Attempts)
	}
}

func TestFalseRefusedWhileProvingTheNegation(t *testing.T) {
	fl := &fakeLLM{
		formal: []string{formal("stmt_1", ": 1 = 1")},
		// claim, then a FALSE inside the disproof (refused), then the disproof
		proofs: []string{"FALSE", "FALSE", proof("good")},
	}
	res, err, _ := run(t, fl, &fakeLean{}, Options{SkipSplit: true, NoExplain: true, ClaimDisproveAttempts: 2}, Hooks{}, "x")
	if err != nil {
		t.Fatal(err)
	}
	s := res.Statements[0]
	if s.Status != StatusDisproved || len(s.Attempts) != 3 || !strings.Contains(s.Attempts[1].Feedback, "FALSE is not an answer here") {
		t.Errorf("stmt = %+v", s)
	}
}

func TestFalseNotAcceptedWhenDisprovingIsOff(t *testing.T) {
	fl := &fakeLLM{formal: []string{formal("stmt_1", ": 1 = 1")}, proofs: []string{"FALSE", proof("good")}}
	res, err, _ := run(t, fl, &fakeLean{}, Options{SkipSplit: true, NoExplain: true, NoDisprove: true}, Hooks{}, "x")
	if err != nil || res.Statements[0].Status != StatusProved || len(res.Statements[0].Attempts) != 2 {
		t.Fatalf("err=%v stmt=%+v", err, res.Statements[0])
	}
	if fb := res.Statements[0].Attempts[0].Feedback; !strings.Contains(fb, "FALSE is not accepted") {
		t.Errorf("feedback = %q", fb)
	}
}

func TestVerificationCoversDisproofs(t *testing.T) {
	script := func() *fakeLLM {
		return &fakeLLM{
			formal: []string{formal("stmt_1", "(n : ℕ) (h : 0 < n) : n ^ 2 ≥ 2 * n")},
			proofs: []string{proof("bad1"), proof("bad2"), proof("good")}, // the third proves the negation
		}
	}
	opts := func(fv *fakeVerifier) Options {
		return Options{SkipSplit: true, NoExplain: true, MaxProofAttempts: 2, Verifier: fv}
	}

	fv := &fakeVerifier{}
	res, err, _ := run(t, script(), &fakeLean{}, opts(fv), Hooks{}, "x")
	if err != nil {
		t.Fatal(err)
	}
	s := res.Statements[0]
	if len(fv.items) != 1 || fv.items[0].Name != "stmt_1_false" || fv.items[0].Signature != ": ¬ (∀ (n : ℕ) (h : 0 < n), n ^ 2 ≥ 2 * n)" ||
		!strings.Contains(fv.code, "theorem stmt_1_false") {
		t.Fatalf("verifier input: items=%+v code=%q", fv.items, fv.code)
	}
	if s.Status != StatusDisproved || s.Verification == nil || !s.Verification.OK {
		t.Errorf("stmt = %+v", s)
	}

	// A rejected proof of the negation leaves the statement unresolved.
	res, _, _ = run(t, script(), &fakeLean{}, opts(&fakeVerifier{reject: map[string]bool{"stmt_1_false": true}}), Hooks{}, "x")
	s = res.Statements[0]
	if s.Status != StatusFailed || s.LeanCode != "" || !strings.Contains(s.Error, "rejected the proof of the negation") ||
		strings.Contains(res.LeanFile, "theorem stmt_1_false") {
		t.Errorf("stmt = %+v\nlean file:\n%s", s, res.LeanFile)
	}

	// The verifier cannot run: the disproof stands, with a note.
	res, _, _ = run(t, script(), &fakeLean{}, opts(&fakeVerifier{err: errors.New("bwrap missing")}), Hooks{}, "x")
	if s := res.Statements[0]; s.Status != StatusDisproved || !strings.Contains(s.Error, "bwrap missing") {
		t.Errorf("stmt = %+v", s)
	}
}

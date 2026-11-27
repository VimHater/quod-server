package pipeline

import (
	"strings"
	"testing"
)

// assembledOK accepts what assemble produces from "good" pieces: have-steps
// whose proofs and the main proof are all "good".
func assembledOK(body string) bool {
	if !strings.HasPrefix(body, "have ") {
		return false
	}
	for _, l := range strings.Split(body, "\n") {
		l = strings.TrimSpace(l)
		if l != "" && l != "good" && !(strings.HasPrefix(l, "have ") && strings.HasSuffix(l, ":= by")) {
			return false
		}
	}
	return true
}

func TestParseOutline(t *testing.T) {
	ol, err := parseOutline("  -- plan\n  have step1 : ∀ n ≥ 1,\n      0 < n := by sorry\n  have h₂ : True := by\n    sorry\n  intro x\n  exact step1 x")
	if err != nil {
		t.Fatal(err)
	}
	if len(ol.Steps) != 2 || ol.Steps[0] != (planStep{"step1", "∀ n ≥ 1, 0 < n"}) || ol.Steps[1] != (planStep{"h₂", "True"}) {
		t.Errorf("steps = %+v", ol.Steps)
	}
	if ol.Main != "intro x\nexact step1 x" {
		t.Errorf("main = %q", ol.Main)
	}
	for _, tc := range []struct{ body, want string }{
		{"intro x\nexact foo", "no steps"},
		{"have step1 (n : ℕ) : 0 < n + 1 := by sorry\nsimp", "no binders"},
		{"have step1 : True := by sorry\nhave step2 : True := by\n  simp\n  sorry\ntrivial", "sorry appears after"},
		{"have a : True := by sorry\nhave a : True := by sorry\ntrivial", "Two steps"},
		{"have a : True := by sorry", "no proof after"},
	} {
		if _, err := parseOutline(tc.body); err == nil || !strings.Contains(err.Error(), tc.want) {
			t.Errorf("parseOutline(%q) err = %v, want %q", tc.body, err, tc.want)
		}
	}
}

func TestStepSigAndAssemble(t *testing.T) {
	steps := []planStep{{"s1", "0 < a"}, {"s2", "a ≠ 0"}}
	if got := stepSig("(a : ℤ) (h : 1 < a)", steps[:1], "a ≠ 0"); got != "(a : ℤ) (h : 1 < a) (s1 : 0 < a) : a ≠ 0" {
		t.Errorf("stepSig = %q", got)
	}
	if got := stepSig("", nil, "True"); got != ": True" {
		t.Errorf("stepSig no binders = %q", got)
	}
	got := assemble(&outline{Steps: steps, Main: "exact s2"}, []string{"omega", "intro h0\n  omega"})
	want := "have s1 : 0 < a := by\n  omega\nhave s2 : a ≠ 0 := by\n  intro h0\n    omega\nexact s2"
	if got != want {
		t.Errorf("assemble =\n%s\nwant\n%s", got, want)
	}
}

func TestOutlineProvesStepsAndAssembles(t *testing.T) {
	fl := &fakeLLM{
		formal: []string{formal("stmt_1", ": 5 = 5")},
		proofs: []string{proof("wrong")},
		plans: []string{
			proof("have step1 : 1 = 1 := by sorry\nwrong"),                                   // main proof fails
			proof("have step1 : 1 = 1 := by sorry\nhave step2 : 2 = 2 := by sorry\ngood"),    // step2 fails
			proof("have step1 : 1 = 1 := by sorry\nhave step2 : 3 = 3 := by\n  sorry\ngood"), // step1 reused
		},
		steps: map[string][]string{"step1": {proof("good")}, "step2": {proof("wrong"), proof("good")}},
	}
	opts := Options{SkipSplit: true, MaxProofAttempts: 1, NoDisprove: true, PlanAttempts: 3, StepAttempts: 1}
	res, err, events := run(t, fl, &fakeLean{}, opts, Hooks{}, "five is five")
	if err != nil {
		t.Fatal(err)
	}
	s := res.Statements[0]
	if s.Status != StatusProved || !strings.Contains(s.Proof, "have step2 : 3 = 3 := by\n  good") {
		t.Fatalf("status %s, proof:\n%s", s.Status, s.Proof)
	}
	var plans, step1, step2 int
	for _, a := range s.Attempts {
		switch {
		case a.Plan:
			plans++
		case a.Step == "step1":
			step1++
		case a.Step == "step2":
			step2++
		}
	}
	if plans != 3 || step1 != 1 || step2 != 2 {
		t.Errorf("plans %d, step1 %d, step2 %d attempts", plans, step1, step2)
	}
	if fb := s.Attempts[1].Feedback; !s.Attempts[1].Plan || !strings.Contains(fb, "proof after the steps does not compile") {
		t.Errorf("first outline feedback = %q", fb)
	}
	// the third outline was told why step2 failed
	var told bool
	for _, r := range fl.reqs {
		for _, m := range r.Messages {
			if strings.Contains(m.Content, "- step2: no proof found in 1 attempt(s)") && strings.Contains(m.Content, "Proved: step1") {
				told = true
			}
		}
	}
	if !told {
		t.Error("the outline session was not told that step2 failed")
	}
	var reused bool
	for _, e := range events {
		reused = reused || (e.Type == EvStepDone && strings.Contains(e.Message, "step1: unchanged"))
	}
	if !reused {
		t.Error("step1 was not reused")
	}
}

func TestOutlineRejectsRestatingTheTheorem(t *testing.T) {
	fl := &fakeLLM{
		formal: []string{formal("stmt_1", ": 5 = 5")},
		proofs: []string{proof("wrong")},
		plans:  []string{proof("have step1 : 5 = 5 := by sorry\nexact step1")},
	}
	opts := Options{SkipSplit: true, MaxProofAttempts: 1, NoDisprove: true, PlanAttempts: 1}
	res, err, _ := run(t, fl, &fakeLean{}, opts, Hooks{}, "five is five")
	if err != nil {
		t.Fatal(err)
	}
	s := res.Statements[0]
	last := s.Attempts[len(s.Attempts)-1]
	if s.Status != StatusFailed || !last.Plan || !strings.Contains(last.Feedback, "the theorem itself") {
		t.Errorf("status %s, last attempt %+v", s.Status, last)
	}
}

func TestPlanAfterCapsDirectAttempts(t *testing.T) {
	fl := &fakeLLM{
		formal: []string{formal("stmt_1", ": 5 = 5")},
		proofs: []string{proof("w1"), proof("w2"), proof("w3"), proof("w4"), proof("w5"), proof("w6")},
	}
	opts := Options{SkipSplit: true, MaxProofAttempts: 6, NoDisprove: true, PlanAttempts: 1}
	res, err, _ := run(t, fl, &fakeLean{}, opts, Hooks{}, "five is five")
	if err != nil {
		t.Fatal(err)
	}
	s := res.Statements[0]
	if n := proofAttempts(s); n != 3 {
		t.Errorf("direct attempts = %d, want 3 (PlanAfter default)", n)
	}
	if last := s.Attempts[len(s.Attempts)-1]; !last.Plan {
		t.Errorf("the outline stage did not follow: %+v", last)
	}
}

func TestPlanAfterNegativeStartsWithOutline(t *testing.T) {
	fl := &fakeLLM{
		formal: []string{formal("stmt_1", ": 5 = 5")},
		proofs: []string{proof("good")}, // would verify, but must not be asked for
		plans:  []string{proof("have step1 : 1 = 1 := by sorry\ngood")},
		steps:  map[string][]string{"step1": {proof("good")}},
	}
	opts := Options{SkipSplit: true, NoDisprove: true, PlanAttempts: 1, PlanAfter: -1}
	res, err, _ := run(t, fl, &fakeLean{}, opts, Hooks{}, "five is five")
	if err != nil {
		t.Fatal(err)
	}
	s := res.Statements[0]
	if s.Status != StatusProved || proofAttempts(s) != 0 || !s.Attempts[0].Plan {
		t.Errorf("status %s, direct attempts %d, first attempt %+v", s.Status, proofAttempts(s), s.Attempts[0])
	}
	if len(fl.proofs) != 1 {
		t.Error("a direct proof was requested")
	}
}

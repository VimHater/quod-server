package pipeline

import (
	"strings"
	"testing"
)

func TestSimilarity(t *testing.T) {
	a := "nlinarith [sq_nonneg (a - b), sq_nonneg a]"
	if s := similarity(a, a); s != 1 {
		t.Errorf("identical: %v", s)
	}
	if s := similarity(a, "nlinarith [sq_nonneg (a - b), sq_nonneg b]"); s < nearDuplicate {
		t.Errorf("one hint changed should be near-duplicate: %v", s)
	}
	if s := similarity(a, "rcases h with h | h\n· omega\n· simp at h"); s >= 0.5 {
		t.Errorf("different proof too similar: %v", s)
	}
	// comments and spacing do not matter
	if s := similarity("simp  -- first try\nring", "simp\n  ring"); s != 1 {
		t.Errorf("comments/spacing: %v", s)
	}
}

func TestSameKinds(t *testing.T) {
	if !sameKinds([]string{"tactic_failed", "unsolved_goals", "tactic_failed"}, []string{"unsolved_goals", "tactic_failed"}) {
		t.Error("same set should match")
	}
	if sameKinds([]string{"tactic_failed"}, []string{"unknown_identifier"}) || sameKinds(nil, nil) {
		t.Error("different or empty sets matched")
	}
}

func TestMainTacticAndSummary(t *testing.T) {
	bodies := []AttemptRecord{
		{Body: "have h := sq_nonneg (a - b)\nnlinarith [h]", ErrorKinds: []string{"tactic_failed"}},
		{Body: "norm_num\nnlinarith [sq_nonneg a]", ErrorKinds: []string{"tactic_failed"}},
	}
	if got := mainTactic([]string{bodies[0].Body, bodies[1].Body}); got != "nlinarith" {
		t.Errorf("mainTactic = %q", got)
	}
	s := restartSummary(bodies)
	for _, want := range []string{"conversation was restarted", "relied on `nlinarith`", "→  tactic_failed", "complete new tactic proof"} {
		if !strings.Contains(s, want) {
			t.Errorf("summary lacks %q:\n%s", want, s)
		}
	}
	if !strings.Contains(restartSummary([]AttemptRecord{{Body: "exact foo", ErrorKinds: []string{"x"}}}), "substantially different") {
		t.Error("no generic advice without a known tactic")
	}
}

func TestStuckSessionRestartsConversation(t *testing.T) {
	fl := &fakeLLM{
		formal: []string{formal("stmt_1", ": 1 = 1")},
		proofs: []string{
			proof("nlinarith [sq_nonneg (a - b), sq_nonneg a]"),
			proof("nlinarith [sq_nonneg (a - b), sq_nonneg b]"), // near-duplicate, same error: stuck 1
			proof("nlinarith [sq_nonneg (a - b), sq_nonneg c]"), // stuck 2 -> restart
			proof("good"),
		},
	}
	res, err, events := run(t, fl, &fakeLean{}, Options{SkipSplit: true, NoExplain: true, NoDisprove: true}, Hooks{}, "x")
	if err != nil {
		t.Fatal(err)
	}
	if s := res.Statements[0]; s.Status != StatusProved || len(s.Attempts) != 4 || s.Restarts != 1 {
		t.Fatalf("stmt = %+v", s)
	}
	var restarted bool
	for _, e := range events {
		restarted = restarted || e.Type == EvRestarted
	}
	if !restarted {
		t.Fatal("no restart event")
	}
	// The request after the restart carries the summary instead of the old rounds.
	var after []string
	for _, r := range fl.reqs {
		if strings.Contains(r.Messages[0].Content, "write tactic proofs") {
			after = nil
			for _, m := range r.Messages {
				after = append(after, m.Content)
			}
		}
	}
	joined := strings.Join(after, "\n")
	if len(after) != 4 || !strings.Contains(joined, "relied on `nlinarith`") || strings.Contains(joined, "linarith failed") {
		t.Errorf("last prove request after restart (%d messages):\n%s", len(after), joined)
	}
}

func TestSmallFixIsNotStuck(t *testing.T) {
	// Two different failing approaches: no restart.
	fl := &fakeLLM{
		formal: []string{formal("stmt_1", ": 1 = 1")},
		proofs: []string{proof("nlinarith [sq_nonneg a]"), proof("rcases h with h | h\nomega\nsimp at h"), proof("good")},
	}
	_, _, events := run(t, fl, &fakeLean{}, Options{SkipSplit: true, NoExplain: true, NoDisprove: true}, Hooks{}, "x")
	for _, e := range events {
		if e.Type == EvRestarted {
			t.Fatal("restarted although the approaches differ")
		}
	}
}

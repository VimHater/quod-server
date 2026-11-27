package main

import (
	"errors"
	"os"
	"path/filepath"
	"strings"
	"testing"
	"time"

	"mathprover/internal/pipeline"
)

func TestLoadBench(t *testing.T) {
	p := filepath.Join(t.TempDir(), "b.txt")
	os.WriteFile(p, []byte("# comment\n\ntrue | algebra | x = x\nFALSE|number| 1 = 2 | with a bar\n"), 0o600)
	ps, err := loadBench(p)
	if err != nil {
		t.Fatal(err)
	}
	if len(ps) != 2 || !ps[0].ExpectTrue || ps[1].ExpectTrue || ps[1].Category != "number" || ps[1].Text != "1 = 2 | with a bar" || ps[1].ID != 2 {
		t.Errorf("problems = %+v", ps)
	}
	os.WriteFile(p, []byte("maybe | x | y\n"), 0o600)
	if _, err := loadBench(p); err == nil {
		t.Error("bad expected answer accepted")
	}
}

func TestLoadShippedBench(t *testing.T) {
	ps, err := loadBench("../../bench/problems.txt")
	if err != nil || len(ps) != 5 {
		t.Fatalf("shipped bench: %d problems, %v", len(ps), err)
	}
}

func TestClassify(t *testing.T) {
	res := func(st pipeline.Status, attempts ...pipeline.AttemptRecord) *pipeline.Result {
		return &pipeline.Result{Statements: []*pipeline.StatementResult{{Status: st, Attempts: attempts}}, LLMCalls: 4, Duration: 2 * time.Second}
	}
	fail := pipeline.AttemptRecord{ErrorKinds: []string{"unsolved_goals"}}
	claim := pipeline.AttemptRecord{ErrorKinds: []string{"claims_false"}}
	ok := pipeline.AttemptRecord{Verified: true}
	tru, fls := benchProblem{ID: 1, ExpectTrue: true}, benchProblem{ID: 2}
	for _, c := range []struct {
		p        benchProblem
		res      *pipeline.Result
		err      error
		outcome  string
		firstTry bool
	}{
		{tru, res(pipeline.StatusProved, ok), nil, outCorrect, true},
		{tru, res(pipeline.StatusProved, fail, ok), nil, outCorrect, false},
		{fls, res(pipeline.StatusDisproved), nil, outCorrect, true},            // counterexample
		{fls, res(pipeline.StatusDisproved, claim, ok), nil, outCorrect, true}, // FALSE, then disproof
		{fls, res(pipeline.StatusDisproved, fail, ok), nil, outCorrect, false},
		{tru, res(pipeline.StatusDisproved), nil, outFalseAlarm, false},
		{fls, res(pipeline.StatusProved, ok), nil, outUnsound, false},
		{tru, res(pipeline.StatusFailed, fail), nil, outMiss, false},
		{tru, nil, errors.New("boom"), outError, false},
		{tru, res(pipeline.StatusCanceled), errors.New("context canceled"), outError, false},
	} {
		r := classify("m", 1, c.p, c.res, c.err, time.Second)
		if r.Outcome != c.outcome || r.FirstTry != c.firstTry {
			t.Errorf("%+v / %v: outcome=%s firstTry=%v, want %s %v", c.res, c.err, r.Outcome, r.FirstTry, c.outcome, c.firstTry)
		}
	}
	r := classify("m", 1, tru, res(pipeline.StatusProved, fail, ok), nil, time.Second)
	if r.Seconds != 2 || r.LLMCalls != 4 || r.ErrorKinds["unsolved_goals"] != 1 || r.Attempts != 2 {
		t.Errorf("record = %+v", r)
	}

	// per-attempt timings and the time outside the attempts
	slow := pipeline.AttemptRecord{N: 1, ErrorKinds: []string{"timeout"}, LLMTime: 600 * time.Millisecond, LeanTime: 900 * time.Millisecond}
	quick := pipeline.AttemptRecord{N: 2, Verified: true, LLMTime: 200 * time.Millisecond, LeanTime: 100 * time.Millisecond}
	r = classify("m", 1, tru, res(pipeline.StatusProved, slow, quick), nil, time.Second)
	if len(r.AttemptTimes) != 2 || r.AttemptTimes[0].LeanSeconds != 0.9 || !r.AttemptTimes[1].Verified {
		t.Errorf("attempt times = %+v", r.AttemptTimes)
	}
	if d := r.OtherSeconds - 0.2; d > 1e-9 || d < -1e-9 { // 2s total - 1.5s - 0.3s
		t.Errorf("other seconds = %v, want 0.2", r.OtherSeconds)
	}
}

func TestBenchReport(t *testing.T) {
	ps := []benchProblem{{ID: 1, ExpectTrue: true, Category: "algebra", Text: "a"}, {ID: 2, Category: "number", Text: "b"}}
	ms := []modelRef{{Model: "x"}, {Model: "y", Endpoint: "local"}}
	recs := []benchRecord{
		{Model: "x", Run: 1, Problem: 1, Category: "algebra", ExpectTrue: true, Outcome: outCorrect, FirstTry: true, Seconds: 10},
		{Model: "x", Run: 1, Problem: 2, Category: "number", Outcome: outCorrect, Seconds: 20},
		{Model: "y@local", Run: 1, Problem: 1, Category: "algebra", ExpectTrue: true, Outcome: outMiss, Seconds: 30, ErrorKinds: map[string]int{"timeout": 2}},
		{Model: "y@local", Run: 1, Problem: 2, Category: "number", Outcome: outUnsound, Seconds: 5, Signature: ": 1 = 1",
			OtherSeconds: 1.5, AttemptTimes: []benchAttempt{{N: 1, Kinds: []string{"timeout"}, LLMSeconds: 2, LeanSeconds: 1.5}, {N: 1, Disproof: true, Verified: true, LLMSeconds: 0.5}}},
	}
	out := benchReport(ps, ms, 1, recs, time.Minute, false)
	for _, want := range []string{
		"| x | 2/2 (100%) | 1/2 | 0 | 0 | 0 | 0 | 0 | 15.0s |",
		"| y@local | 0/2 (0%) | 0/2 | 1 | 0 | 1 | 0 |",
		"| 1 | true | algebra | a | ✓ 10s | ✗ 30s |",
		"- y@local: timeout 2 (100%)",
		"#2 y@local run 1: **unsound**",
		"## Attempt timings",
		"- #2 y@local run 1: other 1.5s | 1: 2.0 + 1.5 = 3.5s ✗ timeout | ¬1: 0.5 + 0.0 = 0.5s ✓",
		"- #1 x run 1: other 0.0s, no attempts",
	} {
		if !strings.Contains(out, want) {
			t.Errorf("report lacks %q:\n%s", want, out)
		}
	}
}

func TestParseModelRef(t *testing.T) {
	t.Setenv("LLM_ENDPOINT_LOCAL", "http://localhost:20128/v1")
	t.Setenv("LLM_ENDPOINT_LOCAL_KEY", "k")
	m, err := parseModelRef("cx/gpt-6-luna@local")
	if err != nil || m.Model != "cx/gpt-6-luna" || m.URL != "http://localhost:20128/v1" || m.Key != "k" || m.String() != "cx/gpt-6-luna@local" {
		t.Errorf("%+v %v", m, err)
	}
	if m, err := parseModelRef(" cx/gpt-6.1-sol "); err != nil || m.Model != "cx/gpt-6.1-sol" || m.URL != "" {
		t.Errorf("%+v %v", m, err)
	}
	if _, err := parseModelRef("x@nowhere"); err == nil || !strings.Contains(err.Error(), "LLM_ENDPOINT_NOWHERE") {
		t.Errorf("unconfigured endpoint: %v", err)
	}
}

// Package pipeline turns natural-language statements into verified Lean
// proofs: split → formalize → check statement → back-translate → (confirm)
// → prove with compiler feedback → explain. Statements are processed in
// order and each proved statement becomes available to the later ones.
package pipeline

import (
	"context"
	"errors"
	"time"

	"mathprover/internal/lean"
)

// Status of one statement.
type Status string

const (
	StatusPending     Status = "pending"
	StatusFormalizing Status = "formalizing"
	StatusProving     Status = "proving"
	StatusProved      Status = "proved"
	StatusFailed      Status = "failed"               // formalized, but no proof found
	StatusUnformal    Status = "formalization_failed" // no Lean statement accepted
	StatusUnverified  Status = "unverified"           // proof found, but independent verification could not run
	StatusCanceled    Status = "canceled"
	StatusDisproved   Status = "disproved" // the Lean statement is false (counterexample or proof of ¬)
)

// StatementResult is everything known about one statement.
type StatementResult struct {
	Index              int    `json:"index"` // 1-based
	Name               string `json:"name"`  // Lean name, e.g. stmt_1
	Text               string `json:"text"`  // natural language
	Signature          string `json:"signature,omitempty"`
	FormalizationNotes string `json:"formalization_notes,omitempty"`
	BackTranslation    string `json:"back_translation,omitempty"`
	// FaithfulnessIssues are the differences an independent check found
	// between Text and the Lean statement (empty = none found).
	FaithfulnessIssues  []string `json:"faithfulness_issues,omitempty"`
	FaithfulnessChecked bool     `json:"faithfulness_checked,omitempty"`
	Status              Status   `json:"status"`
	// Proof and LeanCode are the verified proof; for a disproved statement
	// they prove its negation (theorem <name>_false), unless Counterexample
	// is set (found by testing, no proof).
	Proof          string `json:"proof,omitempty"`
	LeanCode       string `json:"lean_code,omitempty"`
	Counterexample string `json:"counterexample,omitempty"`
	Axioms         string `json:"axioms,omitempty"`
	Explanation    string `json:"explanation,omitempty"`
	// Verification is the independent re-check verdict (see lean.Verifier).
	Verification *lean.VerifiedItem `json:"verification,omitempty"`
	Attempts     []AttemptRecord    `json:"attempts,omitempty"`
	Restarts     int                `json:"restarts,omitempty"` // proof conversations restarted because stuck
	Error        string             `json:"error,omitempty"`
}

// AttemptRecord is one proof attempt.
type AttemptRecord struct {
	Stage      string        `json:"stage"`   // ladder stage name, or "auto" for automation
	Session    int           `json:"session"` // session number within the statement, 1-based (0 = automation)
	N          int           `json:"n"`       // attempt number within session (automation: tactic index)
	Model      string        `json:"model,omitempty"`
	Effort     string        `json:"effort,omitempty"`
	Disproof   bool          `json:"disproof,omitempty"` // an attempt to prove the negation
	Free       bool          `json:"free,omitempty"`     // an exact repeat, not charged as an attempt
	Plan       bool          `json:"plan,omitempty"`     // a proof outline (A3), Body is the outline
	Step       string        `json:"step,omitempty"`     // proving this step of an outline
	Body       string        `json:"body"`
	Verified   bool          `json:"verified"`
	ErrorKinds []string      `json:"error_kinds,omitempty"`
	Feedback   string        `json:"feedback,omitempty"` // what the model was told
	LLMTime    time.Duration `json:"llm_time"`
	LeanTime   time.Duration `json:"lean_time"`
	CostUSD    float64       `json:"cost_usd"`
	// Token usage of the LLM call (reasoning is part of completion).
	CompletionTokens int `json:"completion_tokens,omitempty"`
	ReasoningTokens  int `json:"reasoning_tokens,omitempty"`
	// ToolCalls the model made since the previous record (tool stages).
	ToolCalls int `json:"tool_calls,omitempty"`
}

// Result of a whole job.
type Result struct {
	Statements []*StatementResult `json:"statements"`
	// LeanFile is a standalone file with every proved statement (and the
	// unproved ones commented out), checkable with `lake env lean`.
	LeanFile string `json:"lean_file"`
	// Verification is the independent re-check of all proved statements.
	Verification *lean.VerifyReport `json:"verification,omitempty"`
	CostUSD      float64            `json:"cost_usd"`
	LLMCalls     int                `json:"llm_calls"`
	Duration     time.Duration      `json:"duration"`
}

// EventType names a progress event.
type EventType string

const (
	EvSplit          EventType = "split"           // Message: count
	EvFormalizing    EventType = "formalizing"     // attempt n
	EvStatementError EventType = "statement_error" // Lean rejected the statement
	EvFormalized     EventType = "formalized"      // signature + back-translation ready
	EvRevising       EventType = "revising"        // user asked for a different formalization
	EvAttempt        EventType = "attempt"         // proof attempt finished (Attempt set)
	EvProved         EventType = "proved"
	EvFailed         EventType = "failed"
	EvExplained      EventType = "explained"
	EvAutomation     EventType = "automation"   // automation tactics tried (Message: outcome)
	EvStage          EventType = "stage"        // proof search moved to a ladder stage
	EvThinking       EventType = "thinking"     // LLM still generating (throttled progress)
	EvVerifying      EventType = "verifying"    // independent re-check started
	EvVerified       EventType = "verified"     // independent re-check finished (Message: summary)
	EvSimplified     EventType = "simplified"   // search tactics in a verified proof resolved
	EvFaithfulness   EventType = "faithfulness" // result of the independent formalization check
	EvDisproving     EventType = "disproving"   // no proof found (or model says FALSE); trying to prove the negation
	EvResuming       EventType = "resuming"     // the model's FALSE claim was not confirmed; proving again
	EvRestarted      EventType = "restarted"    // the model was stuck on one approach; conversation restarted
	EvDisproved      EventType = "disproved"    // Statement set; counterexample or proof of ¬
	EvPlanning       EventType = "planning"     // direct proofs failed; asking for a proof outline
	EvPlanned        EventType = "planned"      // Lean accepted an outline; proving its steps
	EvStepDone       EventType = "step"         // one outline step proved or given up
	EvDone           EventType = "done"
	EvError          EventType = "error"
)

// Event reports progress. Statement is a snapshot copy, safe to keep.
type Event struct {
	Time      time.Time        `json:"time"`
	Type      EventType        `json:"type"`
	Stmt      int              `json:"stmt,omitempty"` // 1-based; 0 = job level
	Message   string           `json:"message,omitempty"`
	Attempt   *AttemptRecord   `json:"attempt,omitempty"`
	Statement *StatementResult `json:"statement,omitempty"`
}

// Proposal is a formalization offered to the user for confirmation.
type Proposal struct {
	Index           int      `json:"index"`
	Text            string   `json:"text"`
	Name            string   `json:"name"`
	Signature       string   `json:"signature"`
	Notes           string   `json:"notes"`
	BackTranslation string   `json:"back_translation"`
	Issues          []string `json:"issues,omitempty"` // from the faithfulness check
}

// Decision is the user's answer to a Proposal. Reject with Correction to
// have it re-formalized; reject without one to skip the statement.
type Decision struct {
	Accept     bool   `json:"accept"`
	Correction string `json:"correction,omitempty"`
}

// ConfirmFunc asks the user to approve a formalization. It may block (e.g.
// waiting for a client); honour ctx.
type ConfirmFunc func(ctx context.Context, p Proposal) (Decision, error)

// Verifier independently re-checks finished proofs (lean.Verifier).
type Verifier interface {
	Verify(ctx context.Context, leanFile string, items []lean.VerifyItem) (*lean.VerifyReport, error)
}

// Checker runs Lean during a job; tests use fakes.
type Checker interface {
	CheckStatement(ctx context.Context, base *lean.Snapshot, s lean.Statement) (*lean.StatementCheck, error)
	CheckProof(ctx context.Context, base *lean.Snapshot, s lean.Statement, body string) (*lean.Outcome, error)
	// ExploreProof is CheckProof that allows `sorry` placeholders and
	// reports their goals (never verified); used by the check_proof tool.
	ExploreProof(ctx context.Context, base *lean.Snapshot, s lean.Statement, body string) (*lean.Outcome, error)
	// Query runs a read-only command (lookups for tools) on base.
	Query(ctx context.Context, base *lean.Snapshot, code string, timeout time.Duration) (*lean.Result, error)
}

// CheckerSource hands out a Checker for one job; release ends it.
type CheckerSource interface {
	JobChecker(ctx context.Context) (c Checker, release func(), err error)
}

// CounterexampleFinder is optionally implemented by a Checker: it tests a
// statement for a counterexample (e.g. with Lean's `plausible`) and returns
// "" when it finds none.
type CounterexampleFinder interface {
	FindCounterexample(ctx context.Context, base *lean.Snapshot, s lean.Statement) (string, error)
}

// Suggester proposes existing declarations for identifiers Lean did not
// know; the text is appended to the feedback the model gets. It returns ""
// when it has nothing useful (or is not ready yet). Lookups (e.g. #check)
// go through the job's own Checker, never a separate worker.
type Suggester interface {
	Suggest(ctx context.Context, c Checker, unknown []string) string
}

// PoolSource gives every job its own lease on fresh pool workers, which
// are discarded when the job ends (see lean.Lease). This is what isolates
// jobs from each other.
type PoolSource struct{ Pool *lean.Pool }

func (s PoolSource) JobChecker(context.Context) (Checker, func(), error) {
	l := s.Pool.Lease()
	return LeaseChecker{Lease: l}, l.Close, nil
}

// StaticSource returns the same Checker for every job (tests, trusted use).
type StaticSource struct{ C Checker }

func (s StaticSource) JobChecker(context.Context) (Checker, func(), error) {
	return s.C, func() {}, nil
}

// LeaseChecker runs checks on a job's leased worker.
type LeaseChecker struct{ Lease *lean.Lease }

func (c LeaseChecker) CheckStatement(ctx context.Context, base *lean.Snapshot, s lean.Statement) (*lean.StatementCheck, error) {
	return withRetry(ctx, c.Lease, func(r *lean.REPL) (*lean.StatementCheck, error) {
		return lean.CheckStatement(ctx, r, base, s)
	})
}

func (c LeaseChecker) CheckProof(ctx context.Context, base *lean.Snapshot, s lean.Statement, body string) (*lean.Outcome, error) {
	return withRetry(ctx, c.Lease, func(r *lean.REPL) (*lean.Outcome, error) {
		return lean.CheckProof(ctx, r, base, s, body)
	})
}

func (c LeaseChecker) ExploreProof(ctx context.Context, base *lean.Snapshot, s lean.Statement, body string) (*lean.Outcome, error) {
	return withRetry(ctx, c.Lease, func(r *lean.REPL) (*lean.Outcome, error) {
		return lean.ExploreProof(ctx, r, base, s, body)
	})
}

func (c LeaseChecker) FindCounterexample(ctx context.Context, base *lean.Snapshot, s lean.Statement) (string, error) {
	return withRetry(ctx, c.Lease, func(r *lean.REPL) (string, error) {
		return lean.FindCounterexample(ctx, r, base, s)
	})
}

func (c LeaseChecker) Query(ctx context.Context, base *lean.Snapshot, code string, timeout time.Duration) (*lean.Result, error) {
	return withRetry(ctx, c.Lease, func(r *lean.REPL) (*lean.Result, error) {
		return r.Exec(ctx, base, code, lean.ExecOptions{Timeout: timeout})
	})
}

// withRetry runs fn once more on a fresh worker if the current one died
// before or while replaying (e.g. killed by another session's timeout).
func withRetry[T any](ctx context.Context, l *lean.Lease, fn func(*lean.REPL) (T, error)) (T, error) {
	var zero T
	for attempt := 0; ; attempt++ {
		r, err := l.REPL(ctx)
		if err != nil {
			return zero, err
		}
		out, err := fn(r)
		if err != nil && errors.Is(err, lean.ErrDead) && attempt == 0 && ctx.Err() == nil {
			continue
		}
		return out, err
	}
}

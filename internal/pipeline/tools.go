package pipeline

import (
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"regexp"
	"strings"
	"time"

	"mathprover/internal/lean"
	"mathprover/internal/llm"
)

// Lean-backed tools for tool-using stages. Every argument is validated
// before it is turned into Lean source: no newlines (so no new commands),
// bounded length, and goal statements pass the forbidden-syntax filter. All
// commands run in the job's sandboxed worker, on the statement's base
// environment (earlier proved statements are visible, nothing persists).

const (
	toolTimeout     = 30 * time.Second
	toolResultLimit = 3500 // characters returned to the model per call
)

var toolSpecs = []llm.Tool{
	tool("search_lemmas", "Search Mathlib theorem names. Returns up to `limit` theorems whose full name contains every space-separated fragment (case-insensitive), with their statements. Example query: \"nat pow mod\".",
		`{"type":"object","properties":{"query":{"type":"string","description":"space-separated name fragments"},"limit":{"type":"integer","minimum":1,"maximum":40}},"required":["query"]}`),
	tool("check_name", "Show the exact statement of a constant (#check). Use it to confirm a lemma exists before relying on it.",
		`{"type":"object","properties":{"name":{"type":"string","description":"fully qualified name, e.g. Nat.pow_mod"}},"required":["name"]}`),
	tool("find_lemma", "Run Lean's library search (exact?) on a goal and return a term that closes it, if one exists. State the goal as Lean binders and a proposition, e.g. \"(a b : ℕ) (h : a ≤ b) : a ^ 2 ≤ b ^ 2\".",
		`{"type":"object","properties":{"goal":{"type":"string"}},"required":["goal"]}`),
	tool("check_proof", "Compile a candidate tactic script for the theorem being proved. Returns Lean's errors with the goals at each failure, or success; a successful check (without sorry) finishes the task. You may put `sorry` for unfinished parts: the result then lists the open goal at each sorry.",
		`{"type":"object","properties":{"tactics":{"type":"string","description":"the tactic script after := by"}},"required":["tactics"]}`),
}

func tool(name, desc, schema string) llm.Tool {
	return llm.Tool{Type: "function", Function: llm.ToolFunction{Name: name, Description: desc, Parameters: json.RawMessage(schema)}}
}

var reConstName = regexp.MustCompile(`^[^\s()\[\]{},:;"#@` + "`" + `]+$`)

// leanTools runs tool calls for one session attempt and keeps the attempt
// records of check_proof calls.
type leanTools struct {
	j      *job
	sr     *StatementResult
	stmt   lean.Statement
	base   *lean.Snapshot
	failed *failedSet
	// rec records a check_proof: Lean's outcome (nil for a repeat) and
	// the feedback the model got.
	rec   func(body string, o *lean.Outcome, leanTime time.Duration, repeated, feedback string)
	calls int
	win   *lean.Outcome
}

func (t *leanTools) Tools() []llm.Tool { return toolSpecs }

func (t *leanTools) Run(ctx context.Context, call llm.ToolCall) (string, bool) {
	t.calls++
	var args map[string]any
	if err := json.Unmarshal([]byte(call.Function.Arguments), &args); err != nil {
		return "error: arguments must be a JSON object: " + err.Error(), false
	}
	str := func(k string) string { s, _ := args[k].(string); return strings.TrimSpace(s) }
	switch call.Function.Name {
	case "search_lemmas":
		q := str("query")
		if q == "" || len(q) > 200 || strings.ContainsAny(q, "\n\r") {
			return "error: query must be a non-empty single line (max 200 chars)", false
		}
		limit := 15
		if f, ok := args["limit"].(float64); ok && f >= 1 {
			limit = min(int(f), 40)
		}
		return t.query(ctx, fmt.Sprintf("#harness_search %s %d", leanString(q), limit)), false
	case "check_name":
		n := strings.TrimPrefix(str("name"), "@")
		if !reConstName.MatchString(n) || len(n) > 200 {
			return "error: give a single constant name such as Nat.pow_mod", false
		}
		return t.query(ctx, "#check @"+n), false
	case "find_lemma":
		goal := str("goal")
		if goal == "" || strings.ContainsAny(goal, "\n\r") || len(goal) > 1000 {
			return "error: goal must be a single line of the form \"<binders> : <prop>\"", false
		}
		if !strings.Contains(goal, ":") {
			goal = ": " + goal
		}
		if err := (lean.Statement{Name: "quod_goal", Signature: goal}).Validate(); err != nil {
			return "error: " + err.Error(), false
		}
		return t.query(ctx, "example "+goal+" := by\n  exact?"), false
	case "check_proof":
		body := str("tactics")
		if body == "" {
			return "error: tactics is empty", false
		}
		return t.checkProof(ctx, body)
	}
	return fmt.Sprintf("error: unknown tool %q", call.Function.Name), false
}

func (t *leanTools) checkProof(ctx context.Context, body string) (string, bool) {
	norm := lean.NormalizeBody(body)
	if fb, seen := t.failed.get(norm); seen {
		t.rec(body, nil, 0, fb, "")
		return "This exact proof already failed with:\n" + fb, false
	}
	t0 := time.Now()
	o, err := t.j.p.check.ExploreProof(ctx, t.base, t.stmt, body)
	if err != nil {
		return "error: Lean check failed to run: " + err.Error(), false
	}
	leanTime := time.Since(t0)
	if o.Verdict.Verified {
		t.rec(body, o, leanTime, "", "")
		t.win = o
		return "Verified.", true
	}
	fb := t.j.feedback(ctx, o)
	if o.Result != nil && len(o.Result.Sorries) > 0 {
		var b strings.Builder
		b.WriteString("\n\nOpen goals at your sorry placeholders:")
		for _, sr := range o.Result.Sorries {
			fmt.Fprintf(&b, "\n- proof line %d:\n%s", sr.Pos.Line-o.Attempt.BodyLine+1, indentText(sr.Goal, "    "))
		}
		fb += b.String()
	}
	t.rec(body, o, leanTime, "", fb)
	t.failed.add(norm, fb)
	return fb, false
}

// query runs a read-only Lean command and formats its messages.
func (t *leanTools) query(ctx context.Context, code string) string {
	res, err := t.j.p.check.Query(ctx, t.base, code, toolTimeout)
	if errors.Is(err, lean.ErrTimeout) {
		return "error: Lean timed out on this query (try something more specific)"
	}
	if err != nil {
		return "error: " + err.Error()
	}
	var b strings.Builder
	for _, m := range res.Messages {
		if m.Severity == "warning" && strings.Contains(m.Data, "declaration uses") {
			continue
		}
		if m.Severity != "info" {
			b.WriteString(m.Severity + ": ")
		}
		b.WriteString(strings.TrimSpace(m.Data) + "\n")
	}
	out := strings.TrimSpace(b.String())
	if out == "" {
		out = "(no output)"
	}
	if r := []rune(out); len(r) > toolResultLimit {
		out = string(r[:toolResultLimit]) + "\n… (truncated)"
	}
	return out
}

// leanString quotes s as a Lean string literal.
func leanString(s string) string {
	s = strings.ReplaceAll(s, `\`, `\\`)
	s = strings.ReplaceAll(s, `"`, `\"`)
	return `"` + s + `"`
}

func indentText(s, p string) string {
	ls := strings.Split(strings.TrimRight(s, "\n"), "\n")
	for i := range ls {
		ls[i] = p + ls[i]
	}
	return strings.Join(ls, "\n")
}

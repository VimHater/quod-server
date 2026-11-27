package lean

import (
	"context"
	"errors"
	"strings"
	"time"
)

// NegatedSignature turns a theorem signature "<binders> : <prop>" into the
// signature of its negation, ": ¬ (∀ <binders>, <prop>)". ok is false if
// the signature has no top-level colon.
func NegatedSignature(sig string) (string, bool) {
	binders, prop, ok := splitSignature(sig)
	if !ok || prop == "" {
		return "", false
	}
	if binders == "" {
		return ": ¬ (" + prop + ")", true
	}
	return ": ¬ (∀ " + binders + ", " + prop + ")", true
}

// SplitSignature splits "<binders> : <prop>" at the first colon outside any
// brackets.
func SplitSignature(sig string) (binders, prop string, ok bool) { return splitSignature(sig) }

// splitSignature splits at the first colon outside any brackets.
func splitSignature(sig string) (binders, prop string, ok bool) {
	depth := 0
	rs := []rune(sig)
	for i, r := range rs {
		switch r {
		case '(', '[', '{', '⦃', '⟨':
			depth++
		case ')', ']', '}', '⦄', '⟩':
			depth--
		case ':':
			if depth == 0 && (i+1 >= len(rs) || rs[i+1] != '=') {
				return strings.TrimSpace(string(rs[:i])), strings.TrimSpace(string(rs[i+1:])), true
			}
		}
	}
	return "", "", false
}

const (
	counterexampleTag = "Found a counter-example!"
	plausibleTimeout  = 45 * time.Second
)

// FindCounterexample runs Mathlib's `plausible` (random testing) on the
// statement. It returns the counterexample Lean found, or "" when there is
// none, the types cannot be sampled (e.g. ℝ) or the search timed out.
// A counterexample is evaluated by Lean, so the statement as formalized is
// false; it does not say whether the formalization was faithful.
func FindCounterexample(ctx context.Context, r *REPL, base *Snapshot, s Statement) (string, error) {
	if err := s.Validate(); err != nil {
		return "", err
	}
	probe := Statement{Name: s.Name + "_plausible", Signature: s.Signature}
	code := probe.header() + bodyIndent + "plausible\n"
	res, err := r.Exec(ctx, base, code, ExecOptions{Timeout: plausibleTimeout})
	if errors.Is(err, ErrTimeout) {
		return "", nil
	}
	if err != nil {
		return "", err
	}
	for _, m := range res.Messages {
		if m.Severity == "error" {
			if ce := parseCounterexample(m.Data); ce != "" {
				return ce, nil
			}
		}
	}
	return "", nil
}

// parseCounterexample keeps the variable assignments and the failing part
// of plausible's report.
func parseCounterexample(data string) string {
	_, rest, ok := strings.Cut(data, counterexampleTag)
	if !ok {
		return ""
	}
	if i := strings.Index(rest, "-------------------"); i >= 0 {
		rest = rest[:i]
	}
	var lines []string
	for _, l := range strings.Split(rest, "\n") {
		l = strings.TrimSpace(l)
		if l == "" || strings.HasPrefix(l, "(") && strings.HasSuffix(l, "shrinks)") {
			continue
		}
		lines = append(lines, l)
	}
	return strings.Join(lines, "\n")
}

package lean

import (
	"regexp"
	"sort"
	"strings"
	"unicode/utf8"
)

// Search tactics that close a goal by finding a term and report it as
// "Try this: ...". A proof that still contains them re-runs the search on
// every check (slow, and brittle across Mathlib versions).
var reSearchTactic = regexp.MustCompile(`^(exact\?|apply\?|simp_all\?!?|simp\?!?|rw\?|aesop\?|hint)`)

// HasSearchTactic reports whether body uses a search tactic.
func HasSearchTactic(body string) bool {
	for _, l := range strings.Split(body, "\n") {
		for i := range l {
			if (i == 0 || !isIdentByte(l[i-1])) && reSearchTactic.MatchString(l[i:]) {
				return true
			}
		}
	}
	return false
}

func isIdentByte(c byte) bool {
	return c == '_' || c == '.' || c == '\'' || c >= '0' && c <= '9' || c >= 'a' && c <= 'z' || c >= 'A' && c <= 'Z'
}

// ApplyTryThis rewrites the proof body of a checked attempt, replacing each
// search tactic that Lean answered with "Try this: <tactic>" by that
// tactic. It returns the new body and the number of replacements (0 = body
// unchanged). The caller must re-check the new body.
func ApplyTryThis(o *Outcome) (string, int) {
	if o == nil || o.Attempt == nil || o.Result == nil {
		return "", 0
	}
	a := o.Attempt
	lines := strings.Split(a.Body, "\n")
	type rep struct {
		line, col, end int // rune columns in the body line
		text           string
	}
	var reps []rep
	seen := map[[2]int]bool{}
	for _, m := range o.Result.Messages {
		if m.Severity != "info" {
			continue
		}
		sugg, ok := tryThisText(m.Data)
		if !ok {
			continue
		}
		idx := m.Pos.Line - a.BodyLine
		if idx < 0 || idx >= len(lines) || seen[[2]int{idx, m.Pos.Column}] {
			continue
		}
		lr := []rune(lines[idx])
		col := m.Pos.Column - len(bodyIndent)
		if lines[idx] == "" || col < 0 || col >= len(lr) {
			continue
		}
		rest := string(lr[col:])
		loc := reSearchTactic.FindStringIndex(rest)
		if loc == nil {
			continue
		}
		end := col + utf8.RuneCountInString(rest[:loc[1]])
		// For tactics with arguments (simp? [...] at h) Lean's range covers
		// the whole tactic.
		if m.EndPos != nil && m.EndPos.Line == m.Pos.Line {
			if e := m.EndPos.Column - len(bodyIndent); e > end && e <= len(lr) {
				end = e
			}
		}
		seen[[2]int{idx, m.Pos.Column}] = true
		reps = append(reps, rep{idx, col, end, sugg})
	}
	if len(reps) == 0 {
		return a.Body, 0
	}
	// Right to left, so earlier columns stay valid.
	sort.Slice(reps, func(i, j int) bool {
		if reps[i].line != reps[j].line {
			return reps[i].line < reps[j].line
		}
		return reps[i].col > reps[j].col
	})
	for _, r := range reps {
		lr := []rune(lines[r.line])
		text := r.text
		if strings.Contains(text, "\n") {
			// Continuation lines must be indented past the tactic's column.
			text = strings.ReplaceAll(text, "\n", "\n"+strings.Repeat(" ", r.col+4))
		}
		lines[r.line] = string(lr[:r.col]) + text + string(lr[r.end:])
	}
	return strings.Join(lines, "\n"), len(reps)
}

// tryThisText extracts the suggested tactic from a "Try this:" message.
// Messages offering several alternatives ("Try these:") are skipped.
func tryThisText(data string) (string, bool) {
	rest, ok := strings.CutPrefix(strings.TrimSpace(data), "Try this:")
	if !ok {
		return "", false
	}
	rest = strings.TrimSpace(rest)
	rest = strings.TrimSpace(strings.TrimPrefix(rest, "[apply]"))
	if rest == "" {
		return "", false
	}
	ls := strings.Split(rest, "\n")
	for i := range ls {
		ls[i] = strings.TrimSpace(ls[i])
	}
	return strings.Join(ls, "\n"), true
}

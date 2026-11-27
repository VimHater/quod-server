package lean

import (
	"strings"
	"testing"
)

// info builds a Lean info message at a body position (0-based body line,
// rune column within the body line).
func info(a *Attempt, bodyLine, col int, data string) Message {
	return Message{Severity: "info", Pos: Pos{Line: a.BodyLine + bodyLine, Column: col + len(bodyIndent)}, Data: data}
}

func TestHasSearchTactic(t *testing.T) {
	for body, want := range map[string]bool{
		"exact?":                           true,
		"have h : x = x := by exact?\nrfl": true,
		"  simp? [foo] at h":               true,
		"apply? using h":                   true,
		"exact h\nsimp":                    false,
		"exact my_exact?_lemma":            false, // part of an identifier
		"aesop":                            false,
	} {
		if got := HasSearchTactic(body); got != want {
			t.Errorf("HasSearchTactic(%q) = %v, want %v", body, got, want)
		}
	}
}

func TestApplyTryThis(t *testing.T) {
	s := Statement{Name: "t", Signature: "(A B : P) : P"}
	body := "have hAB : A ≠ B := by exact?\nhave h2 := by simp? [foo] at h\nexact?"
	a := NewAttempt(s, body)
	l0 := []rune(strings.Split(body, "\n")[0])
	col0 := strings.Index(string(l0), "exact?") // ASCII before it except ≠
	col0 = len([]rune(string(l0)[:col0]))
	l1 := strings.Split(body, "\n")[1]
	col1 := strings.Index(l1, "simp?")
	end1 := len(l1)

	simpMsg := info(a, 1, col1, "Try this: simp only [foo, bar] at h")
	simpMsg.EndPos = &Pos{Line: simpMsg.Pos.Line, Column: end1 + len(bodyIndent)}
	o := &Outcome{Attempt: a, Result: &Result{Messages: []Message{
		info(a, 0, col0, "Try this: exact fun h => hABC (by simp [h])"),
		simpMsg,
		info(a, 2, 0, "Try this:\n  [apply] exact EuclideanGeometry.angle_add_angle_add_angle_eq_pi C\n    hBA hCA"),
		{Severity: "info", Pos: Pos{Line: a.AxiomsLine}, Data: "HARNESS_AXIOMS_OK t: []"},
	}}}

	got, n := ApplyTryThis(o)
	want := "have hAB : A ≠ B := by exact fun h => hABC (by simp [h])\n" +
		"have h2 := by simp only [foo, bar] at h\n" +
		"exact EuclideanGeometry.angle_add_angle_add_angle_eq_pi C\n    hBA hCA"
	if n != 3 || got != want {
		t.Errorf("ApplyTryThis = %d replacements:\n%s\nwant:\n%s", n, got, want)
	}
}

func TestApplyTryThisIgnoresUnrelatedMessages(t *testing.T) {
	a := NewAttempt(Statement{Name: "t", Signature: ": True"}, "exact?\ntrivial")
	o := &Outcome{Attempt: a, Result: &Result{Messages: []Message{
		info(a, 1, 0, "Try this: exact True.intro"), // points at `trivial`, not a search tactic
		info(a, 0, 0, "Try these:\n- exact a\n- exact b"),
		{Severity: "warning", Pos: Pos{Line: a.BodyLine}, Data: "Try this: exact x"},
	}}}
	if got, n := ApplyTryThis(o); n != 0 || got != a.Body {
		t.Errorf("unexpected rewrite (%d): %q", n, got)
	}
}

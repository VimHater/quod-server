package pipeline

import (
	"fmt"
	"regexp"
	"sort"
	"strings"
)

// Anti-repetition (A4). A model that keeps resubmitting the same failing
// idea wastes attempts, and its own earlier replies in the conversation
// anchor it. A proof session therefore
//   - does not charge an attempt for an exact repeat (at most freeRepeats),
//   - counts "stuck" attempts: exact repeats, or attempts that are nearly
//     the same as the previous failed one AND fail with the same error kinds
//     (a small edit that changes the errors is progress, not stuck),
//   - after stuckLimit stuck attempts restarts the conversation with a
//     summary of what failed and a concrete different direction
//     (at most maxRestarts times per session).
const (
	freeRepeats   = 2
	stuckLimit    = 2
	maxRestarts   = 2
	nearDuplicate = 0.8 // token similarity to count as "the same approach"
)

var reToken = regexp.MustCompile(`[A-Za-z_][A-Za-z0-9_'.!?]*|\d+|\S`)

func proofTokens(body string) []string {
	var out []string
	for _, l := range strings.Split(body, "\n") {
		if i := strings.Index(l, "--"); i >= 0 {
			l = l[:i]
		}
		out = append(out, reToken.FindAllString(l, -1)...)
	}
	return out
}

// similarity of two proof bodies in [0, 1]: 1 - token edit distance / longer length.
func similarity(a, b string) float64 {
	ta, tb := proofTokens(a), proofTokens(b)
	n := max(len(ta), len(tb))
	if n == 0 {
		return 1
	}
	prev := make([]int, len(tb)+1)
	cur := make([]int, len(tb)+1)
	for j := range prev {
		prev[j] = j
	}
	for i := 1; i <= len(ta); i++ {
		cur[0] = i
		for j := 1; j <= len(tb); j++ {
			cost := 1
			if ta[i-1] == tb[j-1] {
				cost = 0
			}
			cur[j] = min(prev[j]+1, cur[j-1]+1, prev[j-1]+cost)
		}
		prev, cur = cur, prev
	}
	return 1 - float64(prev[len(tb)])/float64(n)
}

func sameKinds(a, b []string) bool {
	if len(a) == 0 || len(b) == 0 {
		return false
	}
	set := func(ks []string) string {
		m := map[string]bool{}
		for _, k := range ks {
			m[k] = true
		}
		var s []string
		for k := range m {
			s = append(s, k)
		}
		sort.Strings(s)
		return strings.Join(s, ",")
	}
	return set(a) == set(b)
}

// Heavy tactics a failing approach usually hinges on, with a different
// direction to suggest when the model is stuck on one of them.
var tacticAlternatives = []struct{ tactic, instead string }{
	{"nlinarith", "a proof that does not hinge on nlinarith: rewrite the goal into a sum of squares or a known inequality and apply an existing Mathlib lemma, or split into cases first"},
	{"linarith", "establish the missing nonlinear facts as separate `have` steps (products, squares, divisions) before calling linarith, or avoid it altogether"},
	{"polyrith", "an explicit `ring`/`linear_combination` argument with the coefficients written out"},
	{"positivity", "proving the sign of each factor separately (mul_pos, sq_nonneg, div_pos) and combining them"},
	{"field_simp", "clearing denominators by hand (div_le_iff₀, le_div_iff₀, mul_comm) instead of field_simp"},
	{"interval_cases", "a direct argument without exhaustive case analysis, or cases on far fewer values"},
	{"simp_all", "explicit rewriting with rw and named lemmas instead of simp_all"},
	{"norm_num", "explicit rewriting with rw and named lemmas, or omega/decide for the arithmetic"},
	{"simp", "explicit rewriting with rw and named lemmas instead of simp"},
	{"omega", "first reducing the nonlinear parts (e.g. work modulo n with Nat.pow_mod, Nat.mul_mod) so that only linear arithmetic is left for omega"},
	{"exact?", "naming the lemma directly (see the suggestions in earlier feedback) or proving the step by automation"},
	{"apply?", "naming the lemma directly or proving the step by automation"},
	{"aesop", "a manual proof with intro/constructor/cases and explicit lemmas"},
	{"decide", "a proof that does not evaluate the statement by computation"},
}

// mainTactic is the heavy tactic used most across the bodies ("" if none).
func mainTactic(bodies []string) string {
	count := map[string]int{}
	for _, b := range bodies {
		seen := map[string]bool{}
		for _, t := range proofTokens(b) {
			seen[t] = true
		}
		for _, ta := range tacticAlternatives {
			if seen[ta.tactic] {
				count[ta.tactic]++
			}
		}
	}
	best, bestN := "", 0
	for _, ta := range tacticAlternatives { // list order breaks ties
		if count[ta.tactic] > bestN {
			best, bestN = ta.tactic, count[ta.tactic]
		}
	}
	return best
}

// restartSummary tells the model, in a fresh conversation, what has been
// tried and failed and which direction to take instead.
func restartSummary(failed []AttemptRecord) string {
	var b strings.Builder
	b.WriteString("Your recent attempts kept repeating the same approach and failing the same way, so the conversation was restarted. Approaches already tried, all rejected by Lean:\n")
	var bodies []string
	from := max(0, len(failed)-4)
	for _, a := range failed[from:] {
		bodies = append(bodies, a.Body)
		lines := strings.Split(strings.TrimSpace(a.Body), "\n")
		head := strings.Join(lines[:min(3, len(lines))], " / ")
		if r := []rune(head); len(r) > 160 {
			head = string(r[:160]) + "…"
		}
		fmt.Fprintf(&b, "- %s  →  %s\n", head, strings.Join(a.ErrorKinds, ", "))
	}
	if t := mainTactic(bodies); t != "" {
		for _, ta := range tacticAlternatives {
			if ta.tactic == t {
				fmt.Fprintf(&b, "They all relied on `%s`. Do not make it the main step again; try %s.\n", t, ta.instead)
			}
		}
	} else {
		b.WriteString("Try a substantially different proof strategy.\n")
	}
	b.WriteString("Write a complete new tactic proof in one lean code block.")
	return b.String()
}

package lean

import "testing"

func TestNegatedSignature(t *testing.T) {
	for sig, want := range map[string]string{
		"(n : ℕ) (h : 0 < n) : n ^ 2 ≥ 2 * n":          ": ¬ (∀ (n : ℕ) (h : 0 < n), n ^ 2 ≥ 2 * n)",
		": Set.Infinite {p : ℕ | Nat.Prime p}":         ": ¬ (Set.Infinite {p : ℕ | Nat.Prime p})",
		"{a b : ℝ} [Fact (0 < a)] (h : a ≤ b) : a ≤ b": ": ¬ (∀ {a b : ℝ} [Fact (0 < a)] (h : a ≤ b), a ≤ b)",
		"(f : ℕ → ℕ) (h : ∀ x : ℕ, f x = x) : f 0 = 0": ": ¬ (∀ (f : ℕ → ℕ) (h : ∀ x : ℕ, f x = x), f 0 = 0)",
	} {
		got, ok := NegatedSignature(sig)
		if !ok || got != want {
			t.Errorf("NegatedSignature(%q) = %q, %v; want %q", sig, got, ok, want)
		}
	}
	if _, ok := NegatedSignature("(n : ℕ) n = n"); ok {
		t.Error("signature without a top-level colon accepted")
	}
}

func TestParseCounterexample(t *testing.T) {
	data := "\n===================\nFound a counter-example!\na := -1\nb := 1\nguard: -1 < 1\nissue: 1 < 1 does not hold\n(0 shrinks)\n-------------------\n"
	want := "a := -1\nb := 1\nguard: -1 < 1\nissue: 1 < 1 does not hold"
	if got := parseCounterexample(data); got != want {
		t.Errorf("parseCounterexample = %q, want %q", got, want)
	}
	if got := parseCounterexample("Unable to find a counter-example"); got != "" {
		t.Errorf("no counterexample: got %q", got)
	}
}

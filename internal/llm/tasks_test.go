package llm

import (
	"context"
	"errors"
	"strings"
	"testing"
)

// fakeChat returns scripted replies and records requests.
type fakeChat struct {
	replies []string
	reqs    []Request
	cost    float64
}

func (f *fakeChat) Chat(_ context.Context, r Request) (*Response, error) {
	f.reqs = append(f.reqs, r)
	if len(f.replies) == 0 {
		return nil, errors.New("no scripted reply")
	}
	c := f.replies[0]
	f.replies = f.replies[1:]
	return &Response{Content: c, CostUSD: f.cost}, nil
}

func TestExtractProofBody(t *testing.T) {
	cases := map[string]string{
		"Here:\n```lean\nintro x\nsimp\n```": "intro x\nsimp",
		"```lean4\npositivity\n```":          "positivity",
		"```\nomega\n```":                    "omega",
		"omega":                              "omega",
		"```lean\ntheorem t (x : ℕ) : x = x := by\n  rfl\n```":            "  rfl", // indent kept; lean.NormalizeBody dedents
		"first try\n```lean\nsimp\n```\nbetter:\n```lean\nnlinarith\n```": "nlinarith",
		"```text\nignored\n```\n```lean\nring\n```":                       "ring",
	}
	cases["```lean\n  rcases h with a | b\n  · simp\n    ring\n```"] = "  rcases h with a | b\n  · simp\n    ring"
	for in, want := range cases {
		if got := ExtractProofBody(in); got != want {
			t.Errorf("ExtractProofBody(%q) = %q, want %q", in, got, want)
		}
	}
}

func TestExtractSignature(t *testing.T) {
	cases := map[string]string{
		"```lean\ntheorem stmt_1 (x : ℝ) (h : 0 < x) : 0 < x ^ 2 := by sorry\n```\n- reals":                         "(x : ℝ) (h : 0 < x) : 0 < x ^ 2",
		"```lean\ntheorem stmt_1 : ∀ n : ℕ, n + 0 = n := sorry\n```":                                                ": ∀ n : ℕ, n + 0 = n",
		"```lean\nimport Mathlib\nopen Real\n\ntheorem s {n : ℕ}\n    (h : 1 ≤ n) :\n    n ≠ 0 := by\n  sorry\n```": "{n : ℕ}\n    (h : 1 ≤ n) :\n    n ≠ 0",
		"```lean\nlemma s (a : ℤ) : a = a := by sorry\n```":                                                         "(a : ℤ) : a = a",
	}
	for in, want := range cases {
		got, ok := ExtractSignature(in)
		if !ok || got != want {
			t.Errorf("ExtractSignature(%q) = %q,%v want %q", in, got, ok, want)
		}
	}
	if _, ok := ExtractSignature("```lean\nexample : True := trivial\n```"); ok {
		t.Error("example accepted as theorem")
	}
}

func TestSplitStatements(t *testing.T) {
	f := &fakeChat{replies: []string{`{"statements": ["  a > 0 ", "", "b > 0"]}`}}
	got, err := NewAgent(f, Options{}).SplitStatements(context.Background(), "a>0 and b>0")
	if err != nil || len(got) != 2 || got[0] != "a > 0" {
		t.Fatalf("got %q, %v", got, err)
	}
	if !f.reqs[0].JSON || !strings.Contains(f.reqs[0].Messages[0].Content, "json") {
		t.Error("split must use JSON mode with 'json' in the prompt")
	}
}

func TestFormalizeWithRetry(t *testing.T) {
	f := &fakeChat{replies: []string{"```lean\ntheorem stmt_2 (x : ℝ) : x ^ 2 ≥ 0 := by sorry\n```\nReals assumed."}}
	a := NewAgent(f, Options{LeanVersion: "Lean v4.36.0"})
	out, err := a.Formalize(context.Background(), FormalizeInput{
		Name:      "stmt_2",
		Statement: "squares are nonnegative",
		Context:   []Lemma{{Name: "stmt_1", Signature: ": 1 = 1", Text: "one is one"}},
		Previous:  &FormalizeRetry{Signature: "(x) : x^2 ≥ 0", Problem: "typeclass error"},
	})
	if err != nil || out.Signature != "(x : ℝ) : x ^ 2 ≥ 0" || out.Notes != "Reals assumed." {
		t.Fatalf("out=%+v err=%v", out, err)
	}
	msgs := f.reqs[0].Messages
	if len(msgs) != 4 || !strings.Contains(msgs[0].Content, "Lean v4.36.0") ||
		!strings.Contains(msgs[1].Content, "theorem stmt_1 : 1 = 1") || !strings.Contains(msgs[3].Content, "typeclass error") {
		t.Errorf("messages: %+v", msgs)
	}
}

func TestProofSessionHistory(t *testing.T) {
	f := &fakeChat{replies: []string{"```lean\ntry1\n```", "```lean\ntry2\n```", "```lean\ntry3\n```", "```lean\ntry4\n```"}}
	a := NewAgent(f, Options{MaxFeedbackRounds: 2})
	s := a.NewProofSession(ProveInput{Name: "t", Signature: ": 1 = 1", Context: []Lemma{
		{Name: "used", Signature: ": True", Proved: true},
		{Name: "unproved", Signature: ": False"},
	}})
	ctx := context.Background()
	for i := 1; i <= 4; i++ {
		body, _, err := s.Next(ctx)
		if err != nil || body != "try"+string(rune('0'+i)) {
			t.Fatalf("round %d: %q %v", i, body, err)
		}
		s.Feedback("error " + string(rune('0'+i)))
	}
	if s.Rounds() != 4 {
		t.Errorf("rounds = %d", s.Rounds())
	}
	intro := f.reqs[0].Messages[1].Content
	if !strings.Contains(intro, "theorem used") || strings.Contains(intro, "unproved") {
		t.Errorf("intro should list only proved lemmas:\n%s", intro)
	}
	// 4th request: system, intro, 2 history pairs from rounds 2-3, with round 1 dropped
	last := f.reqs[3].Messages
	all := ""
	for _, m := range last {
		all += m.Role + ":" + m.Content + "\n"
	}
	if strings.Contains(all, "try1") || !strings.Contains(all, "try3") || !strings.Contains(all, "error 3") || !strings.Contains(all, "1 earlier attempt") {
		t.Errorf("history trimming wrong:\n%s", all)
	}
}

func TestBudget(t *testing.T) {
	f := &fakeChat{replies: []string{"a", "b"}, cost: 0.6}
	a := NewAgent(f, Options{BudgetUSD: 0.5})
	if _, err := a.BackTranslate(context.Background(), "t", ": True", nil); err != nil {
		t.Fatal(err)
	}
	if _, err := a.BackTranslate(context.Background(), "t", ": True", nil); !errors.Is(err, ErrBudget) {
		t.Fatalf("err = %v", err)
	}
	if usd, calls := a.Spent(); usd != 0.6 || calls != 1 {
		t.Errorf("spent %g in %d calls", usd, calls)
	}
}

func TestUnmarshalLenient(t *testing.T) {
	var out struct {
		Statements []string `json:"statements"`
	}
	// The split reply that failed in practice: LaTeX with single backslashes.
	in := `{"statements":["For all positive real numbers \(a\) and \(b\), \(\frac{a}{b}+\frac{b}{a}\ge 2\)."]}`
	if err := unmarshalLenient(in, &out); err != nil {
		t.Fatal(err)
	}
	want := `For all positive real numbers \(a\) and \(b\), \(\frac{a}{b}+\frac{b}{a}\ge 2\).`
	if len(out.Statements) != 1 || out.Statements[0] != want {
		t.Errorf("got %q, want %q", out.Statements, want)
	}
	// Valid JSON keeps its escapes (\n stays a newline) and code fences are stripped.
	var v struct{ A string }
	fenced := "```json\n" + `{"A": "x\ny \u00e9"}` + "\n```"
	if err := unmarshalLenient(fenced, &v); err != nil || v.A != "x\ny \u00e9" {
		t.Errorf("valid json: %q, %v", v.A, err)
	}
}

func TestClaimsFalse(t *testing.T) {
	for reply, want := range map[string]bool{
		"FALSE":                               true,
		"FALSE\ncounterexample: n = 1":        true,
		"FALSE. Take x = 1/2.":                true,
		"FALSE: n = 1 fails":                  true,
		"FALSE — x = 1/2":                     true,
		"**FALSE**\nx = 1/2":                  true,
		"```lean\nFALSE\n```":                 true,
		"-- note\nFALSE":                      true,
		"FALSEHOOD":                           false,
		"exact absurd h FALSE_lemma":          false,
		"nlinarith [sq_nonneg (x - 1)]":       false,
		"by_contra h\n-- the claim is FALSE?": false,
	} {
		if got := ClaimsFalse(ExtractProofBody(reply)); got != want {
			t.Errorf("ClaimsFalse(%q) = %v, want %v", reply, got, want)
		}
	}
}

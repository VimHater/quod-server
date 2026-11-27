package llm

import (
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"strings"
	"sync"
)

// ModelSpec selects a model and its settings for one kind of task.
type ModelSpec struct {
	Model     string
	Effort    Effort
	MaxTokens int
}

// Models assigns a model to each task.
type Models struct {
	Split     ModelSpec
	Formalize ModelSpec
	Back      ModelSpec // back-translation
	Judge     ModelSpec // faithfulness check (statement vs formalization)
	Prove     ModelSpec
	Explain   ModelSpec
}

// DefaultModels uses deepseek-flash everywhere (cheap); switch Prove to
// ModelPro for harder problems.
func DefaultModels() Models {
	return Models{
		Split:     ModelSpec{Model: ModelFlash, Effort: EffortNone, MaxTokens: 4096},
		Formalize: ModelSpec{Model: ModelFlash, Effort: EffortHigh},
		Back:      ModelSpec{Model: ModelFlash, Effort: EffortNone, MaxTokens: 1024},
		Judge:     ModelSpec{Model: ModelFlash, Effort: EffortLow},
		Prove:     ModelSpec{Model: ModelFlash, Effort: EffortHigh},
		Explain:   ModelSpec{Model: ModelFlash, Effort: EffortNone, MaxTokens: 2048},
	}
}

// ErrBudget is returned when the spending limit has been reached.
var ErrBudget = errors.New("llm: budget exhausted")

// Options configures an Agent.
type Options struct {
	Models      Models
	LeanVersion string  // shown to the model, e.g. "Lean v4.36.0, Mathlib v4.36.0"
	BudgetUSD   float64 // 0 = unlimited; checked before each call
	// Imports are the Lean modules the checker has loaded, shown to the
	// model so it only uses what is available. Empty = all of Mathlib.
	Imports []string
	// MaxFeedbackRounds bounds how many (proof, feedback) pairs a proof
	// session keeps in context; older rounds are summarized away. Default 3.
	MaxFeedbackRounds int
}

// Agent runs the prover's LLM tasks and tracks total spend. Safe for
// concurrent use.
type Agent struct {
	c    Chatter
	opts Options

	mu    sync.Mutex
	spent float64
	calls int
}

// NewAgent wraps a Chatter (usually *Client).
func NewAgent(c Chatter, opts Options) *Agent {
	if opts.Models == (Models{}) {
		opts.Models = DefaultModels()
	}
	if opts.LeanVersion == "" {
		opts.LeanVersion = "Lean 4 with a recent Mathlib"
	}
	if opts.MaxFeedbackRounds <= 0 {
		opts.MaxFeedbackRounds = 3
	}
	return &Agent{c: c, opts: opts}
}

// Models returns the model assignment.
func (a *Agent) Models() Models { return a.opts.Models }

// Spent returns the estimated USD spent and the number of calls.
func (a *Agent) Spent() (usd float64, calls int) {
	a.mu.Lock()
	defer a.mu.Unlock()
	return a.spent, a.calls
}

func (a *Agent) call(ctx context.Context, spec ModelSpec, asJSON bool, msgs ...Message) (*Response, error) {
	return a.callProgress(ctx, spec, asJSON, nil, msgs...)
}

func (a *Agent) callProgress(ctx context.Context, spec ModelSpec, asJSON bool, onProgress func(Progress), msgs ...Message) (*Response, error) {
	return a.callTools(ctx, spec, asJSON, nil, onProgress, msgs...)
}

func (a *Agent) callTools(ctx context.Context, spec ModelSpec, asJSON bool, tools []Tool, onProgress func(Progress), msgs ...Message) (*Response, error) {
	a.mu.Lock()
	if spent := a.spent; a.opts.BudgetUSD > 0 && spent >= a.opts.BudgetUSD {
		a.mu.Unlock()
		return nil, fmt.Errorf("%w ($%.4f of $%.2f)", ErrBudget, spent, a.opts.BudgetUSD)
	}
	a.mu.Unlock()

	resp, err := a.c.Chat(ctx, Request{Model: spec.Model, Effort: spec.Effort, MaxTokens: spec.MaxTokens,
		JSON: asJSON, Messages: msgs, Tools: tools, OnProgress: onProgress})
	if resp != nil {
		a.mu.Lock()
		a.spent += resp.CostUSD
		a.calls++
		a.mu.Unlock()
	}
	return resp, err
}

func (a *Agent) system(tmpl string) Message {
	return System(strings.NewReplacer(
		"{{LEAN_VERSION}}", a.opts.LeanVersion,
		"{{IMPORTS}}", a.importsText(),
	).Replace(tmpl))
}

// importsText lists the loaded modules for the prompts. Harness is the
// server's own helper and of no use to the model, so it is left out.
func (a *Agent) importsText() string {
	var mods []string
	for _, m := range a.opts.Imports {
		if m != "Harness" {
			mods = append(mods, m)
		}
	}
	if len(mods) == 0 {
		return "all of Mathlib (`import Mathlib`)"
	}
	return strings.Join(mods, ", ")
}

// Lemma is a previously formalized (and possibly proved) statement that
// later statements may reference.
type Lemma struct {
	Name      string
	Signature string
	Text      string // original natural-language statement
	Proved    bool
}

func renderLemmas(header string, ls []Lemma, onlyProved bool) string {
	var b strings.Builder
	for _, l := range ls {
		if onlyProved && !l.Proved {
			continue
		}
		if b.Len() == 0 {
			b.WriteString(header + "\n")
		}
		fmt.Fprintf(&b, "theorem %s %s\n", l.Name, l.Signature)
		if l.Text != "" {
			fmt.Fprintf(&b, "  -- %s\n", oneLine(l.Text))
		}
	}
	return b.String()
}

// SplitStatements splits free-form input into individual statements.
func (a *Agent) SplitStatements(ctx context.Context, input string) ([]string, error) {
	resp, err := a.call(ctx, a.opts.Models.Split, true, System(splitSystem), User(input))
	if err != nil {
		return nil, err
	}
	var out struct {
		Statements []string `json:"statements"`
	}
	if err := unmarshalLenient(resp.Content, &out); err != nil {
		return nil, fmt.Errorf("llm: split: bad json %q: %w", truncate(resp.Content, 200), err)
	}
	var stmts []string
	for _, s := range out.Statements {
		if s = strings.TrimSpace(s); s != "" {
			stmts = append(stmts, s)
		}
	}
	if len(stmts) == 0 {
		return nil, errors.New("llm: split: no statements found")
	}
	return stmts, nil
}

// FormalizeInput describes one formalization request.
type FormalizeInput struct {
	Name      string  // theorem name to use (server-chosen)
	Statement string  // natural language
	Context   []Lemma // earlier statements it may refer to
	// Previous, if set, is a failed earlier formalization to repair.
	Previous *FormalizeRetry
}

// FormalizeRetry carries a rejected formalization and why it was rejected
// (Lean errors, or the user's correction).
type FormalizeRetry struct {
	Signature string
	Problem   string
}

// Formalization is a proposed Lean statement.
type Formalization struct {
	Signature string // "<binders> : <prop>", for lean.Statement
	Notes     string // the model's interpretation choices
	Response  *Response
}

// Formalize translates a natural-language statement into a Lean signature.
func (a *Agent) Formalize(ctx context.Context, in FormalizeInput) (*Formalization, error) {
	var b strings.Builder
	if c := renderLemmas("Previously formalized statements (you may refer to them by name):", in.Context, false); c != "" {
		b.WriteString(c + "\n")
	}
	fmt.Fprintf(&b, "Theorem name: %s\n\nStatement:\n%s\n", in.Name, in.Statement)
	msgs := []Message{a.system(formalizeSystem), User(b.String())}
	if p := in.Previous; p != nil {
		msgs = append(msgs,
			Assistant(fmt.Sprintf("```lean\ntheorem %s %s := by sorry\n```", in.Name, p.Signature)),
			User("That formalization was rejected:\n"+p.Problem+"\n\nWrite a corrected formalization in the same format."))
	}
	resp, err := a.call(ctx, a.opts.Models.Formalize, false, msgs...)
	if err != nil {
		return nil, err
	}
	sig, ok := ExtractSignature(resp.Content)
	if !ok || sig == "" {
		return nil, fmt.Errorf("llm: formalize: no theorem found in reply %q", truncate(resp.Content, 300))
	}
	return &Formalization{Signature: sig, Notes: Notes(resp.Content), Response: resp}, nil
}

// BackTranslate states in plain language what a Lean statement asserts,
// without seeing the original text, so the user can check faithfulness.
func (a *Agent) BackTranslate(ctx context.Context, name, signature string, lemmas []Lemma) (string, error) {
	var b strings.Builder
	if c := renderLemmas("Earlier statements referenced:", lemmas, false); c != "" {
		b.WriteString(c + "\n")
	}
	fmt.Fprintf(&b, "```lean\ntheorem %s %s\n```", name, signature)
	resp, err := a.call(ctx, a.opts.Models.Back, false, System(backTranslateSystem), User(b.String()))
	if err != nil {
		return "", err
	}
	return strings.TrimSpace(resp.Content), nil
}

// Faithfulness is the verdict of the independent formalization check.
type Faithfulness struct {
	Match  bool     `json:"match"`
	Issues []string `json:"issues"`
}

// CheckFaithfulness asks a separate call whether the Lean statement (and its
// back-translation) says exactly what the informal statement says.
func (a *Agent) CheckFaithfulness(ctx context.Context, text, name, signature, back string, lemmas []Lemma) (*Faithfulness, error) {
	var b strings.Builder
	if c := renderLemmas("Earlier statements the Lean statement may refer to:", lemmas, false); c != "" {
		b.WriteString(c + "\n")
	}
	fmt.Fprintf(&b, "Informal statement:\n%s\n\nLean statement:\n```lean\ntheorem %s %s\n```\n\nPlain-English reading of the Lean statement:\n%s\n",
		text, name, signature, back)
	resp, err := a.call(ctx, a.opts.Models.Judge, true, System(faithfulnessSystem), User(b.String()))
	if err != nil {
		return nil, err
	}
	var f Faithfulness
	if err := unmarshalLenient(resp.Content, &f); err != nil {
		return nil, fmt.Errorf("llm: faithfulness: bad json %q: %w", truncate(resp.Content, 200), err)
	}
	var issues []string
	for _, s := range f.Issues {
		if s = strings.TrimSpace(s); s != "" {
			issues = append(issues, s)
		}
	}
	f.Issues = issues
	if !f.Match && len(f.Issues) == 0 {
		f.Issues = []string{"the check reported a mismatch without details"}
	}
	return &f, nil
}

// unmarshalLenient decodes model-written JSON. If strict decoding fails it
// retries after escaping stray backslashes, typically LaTeX such as \( or
// \frac that the model forgot to double.
func unmarshalLenient(s string, v any) error {
	s = strings.TrimSpace(s)
	if bs := CodeBlocks(s); len(bs) > 0 {
		s = bs[len(bs)-1]
	}
	err := json.Unmarshal([]byte(s), v)
	if err == nil {
		return nil
	}
	if err2 := json.Unmarshal([]byte(fixJSONEscapes(s)), v); err2 == nil {
		return nil
	}
	return err
}

// fixJSONEscapes doubles backslashes inside strings that do not start a
// valid JSON escape. \b \f \n \r \t followed by a letter are taken as LaTeX
// (\frac, \neq, \times) too; this is only used after strict decoding failed.
func fixJSONEscapes(s string) string {
	isHex := func(c byte) bool { return c >= '0' && c <= '9' || c >= 'a' && c <= 'f' || c >= 'A' && c <= 'F' }
	isLetter := func(c byte) bool { return c >= 'a' && c <= 'z' || c >= 'A' && c <= 'Z' }
	var b strings.Builder
	inStr := false
	for i := 0; i < len(s); i++ {
		c := s[i]
		if !inStr {
			inStr = c == '"'
			b.WriteByte(c)
			continue
		}
		if c == '"' {
			inStr = false
			b.WriteByte(c)
			continue
		}
		if c != '\\' {
			b.WriteByte(c)
			continue
		}
		next := byte(0)
		if i+1 < len(s) {
			next = s[i+1]
		}
		valid := false
		switch next {
		case '"', '\\', '/':
			valid = true
		case 'u':
			valid = i+5 < len(s) && isHex(s[i+2]) && isHex(s[i+3]) && isHex(s[i+4]) && isHex(s[i+5])
		case 'b', 'f', 'n', 'r', 't':
			valid = !(i+2 < len(s) && isLetter(s[i+2]))
		}
		if valid {
			b.WriteByte(c)
			b.WriteByte(next)
			i++
		} else {
			b.WriteString(`\\`)
		}
	}
	return b.String()
}

// ProveInput describes the theorem to prove.
type ProveInput struct {
	Name      string
	Signature string
	Text      string  // natural-language statement (helps the model)
	Context   []Lemma // only Proved ones are offered for use
	// Extra is shown verbatim before the theorem (e.g. the outline a step
	// belongs to, or what the direct attempts tried).
	Extra string
}

// ProofSession is a multi-turn conversation: propose a proof, receive
// compiler feedback, propose a fix. Not safe for concurrent use; run
// several sessions for parallel attempts.
type ProofSession struct {
	a                *Agent
	spec             ModelSpec
	system           string // prompt template: proveSystem or outlineSystem
	intro            Message
	rounds           []round // completed (proof, feedback) pairs
	pending          string  // last proposed reply awaiting feedback
	pendingReasoning string  // its reasoning (sent back when tools are used)
	dropped          int     // rounds summarized away
	restart          string  // after Restart: what was tried, sent instead of the old rounds
}

type round struct{ reply, reasoning, feedback string }

// NewProofSession starts a proof conversation with the default prover
// model (Models.Prove).
func (a *Agent) NewProofSession(in ProveInput) *ProofSession {
	return a.NewProofSessionWith(in, a.opts.Models.Prove)
}

// NewProofSessionWith starts a proof conversation using spec.
func (a *Agent) NewProofSessionWith(in ProveInput, spec ModelSpec) *ProofSession {
	var b strings.Builder
	if c := renderLemmas("Previously proved theorems you may use:", in.Context, true); c != "" {
		b.WriteString(c + "\n")
	}
	if in.Text != "" {
		fmt.Fprintf(&b, "Informal statement: %s\n\n", oneLine(in.Text))
	}
	if in.Extra != "" {
		b.WriteString(strings.TrimSpace(in.Extra) + "\n\n")
	}
	fmt.Fprintf(&b, "Prove:\n```lean\ntheorem %s %s := by\n  ...\n```\nReply with the tactic script only.", in.Name, in.Signature)
	return &ProofSession{a: a, spec: spec, system: proveSystem, intro: User(b.String())}
}

// NewPlanSession starts a conversation that asks for a proof outline (see
// outlineSystem): have-steps proved by sorry, then a proof from them. It
// takes feedback like a proof session and uses the prover model.
func (a *Agent) NewPlanSession(in ProveInput) *ProofSession {
	var b strings.Builder
	if c := renderLemmas("Previously proved theorems you may use:", in.Context, true); c != "" {
		b.WriteString(c + "\n")
	}
	if in.Text != "" {
		fmt.Fprintf(&b, "Informal statement: %s\n\n", oneLine(in.Text))
	}
	if in.Extra != "" {
		b.WriteString(strings.TrimSpace(in.Extra) + "\n\n")
	}
	fmt.Fprintf(&b, "Write a proof outline for:\n```lean\ntheorem %s %s := by\n  ...\n```\nReply with the outline in one lean code block.", in.Name, in.Signature)
	return &ProofSession{a: a, spec: a.opts.Models.Prove, system: outlineSystem, intro: User(b.String())}
}

// Next asks for a proof (the first one, or a fix after Feedback).
func (s *ProofSession) Next(ctx context.Context) (body string, resp *Response, err error) {
	return s.NextProgress(ctx, nil)
}

// NextProgress is Next with streaming progress reports (see Request.OnProgress).
func (s *ProofSession) NextProgress(ctx context.Context, onProgress func(Progress)) (body string, resp *Response, err error) {
	msgs := s.history(s.system, false)
	resp, err = s.a.callProgress(ctx, s.spec, false, onProgress, msgs...)
	if err != nil {
		return "", resp, err
	}
	body = ExtractProofBody(resp.Content)
	// Keep only the code in history: shorter context, and prose from a
	// failed attempt tends to mislead later ones.
	s.pending = "```lean\n" + body + "\n```"
	return body, resp, nil
}

// history is the conversation so far: system prompt, task, earlier rounds.
// withReasoning keeps each round's reasoning (required with tools).
func (s *ProofSession) history(system string, withReasoning bool) []Message {
	msgs := []Message{s.a.system(system), s.intro}
	if s.restart != "" {
		msgs = append(msgs, Assistant("(earlier attempts omitted)"), User(s.restart))
	}
	if s.dropped > 0 {
		msgs = append(msgs, Assistant("(earlier attempts omitted)"),
			User(fmt.Sprintf("%d earlier attempt(s) failed and are omitted. Continue.", s.dropped)))
	}
	for _, r := range s.rounds {
		m := Assistant(r.reply)
		if withReasoning {
			m.ReasoningContent = r.reasoning
		}
		msgs = append(msgs, m, User(r.feedback))
	}
	return msgs
}

// ToolRunner executes the tools a proof session may use.
type ToolRunner interface {
	Tools() []Tool
	// Run executes one call and returns the text shown to the model.
	// stop=true ends the attempt (e.g. check_proof verified the proof).
	Run(ctx context.Context, call ToolCall) (result string, stop bool)
}

// ErrNoAnswer means the model kept calling tools past its budget.
var ErrNoAnswer = errors.New("llm: no final answer within the tool-call budget")

// NextTools runs one attempt in which the model may call tools (at most
// maxCalls in total) before replying with a proof. onTurn sees every LLM
// response (cost, tokens). If a tool returns stop, NextTools returns
// stopped=true. Otherwise body is the model's final proof.
func (s *ProofSession) NextTools(ctx context.Context, runner ToolRunner, maxCalls int,
	onProgress func(Progress), onTurn func(*Response)) (body string, stopped bool, err error) {
	msgs := s.history(proveSystem+proveToolsAddendum, true)
	tools := runner.Tools()
	calls, warned := 0, false
	for {
		resp, err := s.a.callTools(ctx, s.spec, false, tools, onProgress, msgs...)
		if resp != nil && onTurn != nil {
			onTurn(resp)
		}
		if err != nil {
			return "", false, err
		}
		if len(resp.ToolCalls) == 0 {
			body = ExtractProofBody(resp.Content)
			s.pending = "```lean\n" + body + "\n```"
			s.pendingReasoning = resp.Reasoning
			return body, false, nil
		}
		if warned {
			return "", false, ErrNoAnswer
		}
		msgs = append(msgs, Message{Role: "assistant", Content: resp.Content,
			ReasoningContent: resp.Reasoning, ToolCalls: resp.ToolCalls})
		for _, c := range resp.ToolCalls {
			calls++
			result, stop := runner.Run(ctx, c)
			if stop {
				return "", true, nil
			}
			msgs = append(msgs, ToolResult(c.ID, result))
		}
		if calls >= maxCalls {
			warned = true
			msgs = append(msgs, User("Tool budget used up. Reply now with your final tactic proof in one lean code block, without calling tools."))
		}
	}
}

// Feedback records why the last proof failed; call Next for a fix.
func (s *ProofSession) Feedback(feedback string) {
	if s.pending == "" {
		return
	}
	fix := "\n\nFix the proof. Reply with the complete corrected tactic script in one lean code block."
	if s.system == outlineSystem {
		fix = "\n\nRevise the outline. Reply with the complete outline in one lean code block."
	}
	s.rounds = append(s.rounds, round{reply: s.pending, reasoning: s.pendingReasoning, feedback: feedback + fix})
	s.pending, s.pendingReasoning = "", ""
	if over := len(s.rounds) - s.a.opts.MaxFeedbackRounds; over > 0 {
		s.rounds = s.rounds[over:]
		s.dropped += over
	}
}

// Restart drops the conversation so far (the model keeps repeating a failing
// approach and its own earlier attempts anchor it) and continues from the
// intro plus summary, which should say what was tried and what to do now.
func (s *ProofSession) Restart(summary string) {
	s.restart = summary
	s.rounds, s.pending, s.pendingReasoning, s.dropped = nil, "", "", 0
}

// Rounds is the number of failed attempts recorded so far.
func (s *ProofSession) Rounds() int { return s.dropped + len(s.rounds) }

// Explain describes a verified proof in plain language.
func (a *Agent) Explain(ctx context.Context, text, name, signature, proof string) (string, error) {
	u := fmt.Sprintf("Statement: %s\n\nVerified Lean proof:\n```lean\ntheorem %s %s := by\n%s\n```", text, name, signature, indentLines(proof, "  "))
	resp, err := a.call(ctx, a.opts.Models.Explain, false, System(explainSystem), User(u))
	if err != nil {
		return "", err
	}
	return strings.TrimSpace(resp.Content), nil
}

func oneLine(s string) string { return strings.Join(strings.Fields(s), " ") }

func truncate(s string, n int) string {
	if len(s) <= n {
		return s
	}
	return s[:n] + "..."
}

func indentLines(s, p string) string {
	ls := strings.Split(s, "\n")
	for i := range ls {
		ls[i] = p + ls[i]
	}
	return strings.Join(ls, "\n")
}

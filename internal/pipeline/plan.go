package pipeline

// Proof outlines (A3). When the direct attempts fail, the model writes an
// outline: a few intermediate facts as `have stepK : P := by sorry`, then a
// proof of the theorem from them. Lean checks that proof right away, with the
// steps as hypotheses of the theorem. Each step is then proved as its own
// small theorem (the theorem's hypotheses and the earlier steps assumed), all
// steps in parallel. Finally the pieces are assembled into one proof without
// sorry, which Lean checks against the original statement: that check is the
// only one the result relies on.

import (
	"context"
	"errors"
	"fmt"
	"regexp"
	"strings"
	"time"

	"mathprover/internal/lean"
	"mathprover/internal/llm"
)

const maxPlanSteps = 8

type planStep struct{ Name, Prop string }

type outline struct {
	Steps  []planStep
	Main   string // tactic proof of the theorem from the steps
	Source string // the outline as written (normalized)
}

var (
	reStepHead    = regexp.MustCompile(`^have\s+([\p{L}_][\p{L}\p{N}_'!?]*)\s*:\s*`)
	reStepSorry   = regexp.MustCompile(`(?s)\s*:=\s*(?:by\s+)?sorry\s*$`)
	reSorryWord   = regexp.MustCompile(`(^|[^\p{L}\p{N}_'.])sorry($|[^\p{L}\p{N}_'])`)
	reLineComment = regexp.MustCompile(`--.*$`)
)

// parseOutline reads an outline: leading top-level `have name : P := by
// sorry` blocks, then the main proof. The error text is written for the
// model.
func parseOutline(body string) (*outline, error) {
	body = lean.NormalizeBody(body)
	// Top-level tactics start at column 0; indented lines continue them.
	var blocks []string
	for _, l := range strings.Split(body, "\n") {
		if len(blocks) == 0 || (strings.TrimSpace(l) != "" && !strings.HasPrefix(l, " ")) {
			blocks = append(blocks, l)
		} else {
			blocks[len(blocks)-1] += "\n" + l
		}
	}
	ol := &outline{Source: body}
	seen := map[string]bool{}
	i := 0
	for ; i < len(blocks); i++ {
		b := strings.TrimSpace(blocks[i])
		if b == "" || strings.HasPrefix(b, "--") {
			continue
		}
		if !strings.HasPrefix(b, "have") || !reStepSorry.MatchString(b) {
			break
		}
		m := reStepHead.FindStringSubmatchIndex(b)
		if m == nil {
			return nil, fmt.Errorf("Could not read the step `%s`. Write each step as `have name : statement := by sorry`, with quantifiers and assumptions inside the statement (no binders before the colon).", firstLine(b))
		}
		name := b[m[2]:m[3]]
		prop := flattenTerm(reStepSorry.ReplaceAllString(b[m[1]:], ""))
		if prop == "" {
			return nil, fmt.Errorf("The step %s has no statement.", name)
		}
		if seen[name] {
			return nil, fmt.Errorf("Two steps are named %s; give every step its own name.", name)
		}
		seen[name] = true
		ol.Steps = append(ol.Steps, planStep{Name: name, Prop: prop})
	}
	ol.Main = strings.TrimSpace(strings.Join(blocks[i:], "\n"))
	switch {
	case len(ol.Steps) == 0:
		return nil, errors.New("The outline has no steps. It must start with lines `have step1 : <statement> := by sorry` at column 0, followed by the proof that uses them.")
	case len(ol.Steps) > maxPlanSteps:
		return nil, fmt.Errorf("The outline has %d steps; use at most %d (group small facts together).", len(ol.Steps), maxPlanSteps)
	case ol.Main == "":
		return nil, errors.New("The outline has no proof after the steps: add the tactics that prove the theorem from them.")
	case reSorryWord.MatchString(ol.Main):
		return nil, errors.New("sorry appears after the steps. All `have ... := by sorry` steps must come first, each at column 0, and the proof after them must not use sorry.")
	}
	return ol, nil
}

// restates reports a step that is just the theorem's own conclusion.
func (ol *outline) restates(prop string) string {
	p := strings.Join(strings.Fields(prop), " ")
	for _, s := range ol.Steps {
		if strings.Join(strings.Fields(s.Prop), " ") == p {
			return s.Name
		}
	}
	return ""
}

// flattenTerm puts a (possibly multi-line) Lean term on one line, dropping
// line comments, so it can be used as a binder type.
func flattenTerm(s string) string {
	lines := strings.Split(s, "\n")
	for i, l := range lines {
		lines[i] = reLineComment.ReplaceAllString(l, "")
	}
	return strings.Join(strings.Fields(strings.Join(lines, " ")), " ")
}

func firstLine(s string) string {
	l, _, _ := strings.Cut(strings.TrimSpace(s), "\n")
	return l
}

// stepSig is the signature of the theorem `binders (h1 : P1) ... : prop`.
func stepSig(binders string, hyps []planStep, prop string) string {
	var parts []string
	if binders != "" {
		parts = append(parts, binders)
	}
	for _, h := range hyps {
		parts = append(parts, "("+h.Name+" : "+h.Prop+")")
	}
	return strings.TrimSpace(strings.Join(parts, " ") + " : " + prop)
}

// assemble turns the outline and the step proofs into one proof.
func assemble(ol *outline, proofs []string) string {
	var b strings.Builder
	for i, s := range ol.Steps {
		fmt.Fprintf(&b, "have %s : %s := by\n%s\n", s.Name, s.Prop, indentBody(lean.NormalizeBody(proofs[i]), "  "))
	}
	b.WriteString(ol.Main)
	return b.String()
}

func indentBody(s, p string) string {
	ls := strings.Split(s, "\n")
	for i, l := range ls {
		if l != "" {
			ls[i] = p + l
		}
	}
	return strings.Join(ls, "\n")
}

// plan runs the outline stage. It returns a verified outcome for stmt, or
// nil if no outline led to a proof.
func (j *job) plan(ctx context.Context, sr *StatementResult, stmt lean.Statement, base *lean.Snapshot, lemmas []llm.Lemma) (*lean.Outcome, error) {
	binders, prop, ok := lean.SplitSignature(stmt.Signature)
	if !ok || prop == "" {
		return nil, nil
	}
	why := "no direct proof found"
	if !j.p.opts.NoPlan && j.p.opts.PlanAfter < 0 {
		why = "outline first (no direct attempts)"
	}
	j.emit(Event{Type: EvPlanning, Stmt: sr.Index, Message: fmt.Sprintf("%s; asking for a proof outline (%d outline(s), %d attempt(s) per step)", why, j.p.opts.PlanAttempts, j.p.opts.StepAttempts)})
	sess := j.p.agent.NewPlanSession(llm.ProveInput{Name: stmt.Name, Signature: stmt.Signature, Text: sr.Text, Context: lemmas, Extra: j.triedSummary(sr)})
	proved := map[string]string{} // step signature → verified proof, reused across outlines
	for k := 1; k <= j.p.opts.PlanAttempts; k++ {
		if err := ctx.Err(); err != nil {
			return nil, err
		}
		rec := AttemptRecord{Stage: "outline", Session: 1, N: k, Plan: true}
		t0 := time.Now()
		body, resp, err := sess.Next(ctx)
		rec.LLMTime = time.Since(t0)
		if resp != nil {
			rec.CostUSD = resp.CostUSD
		}
		if err != nil {
			if fatalErr(ctx, err) {
				return nil, err
			}
			if errors.Is(err, llm.ErrTruncated) {
				rec.ErrorKinds = []string{"truncated"}
				j.record(sr, rec)
				continue
			}
			return nil, err
		}
		rec.Body = body
		reject := func(kinds []string, fb string) {
			rec.ErrorKinds, rec.Feedback = kinds, fb
			j.record(sr, rec)
			sess.Feedback(fb)
		}
		if llm.ClaimsFalse(body) {
			reject([]string{"claims_false"}, "FALSE is not an answer here (the negation is tried separately): write a proof outline.")
			continue
		}
		ol, perr := parseOutline(body)
		if perr == nil {
			if name := ol.restates(prop); name != "" {
				perr = fmt.Errorf("The step %s is the theorem itself. Each step must be a smaller intermediate fact.", name)
			}
		}
		if perr != nil {
			reject([]string{"bad_outline"}, perr.Error())
			continue
		}

		main := lean.Statement{Name: stmt.Name + "_outline", Signature: stepSig(binders, ol.Steps, prop)}
		t1 := time.Now()
		fb, kinds, err := j.checkOutline(ctx, base, main, ol.Main)
		rec.LeanTime = time.Since(t1)
		if err != nil {
			return nil, err
		}
		if fb != "" {
			reject(kinds, fb)
			continue
		}
		rec.Verified = true // the outline holds, given its steps
		j.record(sr, rec)
		names := make([]string, len(ol.Steps))
		for i, s := range ol.Steps {
			names[i] = s.Name
		}
		j.emit(Event{Type: EvPlanned, Stmt: sr.Index, Message: fmt.Sprintf("outline %d accepted by Lean: %d step(s) (%s); proving them", k, len(ol.Steps), strings.Join(names, ", "))})

		proofs, failures, err := j.proveSteps(ctx, sr, stmt, base, lemmas, binders, ol, proved)
		if err != nil {
			return nil, err
		}
		if len(failures) > 0 {
			sess.Feedback(stepFeedback(ol, proofs, failures))
			continue
		}
		o, err := j.p.check.CheckProof(ctx, base, stmt, assemble(ol, proofs))
		if err != nil {
			if ctx.Err() != nil {
				return nil, ctx.Err()
			}
			return nil, fmt.Errorf("lean: %w", err)
		}
		if o.Verdict.Verified {
			j.emit(Event{Type: EvPlanned, Stmt: sr.Index, Message: "all steps proved; the assembled proof is verified"})
			return j.resolveSearch(ctx, sr, stmt, base, o), nil
		}
		fb = "Every step was proved, but the assembled proof (each step's proof inserted under its have) did not compile:\n" + lean.RenderFeedback(o, j.p.opts.Feedback)
		j.emit(Event{Type: EvError, Stmt: sr.Index, Message: "the assembled outline proof did not compile"})
		sess.Feedback(fb)
	}
	return nil, nil
}

// checkOutline checks the proof after the steps, with the steps as
// hypotheses. feedback is "" if it compiles.
func (j *job) checkOutline(ctx context.Context, base *lean.Snapshot, main lean.Statement, body string) (feedback string, kinds []string, err error) {
	if err := main.Validate(); err != nil {
		return "The steps cannot be used as hypotheses: " + err.Error(), []string{"bad_outline"}, nil
	}
	sc, err := j.p.check.CheckStatement(ctx, base, main)
	if err != nil {
		if ctx.Err() != nil {
			return "", nil, ctx.Err()
		}
		return "", nil, fmt.Errorf("lean: %w", err)
	}
	if !sc.OK {
		for _, d := range sc.Errors {
			kinds = append(kinds, string(d.Kind))
		}
		return "Lean rejected the step statements (checked as hypotheses of the theorem):\n" + renderStatementErrors(sc), kinds, nil
	}
	o, err := j.p.check.CheckProof(ctx, base, main, body)
	if err != nil {
		if ctx.Err() != nil {
			return "", nil, ctx.Err()
		}
		return "", nil, fmt.Errorf("lean: %w", err)
	}
	if o.Verdict.Verified {
		return "", nil, nil
	}
	for _, d := range o.Verdict.Errors {
		kinds = append(kinds, string(d.Kind))
	}
	fb := "Lean accepted the step statements, but the proof after the steps does not compile with the steps assumed:\n" + lean.RenderFeedback(o, j.p.opts.Feedback)
	if hint := j.suggest(ctx, o); hint != "" {
		fb += "\n" + hint
	}
	return fb, kinds, nil
}

// proveSteps proves the outline's steps in parallel. proofs[i] is set for
// each proved step; failures maps the others to why they failed.
func (j *job) proveSteps(ctx context.Context, sr *StatementResult, stmt lean.Statement, base *lean.Snapshot, lemmas []llm.Lemma, binders string, ol *outline, proved map[string]string) (proofs []string, failures map[int]string, err error) {
	n := len(ol.Steps)
	proofs, failures = make([]string, n), map[int]string{}
	stmts := make([]lean.Statement, n)
	type res struct {
		i         int
		body, why string
		err       error
	}
	ch := make(chan res, n)
	running := 0
	for i, st := range ol.Steps {
		stmts[i] = lean.Statement{Name: stmt.Name + "_" + st.Name, Signature: stepSig(binders, ol.Steps[:i], st.Prop)}
		if b, ok := proved[stmts[i].Signature]; ok {
			proofs[i] = b
			j.emit(Event{Type: EvStepDone, Stmt: sr.Index, Message: st.Name + ": unchanged, reusing its proof"})
			continue
		}
		running++
		sn := j.nextSession(sr)
		go func() {
			in := llm.ProveInput{Name: stmts[i].Name, Signature: stmts[i].Signature, Context: lemmas, Extra: stepContext(sr.Text, ol, st.Name)}
			// A fresh failedSet: a step name can come back with another statement.
			o, err := j.session(ctx, sn, j.p.lastStage(), sr, stmts[i], base, in, newFailedSet(),
				sessionOpts{max: j.p.opts.StepAttempts, allowFalse: true, step: st.Name})
			switch {
			case errors.Is(err, errClaimsFalse):
				ch <- res{i: i, why: "the model says this step is false: " + truncateText(oneLine(j.lastStepRecord(sr, st.Name).Body), 300)}
			case err != nil:
				ch <- res{i: i, err: err}
			case o == nil:
				why := fmt.Sprintf("no proof found in %d attempt(s)", j.p.opts.StepAttempts)
				if fb := j.lastStepRecord(sr, st.Name).Feedback; fb != "" {
					why += ". The last attempt's errors:\n" + truncateText(fb, 1500)
				}
				ch <- res{i: i, why: why}
			default:
				ch <- res{i: i, body: o.Attempt.Body}
			}
		}()
	}
	for range running {
		r := <-ch
		name := ol.Steps[r.i].Name
		switch {
		case r.err != nil:
			if err == nil {
				err = r.err
			}
		case r.body != "":
			proofs[r.i] = r.body
			proved[stmts[r.i].Signature] = r.body
			j.emit(Event{Type: EvStepDone, Stmt: sr.Index, Message: name + ": proved"})
		default:
			failures[r.i] = r.why
			j.emit(Event{Type: EvStepDone, Stmt: sr.Index, Message: name + ": not proved (" + firstLine(r.why) + ")"})
		}
	}
	return proofs, failures, err
}

// lastStepRecord is the latest attempt at the named step. Steps of one name
// never run concurrently, so after its session it is that session's last.
func (j *job) lastStepRecord(sr *StatementResult, step string) AttemptRecord {
	j.mu.Lock()
	defer j.mu.Unlock()
	for i := len(sr.Attempts) - 1; i >= 0; i-- {
		if sr.Attempts[i].Step == step {
			return sr.Attempts[i]
		}
	}
	return AttemptRecord{}
}

// stepContext tells a step's prover where the step comes from.
func stepContext(text string, ol *outline, step string) string {
	return fmt.Sprintf("This theorem is the step `%s` of a proof outline for: %s\n\nThe outline (every step is proved separately; earlier steps are hypotheses of this theorem, the theorem's own hypotheses are kept):\n```lean\n%s\n```\nProve only the step `%s`, stated below.",
		step, oneLine(text), ol.Source, step)
}

// stepFeedback tells the outline session which steps failed and why.
func stepFeedback(ol *outline, proofs []string, failures map[int]string) string {
	var b strings.Builder
	b.WriteString("Lean accepted the outline, but some steps could not be proved:\n")
	var ok []string
	for i, s := range ol.Steps {
		if why, bad := failures[i]; bad {
			fmt.Fprintf(&b, "- %s: %s\n", s.Name, why)
		} else if proofs[i] != "" {
			ok = append(ok, s.Name)
		}
	}
	if len(ok) > 0 {
		fmt.Fprintf(&b, "Proved: %s. Keep these steps word for word (and the steps before them) to reuse their proofs.\n", strings.Join(ok, ", "))
	}
	b.WriteString("Check that the failed steps are true. Split them into smaller steps, weaken them, or take another route.")
	return b.String()
}

// triedSummary shows the outline session the last direct attempt.
func (j *job) triedSummary(sr *StatementResult) string {
	j.mu.Lock()
	defer j.mu.Unlock()
	var last *AttemptRecord
	n := 0
	for i := range sr.Attempts {
		a := &sr.Attempts[i]
		if a.Disproof || a.Free || a.Plan || a.Step != "" || a.Verified || a.Feedback == "" || llm.ClaimsFalse(a.Body) {
			continue
		}
		n++
		last = a
	}
	if last == nil {
		return ""
	}
	return fmt.Sprintf("%d direct proof attempt(s) were rejected by Lean. The last one (parts of it may still be useful inside steps):\n```lean\n%s\n```\nLean's errors for it:\n%s",
		n, truncateText(last.Body, 8000), truncateText(last.Feedback, 2000))
}

// planAttempts counts the outlines asked for.
func planAttempts(sr *StatementResult) int {
	n := 0
	for _, a := range sr.Attempts {
		if a.Plan {
			n++
		}
	}
	return n
}

func truncateText(s string, n int) string {
	if r := []rune(s); len(r) > n {
		return string(r[:n]) + "…"
	}
	return s
}

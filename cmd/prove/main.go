// Command prove runs the full pipeline on natural-language input from the
// command line, printing progress to stderr and the result to stdout.
//
//	go run ./cmd/prove "For all real x, x^2 - 2x + 1 >= 0."
//	echo "..." | go run ./cmd/prove -confirm=false
//
// Importing Mathlib takes minutes, so Lean can be kept loaded in a
// background prover: start it once with `prove -serve`, and later `prove`
// calls send their jobs to it (see internal/daemon). Without one, prove
// starts Lean itself as before.
package main

import (
	"bufio"
	"context"
	"encoding/json"
	"flag"
	"fmt"
	"io"
	"os"
	"os/signal"
	"strings"
	"time"

	"mathprover/internal/daemon"
	"mathprover/internal/dotenv"
	"mathprover/internal/lean"
	"mathprover/internal/llm"
	"mathprover/internal/pipeline"
)

// runner runs one job, in this process or on the background prover.
type runner func(ctx context.Context, job daemon.Job) (*pipeline.Result, error)

func main() {
	var (
		leanDir   = flag.String("lean-dir", "lean_env", "Lake project with Mathlib (see scripts/bootstrap.sh)")
		envFile   = flag.String("env", ".env", "dotenv file with DEEPSEEK_API_KEY")
		workers   = flag.Int("workers", 1, "warm Lean workers (each ~7GB RAM); each job gets a fresh one (use 2 with -i or -serve to skip the ~4s restart between jobs)")
		sandbox   = flag.String("sandbox", "bwrap", "Lean process isolation: bwrap | none")
		sbMem     = flag.String("sandbox-mem", "10G", "memory limit per Lean worker; empty = none")
		sbTasks   = flag.Int("sandbox-tasks", 256, "process/thread limit per Lean worker; 0 = none")
		verify    = flag.Bool("verify", true, "independently re-check proofs at the end (kernel + axiom audit, ~30s)")
		model     = flag.String("model", llm.ModelFlash, "prover model: deepseek-flash | deepseek-v4-pro | any id your endpoint serves")
		effort    = flag.String("effort", "", "single stage at this effort (none|low|high|max; OpenAI: low|medium|high) instead of the ladder")
		stagesArg = flag.String("stages", strings.Join(pipeline.DefaultStageNames, ","), "proof-search ladder: comma-separated presets (fast, tools, tools-low, think, deep, deep-tools)")
		auxModel  = flag.String("aux-model", llm.ModelFlash, "model for split, formalize, back-translate and explain")
		auxEffort = flag.String("aux-effort", "none", "reasoning effort for split, back-translate and explain (gpt-5: minimal)")
		attempts  = flag.Int("attempts", 0, "if > 0: proof attempts per session in every stage")
		parallel  = flag.Int("parallel", 0, "if > 0: parallel proof sessions in every stage")
		noAuto    = flag.Bool("no-auto", false, "skip trying automation tactics before the LLM")
		budget    = flag.Float64("budget", 0.50, "max USD to spend per job (0 = unlimited)")
		timeout   = flag.Duration("timeout", 30*time.Minute, "time limit per job (after Lean is ready)")
		startTO   = flag.Duration("start-timeout", 10*time.Minute, "time allowed for each Lean worker to import Mathlib")
		cmdTO     = flag.Duration("cmd-timeout", time.Minute, "time allowed for each Lean check")
		imports   = flag.String("imports", "Mathlib", "comma-separated Lean modules each worker imports (Harness is always added); fewer = faster startup, less RAM")
		confirm   = flag.Bool("confirm", false, "ask before proving each formalized statement")
		noExplain = flag.Bool("no-explain", false, "skip plain-language explanations")
		noSplit   = flag.Bool("no-split", false, "treat input as a single statement")
		noFaith   = flag.Bool("no-faith-check", false, "skip the independent check that each Lean statement says what the text says")
		noDisprov = flag.Bool("no-disprove", false, "don't look for counterexamples or try to prove the negation of unproved statements")
		noPlan    = flag.Bool("no-plan", false, "don't fall back to a proof outline (have-steps proved one by one) when direct attempts fail")
		planTries = flag.Int("plan-attempts", 4, "proof outlines to try after direct attempts fail")
		stepTries = flag.Int("step-attempts", 4, "proof attempts per outline step")
		planAfter = flag.Int("plan-after", 3, "direct proof attempts per session in each stage before the proof outline (caps -attempts unless -no-plan; 0 = outline right away)")
		asJSON    = flag.Bool("json", false, "print the result as JSON")
		verbose   = flag.Bool("v", false, "print Lean feedback for failed attempts")
		interact  = flag.Bool("i", false, "interactive: keep Lean loaded and prompt for statements repeatedly")
		serve     = flag.Bool("serve", false, "run as the background prover: load Lean once, then serve jobs on -socket")
		stopSrv   = flag.Bool("stop", false, "stop the background prover")
		status    = flag.Bool("status", false, "show whether the background prover is running")
		socket    = flag.String("socket", "", "Unix socket of the background prover (default ~/.quod/prove.sock)")
		local     = flag.Bool("local", false, "start Lean in this process even if a background prover is running")
		benchFile = flag.String("bench", "", "run a bench file (lines: true|false | category | statement) and report metrics")
		benchRuns = flag.Int("runs", 1, "-bench: runs per model and problem (stability)")
		benchMods = flag.String("models", "", "-bench: comma-separated models, each `model` or `model@endpoint` (default: -model)")
		benchOut  = flag.String("bench-out", "bench-results", "-bench: directory for report.md and results.json")
	)
	flag.Parse()

	if err := dotenv.Load(*envFile); err != nil {
		fatal("loading %s: %v", *envFile, err)
	}
	// Flags not given on the command line fall back to the environment, so
	// .env can pin the models (e.g. for a 9router endpoint).
	setFlags := map[string]bool{}
	flag.Visit(func(f *flag.Flag) { setFlags[f.Name] = true })
	for name, env := range map[string]string{
		"model": "LLM_MODEL", "effort": "LLM_EFFORT",
		"aux-model": "LLM_AUX_MODEL", "aux-effort": "LLM_AUX_EFFORT",
		"start-timeout": "LEAN_START_TIMEOUT", "cmd-timeout": "LEAN_CMD_TIMEOUT",
		"imports": "LEAN_IMPORTS", "lean-dir": "LEAN_DIR", "socket": "PROVE_SOCKET",
	} {
		if v := strings.TrimSpace(os.Getenv(env)); v != "" && !setFlags[name] {
			_ = flag.Set(name, v)
		}
	}
	if *socket == "" {
		*socket = daemon.DefaultSocket()
	}

	sb := lean.Sandbox{Kind: lean.SandboxKind(*sandbox), MemoryMax: *sbMem, TasksMax: *sbTasks}
	if sb.Kind == lean.SandboxNone {
		sb = lean.Sandbox{Kind: lean.SandboxNone}
	}
	ls := leanSettings{
		Dir: *leanDir, Workers: *workers, Imports: leanImports(*imports),
		StartTimeout: *startTO, CmdTimeout: *cmdTO, Sandbox: sb, Verify: *verify,
	}
	switch {
	case *stopSrv:
		runStop(*socket)
		return
	case *status:
		runStatus(*socket)
		return
	case *serve:
		runServe(*socket, ls)
		return
	}

	// A model may name its endpoint ("cx/gpt-6-luna@local"); the job then
	// sends all its LLM calls there, so the aux model must live there too.
	mref, err := parseModelRef(*model)
	if err != nil {
		fatal("%v", err)
	}
	aref, err := parseModelRef(*auxModel)
	if err != nil {
		fatal("%v", err)
	}
	if aref.URL != mref.URL {
		if mref.URL == "" {
			fatal("-aux-model %s uses another endpoint than -model %s; give both the same @endpoint", aref, mref)
		}
		aref = mref // model on a named endpoint: use it for the aux tasks too
	}
	base := daemon.Job{
		Model: mref.Model, Effort: *effort, AuxModel: aref.Model, AuxEffort: *auxEffort,
		Stages: strings.Split(*stagesArg, ","), NoAuto: *noAuto,
		Attempts: *attempts, Parallel: *parallel, NoSplit: *noSplit, NoExplain: *noExplain,
		NoFaithCheck: *noFaith, NoDisprove: *noDisprov,
		NoPlan: *noPlan, PlanAttempts: *planTries, StepAttempts: *stepTries, PlanAfter: planAfterJob(*planAfter),
		BudgetUSD: *budget, Timeout: *timeout,
		BaseURL: mref.URL, APIKey: mref.Key,
	}
	if _, err := jobStages(base); err != nil {
		fatal("%v", err)
	}

	var benchProblems []benchProblem
	var benchModels []modelRef
	if *benchFile != "" {
		if benchProblems, err = loadBench(*benchFile); err != nil {
			fatal("%v", err)
		}
		benchModels = []modelRef{mref}
		if strings.TrimSpace(*benchMods) != "" {
			benchModels = nil
			for _, s := range strings.Split(*benchMods, ",") {
				ref, err := parseModelRef(s)
				if err != nil {
					fatal("%v", err)
				}
				benchModels = append(benchModels, ref)
			}
		}
		if *benchRuns < 1 {
			fatal("-runs must be at least 1")
		}
	}

	var (
		input     string
		fromStdin bool
		stdin     = bufio.NewReader(os.Stdin)
	)
	switch {
	case *benchFile != "":
		if *confirm {
			fatal("-confirm cannot be used with -bench")
		}
	case *interact:
		input = strings.Join(flag.Args(), " ") // optional first job
	default:
		input, fromStdin = readInput()
		if strings.TrimSpace(input) == "" {
			fatal("no input: pass statements as arguments or on stdin (or use -i)")
		}
	}

	useDaemon := !*local && daemon.Available(*socket)
	if useDaemon && *confirm {
		progress("note: -confirm asks on this terminal, so Lean starts in this process instead of using the background prover")
		useDaemon = false
	}
	// The bench prints one line per job instead of every event.
	onEvent := func(e pipeline.Event) { printEvent(e, *verbose) }
	if *benchFile != "" {
		onEvent = nil
	}
	var run runner
	if useDaemon {
		progress("using background prover on %s", *socket)
		run = remoteRunner(*socket, onEvent)
	} else {
		// Startup can be interrupted with Ctrl-C.
		ctx, stop := signal.NotifyContext(context.Background(), os.Interrupt)
		pv, err := startProver(ctx, ls)
		stop()
		if err != nil {
			fatal("%v", err)
		}
		defer pv.Close()
		hooks := pipeline.Hooks{OnEvent: onEvent}
		if *confirm {
			hooks.Confirm = terminalConfirm(stdin, fromStdin)
		}
		run = func(ctx context.Context, job daemon.Job) (*pipeline.Result, error) {
			return pv.run(ctx, job, hooks)
		}
	}

	if *benchFile != "" {
		ctx, stop := signal.NotifyContext(context.Background(), os.Interrupt)
		defer stop()
		if err := runBench(ctx, run, base, benchProblems, benchModels, *benchRuns, *benchOut); err != nil {
			fatal("bench: %v", err)
		}
		return
	}

	var totalUSD float64
	var totalCalls int
	// runJob runs one input; Ctrl-C cancels just this job.
	runJob := func(input string) error {
		jctx, jstop := signal.NotifyContext(context.Background(), os.Interrupt)
		defer jstop()
		job := base
		job.Input = input
		res, err := run(jctx, job)
		if res != nil {
			totalUSD += res.CostUSD
			totalCalls += res.LLMCalls
		}
		if *asJSON {
			enc := json.NewEncoder(os.Stdout)
			enc.SetIndent("", "  ")
			_ = enc.Encode(res)
		} else {
			printResult(res)
		}
		return err
	}

	if !*interact {
		if err := runJob(input); err != nil {
			fatal("%v", err)
		}
		return
	}

	fmt.Fprintln(os.Stderr, "Interactive mode. One input per line (end a line with \\ to continue it).")
	fmt.Fprintln(os.Stderr, "Ctrl-C cancels the running job; :q or Ctrl-D quits.")
	for {
		if strings.TrimSpace(input) != "" {
			if err := runJob(input); err != nil {
				progress("job ended: %v", err)
			}
			progress("session total: $%.4f over %d LLM calls (budget $%.2f per job)", totalUSD, totalCalls, *budget)
		}
		var ok bool
		input, ok = promptInput(stdin)
		if !ok {
			fmt.Fprintln(os.Stderr)
			return
		}
	}
}

// promptInput reads one (possibly \-continued) input; ok=false on EOF or :q.
func promptInput(rd *bufio.Reader) (string, bool) {
	var parts []string
	prompt := "\nprove> "
	for {
		fmt.Fprint(os.Stderr, prompt)
		line, err := rd.ReadString('\n')
		if err != nil && line == "" {
			return "", false
		}
		line = strings.TrimRight(line, "\r\n")
		if len(parts) == 0 {
			switch strings.TrimSpace(line) {
			case ":q", ":quit", "exit", "quit":
				return "", false
			}
		}
		if cont, found := strings.CutSuffix(line, "\\"); found {
			parts = append(parts, cont)
			prompt = "  ...> "
			continue
		}
		parts = append(parts, line)
		return strings.Join(parts, "\n"), true
	}
}

func readInput() (string, bool) {
	if flag.NArg() > 0 {
		return strings.Join(flag.Args(), " "), false
	}
	b, err := io.ReadAll(os.Stdin)
	if err != nil {
		fatal("reading stdin: %v", err)
	}
	return string(b), true
}

var start = time.Now()

func progress(format string, args ...any) {
	fmt.Fprintf(os.Stderr, "[%6.1fs] %s\n", time.Since(start).Seconds(), fmt.Sprintf(format, args...))
}

func printEvent(e pipeline.Event, verbose bool) {
	tag := ""
	if e.Stmt > 0 {
		tag = fmt.Sprintf("stmt_%d: ", e.Stmt)
	}
	switch e.Type {
	case pipeline.EvFormalized:
		s := e.Statement
		progress("%sformalized as  theorem %s %s", tag, s.Name, oneLine(s.Signature))
		progress("%s  reads back as: %s", tag, oneLine(s.BackTranslation))
	case pipeline.EvStatementError:
		progress("%sLean rejected statement: %s", tag, firstLine(e.Message))
	case pipeline.EvAttempt:
		a := e.Attempt
		status := "✗ " + strings.Join(a.ErrorKinds, ", ")
		switch {
		case a.Verified:
			status = "✓ verified"
		case len(a.ErrorKinds) == 1 && a.ErrorKinds[0] == "claims_false":
			status = "→ model says FALSE: " + oneLine(strings.TrimPrefix(strings.TrimSpace(a.Body), "FALSE"))
		}
		if a.Stage == "auto" {
			progress("%sautomation `%s` %s  (lean %s)", tag, a.Body, status, a.LeanTime.Round(time.Millisecond))
			break
		}
		what := "attempt"
		switch {
		case a.Disproof:
			what = "disproof attempt"
		case a.Plan:
			what = "outline"
		case a.Step != "":
			what = "step " + a.Step + " attempt"
		}
		if a.Stage != "" && !a.Plan {
			what = "[" + a.Stage + "] " + what
		}
		tools := ""
		if a.ToolCalls > 0 {
			tools = fmt.Sprintf(", %d tool calls", a.ToolCalls)
		}
		progress("%s%s %d.%d %s  (llm %s, %d thinking tok%s, lean %s, $%.4f)", tag, what, a.Session, a.N, status,
			a.LLMTime.Round(100*time.Millisecond), a.ReasoningTokens, tools, a.LeanTime.Round(time.Millisecond), a.CostUSD)
		if verbose && !a.Verified && a.Feedback != "" {
			fmt.Fprintln(os.Stderr, indent(a.Feedback, "           │ "))
		}
	case pipeline.EvProved:
		progress("%sPROVED", tag)
	case pipeline.EvFailed:
		progress("%sFAILED: %s", tag, e.Statement.Error)
	case pipeline.EvDisproved:
		progress("%sDISPROVED: %s", tag, e.Message)
	case pipeline.EvExplained:
		// shown in the final report
	case pipeline.EvStage, pipeline.EvAutomation, pipeline.EvThinking:
		progress("%s%s", tag, e.Message)
	case pipeline.EvVerifying:
		progress("%s%s...", tag, e.Message)
	case pipeline.EvVerified:
		progress("%sverified: %s", tag, e.Message)
	default:
		msg := e.Message
		if msg != "" {
			msg = ": " + firstLine(msg)
		}
		progress("%s%s%s", tag, e.Type, msg)
	}
}

func printResult(res *pipeline.Result) {
	if res == nil {
		return
	}
	fmt.Println()
	for _, s := range res.Statements {
		fmt.Printf("── %s [%s] ──\n%s\n", s.Name, s.Status, s.Text)
		if s.Signature != "" {
			fmt.Printf("\nLean:  theorem %s %s\nMeans: %s\n", s.Name, oneLine(s.Signature), oneLine(s.BackTranslation))
		}
		if len(s.FaithfulnessIssues) > 0 {
			fmt.Printf("\n⚠ The Lean statement may not match the text:\n%s\n", indent("- "+strings.Join(s.FaithfulnessIssues, "\n- "), "  "))
		}
		switch {
		case s.Status == pipeline.StatusDisproved && s.Counterexample != "":
			fmt.Printf("\nFALSE as formalized. Counterexample (found by testing):\n%s\n", indent(s.Counterexample, "  "))
		case s.Status == pipeline.StatusDisproved:
			fmt.Printf("\nFALSE as formalized. Lean-checked proof of the negation (theorem %s_false):\n%s\n", s.Name, indent(s.Proof, "  "))
		case s.Proof != "":
			fmt.Printf("\nProof:\n%s\n", indent(s.Proof, "  "))
		}
		if v := s.Verification; v != nil && v.OK {
			fmt.Printf("\nIndependently verified (kernel re-check; axioms: %s)\n", strings.Join(v.Axioms, ", "))
		}
		if s.Explanation != "" {
			fmt.Printf("\nExplanation:\n%s\n", indent(s.Explanation, "  "))
		}
		if s.Error != "" && s.Status != pipeline.StatusProved && s.Status != pipeline.StatusDisproved {
			fmt.Printf("\nError: %s\n", s.Error)
		}
		fmt.Println()
	}
	fmt.Printf("── Lean file ──\n%s\n", res.LeanFile)
	fmt.Printf("%s, $%.4f over %d LLM calls\n", res.Duration.Round(100*time.Millisecond), res.CostUSD, res.LLMCalls)
}

// terminalConfirm asks on the terminal, sharing the prompt's reader. If
// stdin carried the input, it reads answers from /dev/tty instead.
func terminalConfirm(stdin *bufio.Reader, stdinUsed bool) pipeline.ConfirmFunc {
	rd := stdin
	if stdinUsed {
		tty, err := os.Open("/dev/tty")
		if err != nil {
			fatal("-confirm needs a terminal: %v", err)
		}
		rd = bufio.NewReader(tty)
	}
	return func(ctx context.Context, p pipeline.Proposal) (pipeline.Decision, error) {
		fmt.Fprintf(os.Stderr, "\n  %s: %s\n  Lean:  theorem %s %s\n  Means: %s\n", p.Name, oneLine(p.Text), p.Name, oneLine(p.Signature), oneLine(p.BackTranslation))
		if p.Notes != "" {
			fmt.Fprintf(os.Stderr, "  Notes: %s\n", indent(p.Notes, "         ")[9:])
		}
		for _, is := range p.Issues {
			fmt.Fprintf(os.Stderr, "  ⚠ may differ: %s\n", is)
		}
		fmt.Fprint(os.Stderr, "  Prove this? [Enter=yes, n=skip, or type a correction]: ")
		line, err := rd.ReadString('\n')
		if err != nil && line == "" {
			return pipeline.Decision{}, err
		}
		switch ans := strings.TrimSpace(line); strings.ToLower(ans) {
		case "", "y", "yes":
			return pipeline.Decision{Accept: true}, nil
		case "n", "no":
			return pipeline.Decision{}, nil
		default:
			return pipeline.Decision{Correction: ans}, nil
		}
	}
}

// leanImports parses the -imports list and makes sure Harness (which
// provides #harness_axioms, needed to verify proofs) is imported.
func leanImports(list string) []string {
	var mods []string
	seen := map[string]bool{}
	for _, m := range strings.Split(list, ",") {
		if m = strings.TrimSpace(m); m != "" && !seen[m] {
			seen[m] = true
			mods = append(mods, m)
		}
	}
	if !seen["Harness"] {
		mods = append(mods, "Harness")
	}
	return mods
}

func oneLine(s string) string { return strings.Join(strings.Fields(s), " ") }

func firstLine(s string) string {
	s, _, _ = strings.Cut(strings.TrimSpace(s), "\n")
	return s
}

func indent(s, p string) string {
	ls := strings.Split(strings.TrimRight(s, "\n"), "\n")
	for i := range ls {
		ls[i] = p + ls[i]
	}
	return strings.Join(ls, "\n")
}

func fatal(format string, args ...any) {
	fmt.Fprintf(os.Stderr, "prove: "+format+"\n", args...)
	os.Exit(1)
}

// planAfterJob maps -plan-after to the job field, where 0 means "default":
// the flag's 0 (outline right away) becomes -1.
func planAfterJob(n int) int {
	if n <= 0 {
		return -1
	}
	return n
}

package main

import (
	"context"
	"errors"
	"fmt"
	"os"
	"os/signal"
	"strings"
	"syscall"
	"time"

	"mathprover/internal/daemon"
	"mathprover/internal/pipeline"
)

// runServe loads Lean once and serves jobs on socket until stopped
// (prove -stop, Ctrl-C or SIGTERM).
func runServe(socket string, ls leanSettings) {
	// Claim the socket before the slow Lean start, so a second -serve
	// fails at once instead of after minutes.
	ln, err := daemon.Listen(socket)
	if errors.Is(err, daemon.ErrRunning) {
		fatal("%v on %s (stop it with: prove -stop)", err, socket)
	}
	if err != nil {
		fatal("socket %s: %v", socket, err)
	}
	defer os.Remove(socket)

	ctx, stop := signal.NotifyContext(context.Background(), os.Interrupt, syscall.SIGTERM)
	defer stop()

	pv, err := startProver(ctx, ls)
	if err != nil {
		ln.Close()
		fatal("%v", err)
	}
	defer pv.Close()

	started := time.Now()
	srv := &daemon.Server{
		Handle: func(ctx context.Context, job daemon.Job, onEvent func(pipeline.Event)) (*pipeline.Result, error) {
			return pv.run(ctx, job, pipeline.Hooks{OnEvent: onEvent})
		},
		Info: func() daemon.Status {
			return daemon.Status{
				PID: os.Getpid(), Started: started, LeanDir: ls.Dir, Imports: ls.Imports,
				Workers: ls.Workers, Endpoint: pv.client.BaseURL,
			}
		},
		Log: progress,
	}
	progress("background prover ready on %s (stop with: prove -stop)", socket)
	if err := srv.Serve(ctx, ln); err != nil {
		fatal("serve: %v", err)
	}
	progress("background prover stopped")
}

func runStatus(socket string) {
	st, err := daemon.GetStatus(context.Background(), socket)
	if err != nil {
		fmt.Fprintf(os.Stderr, "no background prover running (%v)\n", err)
		os.Exit(1)
	}
	fmt.Printf("background prover on %s\n", socket)
	fmt.Printf("  pid        %d\n", st.PID)
	fmt.Printf("  up for     %s (since %s)\n", time.Since(st.Started).Round(time.Second), st.Started.Format("15:04:05"))
	fmt.Printf("  lean dir   %s (%d worker(s))\n", st.LeanDir, st.Workers)
	fmt.Printf("  imports    %s\n", strings.Join(st.Imports, ", "))
	fmt.Printf("  endpoint   %s\n", st.Endpoint)
	fmt.Printf("  jobs       %d done, %d running, %d LLM calls\n", st.JobsDone, st.JobsRunning, st.LLMCalls)
}

func runStop(socket string) {
	if err := daemon.StopServer(context.Background(), socket); err != nil {
		fmt.Fprintf(os.Stderr, "no background prover running (%v)\n", err)
		os.Exit(1)
	}
	fmt.Println("background prover stopped")
}

// remoteRunner sends jobs to the background prover; onEvent may be nil.
func remoteRunner(socket string, onEvent func(pipeline.Event)) runner {
	return func(ctx context.Context, job daemon.Job) (*pipeline.Result, error) {
		return daemon.Prove(ctx, socket, job, onEvent)
	}
}

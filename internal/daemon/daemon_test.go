package daemon

import (
	"context"
	"errors"
	"net"
	"os"
	"path/filepath"
	"strings"
	"testing"
	"time"

	"mathprover/internal/pipeline"
)

// startServer runs a Server with handler h on a temp socket.
func startServer(t *testing.T, h Handler) (sock string, srv *Server, done chan error) {
	t.Helper()
	sock = filepath.Join(t.TempDir(), "p.sock")
	ln, err := Listen(sock)
	if err != nil {
		t.Fatal(err)
	}
	srv = &Server{Handle: h, Info: func() Status { return Status{PID: 42, Imports: []string{"Mathlib.Tactic"}} }}
	done = make(chan error, 1)
	go func() { done <- srv.Serve(context.Background(), ln) }()
	t.Cleanup(func() {
		srv.Stop()
		select {
		case <-done:
		case <-time.After(5 * time.Second):
			t.Error("server did not stop")
		}
	})
	return sock, srv, done
}

func TestProveStreamsEventsAndResult(t *testing.T) {
	var got Job
	sock, _, _ := startServer(t, func(ctx context.Context, job Job, onEvent func(pipeline.Event)) (*pipeline.Result, error) {
		got = job
		onEvent(pipeline.Event{Type: pipeline.EvSplit, Message: "1 statement(s)"})
		onEvent(pipeline.Event{Type: pipeline.EvAttempt, Stmt: 1, Attempt: &pipeline.AttemptRecord{N: 1, Verified: true}})
		return &pipeline.Result{
			Statements: []*pipeline.StatementResult{{Index: 1, Name: "stmt_1", Status: pipeline.StatusProved, Proof: "omega"}},
			LeanFile:   strings.Repeat("x", 200_000), // bigger than a default scanner line
			LLMCalls:   3,
		}, nil
	})

	var events []pipeline.Event
	res, err := Prove(context.Background(), sock, Job{Input: "1+1=2", Model: "m", Attempts: 4, Timeout: time.Minute},
		func(e pipeline.Event) { events = append(events, e) })
	if err != nil {
		t.Fatal(err)
	}
	if got.Input != "1+1=2" || got.Model != "m" || got.Attempts != 4 || got.Timeout != time.Minute {
		t.Errorf("job not passed through: %+v", got)
	}
	if len(events) != 2 || events[0].Type != pipeline.EvSplit || !events[1].Attempt.Verified {
		t.Errorf("events = %+v", events)
	}
	if res == nil || len(res.Statements) != 1 || res.Statements[0].Proof != "omega" || len(res.LeanFile) != 200_000 {
		t.Fatalf("result = %+v", res)
	}
}

func TestProveReturnsErrorWithPartialResult(t *testing.T) {
	sock, _, _ := startServer(t, func(ctx context.Context, job Job, onEvent func(pipeline.Event)) (*pipeline.Result, error) {
		return &pipeline.Result{LLMCalls: 1}, errors.New("llm: budget exhausted")
	})
	res, err := Prove(context.Background(), sock, Job{Input: "x"}, nil)
	if err == nil || !strings.Contains(err.Error(), "budget") {
		t.Fatalf("err = %v", err)
	}
	if res == nil || res.LLMCalls != 1 {
		t.Errorf("partial result lost: %+v", res)
	}
}

func TestClientHangUpCancelsJob(t *testing.T) {
	started := make(chan struct{})
	canceled := make(chan struct{})
	sock, _, _ := startServer(t, func(ctx context.Context, job Job, onEvent func(pipeline.Event)) (*pipeline.Result, error) {
		close(started)
		<-ctx.Done()
		close(canceled)
		return nil, ctx.Err()
	})

	ctx, cancel := context.WithCancel(context.Background())
	errc := make(chan error, 1)
	go func() {
		_, err := Prove(ctx, sock, Job{Input: "x"}, nil)
		errc <- err
	}()
	<-started
	cancel() // like Ctrl-C in the client
	select {
	case <-canceled:
	case <-time.After(5 * time.Second):
		t.Fatal("job was not canceled after the client hung up")
	}
	if err := <-errc; !errors.Is(err, context.Canceled) {
		t.Errorf("client err = %v", err)
	}
}

func TestStatusCountsJobs(t *testing.T) {
	sock, _, _ := startServer(t, func(ctx context.Context, job Job, onEvent func(pipeline.Event)) (*pipeline.Result, error) {
		return &pipeline.Result{LLMCalls: 5}, nil
	})
	for range 2 {
		if _, err := Prove(context.Background(), sock, Job{Input: "x"}, nil); err != nil {
			t.Fatal(err)
		}
	}
	st, err := GetStatus(context.Background(), sock)
	if err != nil {
		t.Fatal(err)
	}
	if st.PID != 42 || st.JobsDone != 2 || st.JobsRunning != 0 || st.LLMCalls != 10 || st.Imports[0] != "Mathlib.Tactic" {
		t.Errorf("status = %+v", st)
	}
}

func TestStopEndsServeAndCancelsJobs(t *testing.T) {
	jobCanceled := make(chan struct{})
	started := make(chan struct{})
	sock, _, done := startServer(t, func(ctx context.Context, job Job, onEvent func(pipeline.Event)) (*pipeline.Result, error) {
		close(started)
		<-ctx.Done()
		close(jobCanceled)
		return nil, ctx.Err()
	})
	go func() { _, _ = Prove(context.Background(), sock, Job{Input: "x"}, nil) }()
	<-started

	if err := StopServer(context.Background(), sock); err != nil {
		t.Fatal(err)
	}
	select {
	case err := <-done:
		if err != nil {
			t.Errorf("Serve returned %v", err)
		}
		done <- nil // let the cleanup see it too
	case <-time.After(5 * time.Second):
		t.Fatal("Serve did not return after stop")
	}
	select {
	case <-jobCanceled:
	default:
		t.Error("running job was not canceled by stop")
	}
	if Available(sock) {
		t.Error("socket still answers after stop")
	}
}

func TestListenRefusesLiveAndReplacesStaleSocket(t *testing.T) {
	sock, _, _ := startServer(t, func(context.Context, Job, func(pipeline.Event)) (*pipeline.Result, error) {
		return nil, nil
	})
	if _, err := Listen(sock); !errors.Is(err, ErrRunning) {
		t.Errorf("second Listen on a live socket: err = %v, want ErrRunning", err)
	}

	// A socket file nobody listens on (crashed server) is replaced.
	stale := filepath.Join(t.TempDir(), "stale.sock")
	ln, err := net.Listen("unix", stale)
	if err != nil {
		t.Fatal(err)
	}
	ln.(*net.UnixListener).SetUnlinkOnClose(false)
	ln.Close()
	if _, err := os.Stat(stale); err != nil {
		t.Fatalf("stale socket file not left behind: %v", err)
	}
	ln2, err := Listen(stale)
	if err != nil {
		t.Fatalf("Listen over stale socket: %v", err)
	}
	ln2.Close()
}

func TestSocketIsPrivate(t *testing.T) {
	dir := filepath.Join(t.TempDir(), "q")
	sock := filepath.Join(dir, "p.sock")
	ln, err := Listen(sock)
	if err != nil {
		t.Fatal(err)
	}
	defer ln.Close()
	fi, err := os.Stat(sock)
	if err != nil {
		t.Fatal(err)
	}
	if fi.Mode().Perm() != 0o600 {
		t.Errorf("socket mode = %v, want 0600", fi.Mode().Perm())
	}
	di, _ := os.Stat(dir)
	if di.Mode().Perm() != 0o700 {
		t.Errorf("socket dir mode = %v, want 0700", di.Mode().Perm())
	}
}

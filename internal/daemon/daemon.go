// Package daemon keeps a warm prover (Lean with Mathlib already imported)
// running in the background and serves proof jobs over a Unix socket, so a
// `prove` call does not pay the multi-minute Mathlib import every time.
//
// Protocol: newline-delimited JSON over one connection per request. The
// client sends one Request line. For a job the server answers with any
// number of {"event": ...} lines and then one line with "final": true
// carrying the result (and an error message, if any). The client closing
// the connection cancels its job.
//
// The socket lives in the user's home directory with 0600 permissions, so
// only that user can submit jobs: the server never listens on the network.
package daemon

import (
	"bufio"
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"net"
	"os"
	"path/filepath"
	"sync"
	"time"

	"mathprover/internal/pipeline"
)

// Op names a request.
const (
	OpProve  = "prove"
	OpStatus = "status"
	OpStop   = "stop"
)

// Request is the single line a client sends.
type Request struct {
	Op  string `json:"op"`
	Job *Job   `json:"job,omitempty"`
}

// Job is one prove request with the per-job settings. Settings that need a
// restart (Lean imports, Lean project, LLM endpoint and key) are the
// server's own and are not part of a job.
type Job struct {
	Input     string `json:"input"`
	Model     string `json:"model,omitempty"`
	Effort    string `json:"effort,omitempty"` // a single stage at this effort; "" = the Stages ladder
	AuxModel  string `json:"aux_model,omitempty"`
	AuxEffort string `json:"aux_effort,omitempty"`
	Attempts  int    `json:"attempts,omitempty"`
	Parallel  int    `json:"parallel,omitempty"`
	NoSplit   bool   `json:"no_split,omitempty"`
	NoExplain bool   `json:"no_explain,omitempty"`
	// Stages names the proof-search ladder (pipeline.StagePresets; nil =
	// pipeline.DefaultStageNames); Attempts and Parallel, if > 0, override
	// every stage. NoAuto skips the automation tactics tried first.
	Stages []string `json:"stages,omitempty"`
	NoAuto bool     `json:"no_auto,omitempty"`
	// NoFaithCheck skips the formalization check; NoDisprove skips the
	// search for counterexamples and proofs of the negation.
	NoFaithCheck bool `json:"no_faith_check,omitempty"`
	NoDisprove   bool `json:"no_disprove,omitempty"`
	// NoPlan skips the proof-outline stage after direct attempts fail;
	// PlanAttempts and StepAttempts bound it (0 = defaults).
	NoPlan       bool `json:"no_plan,omitempty"`
	PlanAttempts int  `json:"plan_attempts,omitempty"`
	StepAttempts int  `json:"step_attempts,omitempty"`
	PlanAfter    int  `json:"plan_after,omitempty"` // direct attempts before the outline stage
	// BaseURL and APIKey, if set, send this job's LLM calls to another
	// OpenAI-compatible endpoint than the server's default (see
	// LLM_ENDPOINT_<NAME> in the README). The socket is private to the
	// user, so the key does not leave the machine.
	BaseURL   string        `json:"base_url,omitempty"`
	APIKey    string        `json:"api_key,omitempty"`
	BudgetUSD float64       `json:"budget_usd,omitempty"`
	Timeout   time.Duration `json:"timeout,omitempty"` // 0 = no limit
}

// Status describes a running server.
type Status struct {
	PID         int       `json:"pid"`
	Started     time.Time `json:"started"`
	LeanDir     string    `json:"lean_dir"`
	Imports     []string  `json:"imports"`
	Workers     int       `json:"workers"`
	Endpoint    string    `json:"endpoint"`
	JobsDone    int       `json:"jobs_done"`
	JobsRunning int       `json:"jobs_running"`
	LLMCalls    int       `json:"llm_calls"`
}

// message is one line the server sends.
type message struct {
	Event  *pipeline.Event  `json:"event,omitempty"`
	Final  bool             `json:"final,omitempty"`
	Result *pipeline.Result `json:"result,omitempty"`
	Status *Status          `json:"status,omitempty"`
	Error  string           `json:"error,omitempty"`
}

// Handler runs one job; onEvent must be called synchronously and quickly.
type Handler func(ctx context.Context, job Job, onEvent func(pipeline.Event)) (*pipeline.Result, error)

// ErrRunning is returned by Listen when another server owns the socket.
var ErrRunning = errors.New("a background prover is already running")

const maxRequest = 1 << 20 // bytes; a request is one statement list

// DefaultSocket is $PROVE_SOCKET or ~/.quod/prove.sock.
func DefaultSocket() string {
	if s := os.Getenv("PROVE_SOCKET"); s != "" {
		return s
	}
	home, err := os.UserHomeDir()
	if err != nil {
		return filepath.Join(os.TempDir(), "quod-prove.sock")
	}
	return filepath.Join(home, ".quod", "prove.sock")
}

// Listen creates the socket. A stale socket file left by a crashed server
// is removed; a live one makes Listen fail with ErrRunning.
func Listen(path string) (net.Listener, error) {
	if err := os.MkdirAll(filepath.Dir(path), 0o700); err != nil {
		return nil, err
	}
	if _, err := os.Stat(path); err == nil {
		if Available(path) {
			return nil, ErrRunning
		}
		if err := os.Remove(path); err != nil {
			return nil, fmt.Errorf("removing stale socket: %w", err)
		}
	}
	ln, err := net.Listen("unix", path)
	if err != nil {
		return nil, err
	}
	if err := os.Chmod(path, 0o600); err != nil {
		ln.Close()
		return nil, err
	}
	return ln, nil
}

// Server serves jobs from a Listener.
type Server struct {
	Handle Handler
	Info   func() Status // static part of Status; counters are filled in
	Log    func(format string, args ...any)

	mu       sync.Mutex
	running  int
	done     int
	calls    int
	stopOnce sync.Once
	stopped  chan struct{}
}

func (s *Server) init() {
	s.mu.Lock()
	if s.stopped == nil {
		s.stopped = make(chan struct{})
	}
	s.mu.Unlock()
}

// Stop makes Serve return; running jobs are canceled.
func (s *Server) Stop() {
	s.init()
	s.stopOnce.Do(func() { close(s.stopped) })
}

func (s *Server) logf(format string, args ...any) {
	if s.Log != nil {
		s.Log(format, args...)
	}
}

// Serve accepts connections until ctx is done or Stop is called, then
// cancels running jobs, waits for them and closes ln.
func (s *Server) Serve(ctx context.Context, ln net.Listener) error {
	s.init()
	sctx, cancel := context.WithCancel(ctx)
	defer cancel()
	go func() {
		select {
		case <-sctx.Done():
		case <-s.stopped:
		}
		cancel()
		ln.Close()
	}()

	var wg sync.WaitGroup
	defer wg.Wait()
	for {
		conn, err := ln.Accept()
		if err != nil {
			if sctx.Err() != nil {
				return nil
			}
			return err
		}
		wg.Add(1)
		go func() {
			defer wg.Done()
			s.serveConn(sctx, conn)
		}()
	}
}

func (s *Server) serveConn(ctx context.Context, conn net.Conn) {
	defer conn.Close()
	rd := bufio.NewReader(io.LimitReader(conn, maxRequest))
	line, err := rd.ReadBytes('\n')
	if err != nil && len(line) == 0 {
		return
	}
	var req Request
	if err := json.Unmarshal(line, &req); err != nil {
		writeMsg(conn, message{Final: true, Error: "bad request: " + err.Error()})
		return
	}
	switch req.Op {
	case OpStatus:
		st := s.status()
		writeMsg(conn, message{Final: true, Status: &st})
	case OpStop:
		writeMsg(conn, message{Final: true})
		s.logf("stop requested")
		s.Stop()
	case OpProve, "":
		if req.Job == nil {
			writeMsg(conn, message{Final: true, Error: "bad request: no job"})
			return
		}
		s.serveJob(ctx, conn, *req.Job)
	default:
		writeMsg(conn, message{Final: true, Error: "unknown op " + req.Op})
	}
}

func (s *Server) serveJob(ctx context.Context, conn net.Conn, job Job) {
	jctx, cancel := context.WithCancel(ctx)
	defer cancel()
	if job.Timeout > 0 {
		jctx, cancel = context.WithTimeout(jctx, job.Timeout)
		defer cancel()
	}
	// The client sends nothing after its request; a read returning means
	// it hung up (Ctrl-C, crash), so the job is abandoned.
	go func() {
		_, _ = io.Copy(io.Discard, conn)
		cancel()
	}()

	var wmu sync.Mutex
	send := func(m message) {
		wmu.Lock()
		defer wmu.Unlock()
		if writeMsg(conn, m) != nil {
			cancel()
		}
	}

	s.mu.Lock()
	s.running++
	s.mu.Unlock()
	t0 := time.Now()
	s.logf("job started: %.80q", job.Input)

	res, err := s.Handle(jctx, job, func(e pipeline.Event) { send(message{Event: &e}) })

	final := message{Final: true, Result: res}
	if err != nil {
		final.Error = err.Error()
	}
	send(final)

	s.mu.Lock()
	s.running--
	s.done++
	if res != nil {
		s.calls += res.LLMCalls
	}
	s.mu.Unlock()
	switch {
	case err != nil:
		s.logf("job ended after %s: %v", time.Since(t0).Round(100*time.Millisecond), err)
	case res != nil:
		s.logf("job done in %s: %s", time.Since(t0).Round(100*time.Millisecond), summary(res))
	}
}

func (s *Server) status() Status {
	var st Status
	if s.Info != nil {
		st = s.Info()
	}
	s.mu.Lock()
	st.JobsDone, st.JobsRunning, st.LLMCalls = s.done, s.running, s.calls
	s.mu.Unlock()
	return st
}

func summary(res *pipeline.Result) string {
	proved := 0
	for _, sr := range res.Statements {
		if sr.Status == pipeline.StatusProved {
			proved++
		}
	}
	return fmt.Sprintf("%d/%d proved", proved, len(res.Statements))
}

func writeMsg(w io.Writer, m message) error {
	b, err := json.Marshal(m)
	if err != nil {
		return err
	}
	_, err = w.Write(append(b, '\n'))
	return err
}

// --- client side ---------------------------------------------------------

func dial(path string) (net.Conn, error) {
	return net.DialTimeout("unix", path, 2*time.Second)
}

// Available reports whether a server answers on path.
func Available(path string) bool {
	c, err := dial(path)
	if err != nil {
		return false
	}
	c.Close()
	return true
}

// roundTrip sends req and returns each line to handle until a final line.
func roundTrip(ctx context.Context, path string, req Request, onEvent func(pipeline.Event)) (*message, error) {
	conn, err := dial(path)
	if err != nil {
		return nil, fmt.Errorf("background prover not reachable at %s: %w", path, err)
	}
	defer conn.Close()
	stop := context.AfterFunc(ctx, func() { conn.Close() }) // hang up = cancel the job
	defer stop()

	if err := writeMsgAny(conn, req); err != nil {
		return nil, err
	}
	sc := bufio.NewScanner(conn)
	sc.Buffer(make([]byte, 64<<10), 256<<20) // results carry whole Lean files
	for sc.Scan() {
		var m message
		if err := json.Unmarshal(sc.Bytes(), &m); err != nil {
			return nil, fmt.Errorf("bad reply from background prover: %w", err)
		}
		if m.Event != nil && onEvent != nil {
			onEvent(*m.Event)
		}
		if m.Final {
			return &m, nil
		}
	}
	if ctx.Err() != nil {
		return nil, ctx.Err()
	}
	if err := sc.Err(); err != nil {
		return nil, err
	}
	return nil, errors.New("background prover closed the connection (did it stop?)")
}

func writeMsgAny(w io.Writer, v any) error {
	b, err := json.Marshal(v)
	if err != nil {
		return err
	}
	_, err = w.Write(append(b, '\n'))
	return err
}

// Prove runs job on the server, calling onEvent for each progress event.
// Canceling ctx hangs up, which cancels the job on the server. Like
// pipeline.Run it may return a partial result together with an error.
func Prove(ctx context.Context, path string, job Job, onEvent func(pipeline.Event)) (*pipeline.Result, error) {
	m, err := roundTrip(ctx, path, Request{Op: OpProve, Job: &job}, onEvent)
	if err != nil {
		return nil, err
	}
	if m.Error != "" {
		return m.Result, errors.New(m.Error)
	}
	return m.Result, nil
}

// GetStatus asks the server for its status.
func GetStatus(ctx context.Context, path string) (*Status, error) {
	m, err := roundTrip(ctx, path, Request{Op: OpStatus}, nil)
	if err != nil {
		return nil, err
	}
	if m.Status == nil {
		return nil, errors.New("no status in reply: " + m.Error)
	}
	return m.Status, nil
}

// StopServer asks the server to exit; running jobs are canceled.
func StopServer(ctx context.Context, path string) error {
	m, err := roundTrip(ctx, path, Request{Op: OpStop}, nil)
	if err != nil {
		return err
	}
	if m.Error != "" {
		return errors.New(m.Error)
	}
	return nil
}

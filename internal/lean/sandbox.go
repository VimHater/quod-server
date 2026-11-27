package lean

import (
	"errors"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strconv"
	"strings"
)

// SandboxKind selects how a REPL process is isolated.
type SandboxKind string

const (
	// SandboxNone runs the REPL directly (trusted input only).
	SandboxNone SandboxKind = "none"
	// SandboxBwrap runs the REPL under bubblewrap: fresh user/pid/net/ipc/uts
	// namespaces, toolchain and project mounted read-only, private /tmp,
	// nothing else from the host filesystem except /usr.
	SandboxBwrap SandboxKind = "bwrap"
)

// Sandbox configures process isolation and resource limits for REPLs.
//
// Model-written Lean can execute code at elaboration time (#eval, custom
// elaborators, unsafe), so every REPL must be treated as running hostile
// code. The sandbox ensures such code cannot read secrets or host files,
// cannot write anything that outlives the process (the project is
// read-only, /tmp is a private tmpfs), has no network, and is confined to
// its own memory/task budget so it cannot starve the server or other jobs.
type Sandbox struct {
	Kind SandboxKind
	// Limits apply via a transient systemd user scope (cgroup v2). Empty
	// MemoryMax and zero TasksMax mean no limits (and no systemd-run).
	MemoryMax string // e.g. "10G"; includes page cache of mapped .olean files
	TasksMax  int    // processes + threads; Lean's thread pool needs ~nproc+16
	// ExtraReadOnly are additional host paths mounted read-only.
	ExtraReadOnly []string
}

// DefaultSandbox is bubblewrap with limits sized for one Mathlib REPL.
func DefaultSandbox() Sandbox {
	return Sandbox{Kind: SandboxBwrap, MemoryMax: "10G", TasksMax: 256}
}

func (s Sandbox) usesSystemd() bool { return s.MemoryMax != "" || s.TasksMax > 0 }

// Check verifies the required tools work on this host.
func (s Sandbox) Check() error {
	if s.Kind == SandboxNone || s.Kind == "" {
		return nil
	}
	if s.Kind != SandboxBwrap {
		return fmt.Errorf("lean: unknown sandbox %q", s.Kind)
	}
	// Same root layout as the real sandbox: hard-coding Arch's symlinks
	// (/lib64 -> usr/lib) breaks Debian/Ubuntu, whose loader is only under
	// /usr/lib64, and every exec then fails with ENOENT.
	args := append([]string{"--unshare-all", "--ro-bind", "/usr", "/usr"}, rootDirArgs()...)
	args = append(args, "--", "/usr/bin/true")
	if out, err := exec.Command("bwrap", args...).CombinedOutput(); err != nil {
		return fmt.Errorf("lean: bubblewrap unusable (install bubblewrap; unprivileged user namespaces must be enabled): %v: %s", err, strings.TrimSpace(string(out)))
	}
	if s.usesSystemd() {
		if out, err := exec.Command("systemd-run", "--user", "--scope", "--quiet", "--collect", "--", "true").CombinedOutput(); err != nil {
			return fmt.Errorf("lean: systemd user scopes unusable for resource limits (need a systemd user session; `loginctl enable-linger $USER` on servers): %v: %s", err, strings.TrimSpace(string(out)))
		}
	}
	return nil
}

// command builds argv for running the REPL binary inside the sandbox, and
// the environment for the outermost process. cfg.Env must be scrubbed.
func (s Sandbox) command(cfg Config, bin string) (argv, env []string, err error) {
	return s.wrap(cfg, cfg.Env, cfg.ProjectDir, nil, []string{bin})
}

// mount is an extra host directory made visible inside the sandbox at the
// same path.
type mount struct {
	path     string
	writable bool
}

// wrap builds argv for running inner (argv[0] = absolute binary path) in
// the sandbox with the given environment, working directory and extra
// mounts, plus the environment for the outermost process.
//
// Without a sandbox the command gets innerEnv directly. With bwrap, the
// launcher (systemd-run/bwrap) gets only what it needs to reach the user's
// systemd instance, and bwrap clears the environment and sets innerEnv for
// the sandboxed process, so nothing else from the host passes through.
func (s Sandbox) wrap(cfg Config, innerEnv []string, cwd string, mounts []mount, inner []string) (argv, env []string, err error) {
	if s.Kind == SandboxNone || s.Kind == "" {
		return inner, innerEnv, nil
	}
	if s.Kind != SandboxBwrap {
		return nil, nil, fmt.Errorf("lean: unknown sandbox %q", s.Kind)
	}
	sysroot := envValue(innerEnv, "LEAN_SYSROOT")
	if sysroot == "" {
		return nil, nil, errors.New("lean: LEAN_SYSROOT missing from environment; cannot sandbox")
	}
	env = []string{"PATH=/usr/bin:/bin"}
	for _, k := range []string{"XDG_RUNTIME_DIR", "DBUS_SESSION_BUS_ADDRESS"} {
		if v, ok := os.LookupEnv(k); ok {
			env = append(env, k+"="+v)
		}
	}

	if s.usesSystemd() {
		// --scope execs the command in place, so our child PID is bwrap.
		argv = append(argv, "systemd-run", "--user", "--scope", "--quiet", "--collect")
		if s.MemoryMax != "" {
			argv = append(argv, "-p", "MemoryMax="+s.MemoryMax, "-p", "MemorySwapMax=0")
		}
		if s.TasksMax > 0 {
			argv = append(argv, "-p", "TasksMax="+strconv.Itoa(s.TasksMax))
		}
		argv = append(argv, "--")
	}
	argv = append(argv,
		"bwrap",
		"--unshare-all",     // user, pid, net, ipc, uts, cgroup namespaces
		"--die-with-parent", // the sandboxed process dies when bwrap (or the server) dies
		"--new-session",     // no access to the controlling terminal
		"--cap-drop", "ALL",
		"--ro-bind", "/usr", "/usr",
		"--proc", "/proc",
		"--dev", "/dev",
		"--tmpfs", "/tmp", // private, empty, gone with the process
		"--clearenv",
	)
	for _, kv := range innerEnv {
		if k, v, ok := strings.Cut(kv, "="); ok {
			argv = append(argv, "--setenv", k, v)
		}
	}
	argv = append(argv, rootDirArgs()...)
	for _, f := range []string{"/etc/ld.so.cache", "/etc/localtime"} {
		argv = append(argv, "--ro-bind-try", f, f)
	}
	ro := append([]string{sysroot, cfg.ProjectDir}, s.ExtraReadOnly...)
	for _, p := range ro {
		argv = append(argv, "--ro-bind", p, p)
	}
	// Extra mounts come last so they appear on top of the /tmp tmpfs.
	for _, m := range mounts {
		flag := "--ro-bind"
		if m.writable {
			flag = "--bind"
		}
		argv = append(argv, flag, m.path, m.path)
	}
	argv = append(argv, "--chdir", cwd, "--")
	argv = append(argv, inner...)
	return argv, env, nil
}

// rootDirArgs recreates the host's merged-/usr symlinks (/bin, /lib64, ...
// pointing into /usr, whatever the distribution's layout) or binds the real
// directories read-only.
func rootDirArgs() []string {
	var args []string
	for _, d := range []string{"/bin", "/sbin", "/lib", "/lib64"} {
		fi, err := os.Lstat(d)
		switch {
		case err != nil:
			continue
		case fi.Mode()&os.ModeSymlink != 0:
			if target, err := os.Readlink(d); err == nil {
				args = append(args, "--symlink", target, d)
			}
		default:
			args = append(args, "--ro-bind", d, d)
		}
	}
	return args
}

// ScrubEnv keeps only what the REPL needs, so secrets in the server's
// environment (API keys, tokens) never reach Lean. LD_LIBRARY_PATH and
// PATH are restricted to the toolchain.
func ScrubEnv(env []string) []string {
	sysroot := envValue(env, "LEAN_SYSROOT")
	out := []string{"HOME=/tmp", "LANG=C.UTF-8", "TMPDIR=/tmp"}
	for _, k := range []string{"LEAN_PATH", "LEAN_SYSROOT", "LEAN_SRC_PATH", "LEAN", "LEAN_GITHASH"} {
		if v := envValue(env, k); v != "" {
			out = append(out, k+"="+v)
		}
	}
	if sysroot != "" {
		out = append(out,
			"PATH="+filepath.Join(sysroot, "bin")+":/usr/bin",
			"LD_LIBRARY_PATH="+filepath.Join(sysroot, "lib", "lean")+":"+filepath.Join(sysroot, "lib"),
		)
	} else {
		out = append(out, "PATH=/usr/bin")
	}
	return out
}

func envValue(env []string, key string) string {
	for i := len(env) - 1; i >= 0; i-- { // last wins, like the OS
		if v, ok := strings.CutPrefix(env[i], key+"="); ok {
			return v
		}
	}
	return ""
}

// treeRSS sums the resident memory of pid and its descendants (Linux).
// Under a sandbox the direct child is bwrap/systemd-run, not the REPL.
func treeRSS(pid int) int64 {
	var total int64
	seen := map[int]bool{}
	var walk func(int)
	walk = func(p int) {
		if seen[p] {
			return
		}
		seen[p] = true
		total += procRSS(p)
		tasks, _ := filepath.Glob(fmt.Sprintf("/proc/%d/task/*/children", p))
		for _, t := range tasks {
			b, err := os.ReadFile(t)
			if err != nil {
				continue
			}
			for _, f := range strings.Fields(string(b)) {
				if c, err := strconv.Atoi(f); err == nil {
					walk(c)
				}
			}
		}
	}
	walk(pid)
	return total
}

func procRSS(pid int) int64 {
	b, err := os.ReadFile(fmt.Sprintf("/proc/%d/status", pid))
	if err != nil {
		return 0
	}
	for _, line := range strings.Split(string(b), "\n") {
		if rest, ok := strings.CutPrefix(line, "VmRSS:"); ok {
			if f := strings.Fields(rest); len(f) >= 1 {
				kb, _ := strconv.ParseInt(f[0], 10, 64)
				return kb * 1024
			}
		}
	}
	return 0
}

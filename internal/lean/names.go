package lean

import (
	"bufio"
	"context"
	"errors"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"sort"
	"strconv"
	"strings"
	"time"
)

// NameIndex answers "did you mean ...?" for identifiers Lean did not know,
// over the declaration names of an environment (see DumpNames).
type NameIndex struct {
	names []string
	set   map[string]struct{}
}

// Auto-generated declarations (equation lemmas, matchers, recursors, ...)
// are never what a proof author means; leave them out of suggestions.
var reGenerated = regexp.MustCompile(`\.(eq_\d+|eq_def|proof_\d+|match_\d+|_[A-Za-z0-9_]+|rec|recOn|casesOn|brecOn|binductionOn|below|ibelow|noConfusion|noConfusionType|injEq|inj|sizeOf_spec|ctorIdx|toCtorIdx)$|\.mk\.|^_`)

// NewNameIndex builds an index; generated names are dropped.
func NewNameIndex(names []string) *NameIndex {
	x := &NameIndex{set: make(map[string]struct{}, len(names))}
	for _, n := range names {
		n = strings.TrimSpace(n)
		if n == "" || reGenerated.MatchString(n) {
			continue
		}
		if _, dup := x.set[n]; dup {
			continue
		}
		x.set[n] = struct{}{}
		x.names = append(x.names, n)
	}
	return x
}

// LoadNameIndex reads a file written by DumpNames.
func LoadNameIndex(path string) (*NameIndex, error) {
	f, err := os.Open(path)
	if err != nil {
		return nil, err
	}
	defer f.Close()
	var names []string
	sc := bufio.NewScanner(f)
	sc.Buffer(make([]byte, 64<<10), 1<<20)
	for sc.Scan() {
		names = append(names, sc.Text())
	}
	if err := sc.Err(); err != nil {
		return nil, err
	}
	return NewNameIndex(names), nil
}

// Len is the number of indexed names.
func (x *NameIndex) Len() int { return len(x.names) }

// Has reports whether name exists.
func (x *NameIndex) Has(name string) bool {
	_, ok := x.set[strings.TrimPrefix(name, "_root_.")]
	return ok
}

// Similar returns up to k existing names close to query, best first.
// Same last component in another namespace ranks highest (the usual
// mistake: right lemma, wrong namespace), then names sharing most of the
// underscore-separated words, then small spelling differences.
func (x *NameIndex) Similar(query string, k int) []string {
	q := strings.TrimPrefix(query, "_root_.")
	qNS, qLast := splitName(q)
	qTok := tokens(qLast)
	qLow := strings.ToLower(qLast)

	type cand struct {
		name  string
		score float64
	}
	var best []cand
	worst := -1.0
	for _, n := range x.names {
		if n == q {
			continue
		}
		ns, last := splitName(n)
		var score float64
		if last == qLast {
			score = 100
		} else {
			shared, union := overlap(qTok, tokens(last))
			low := strings.ToLower(last)
			lenDiff := abs(len(low) - len(qLow))
			if shared == 0 && lenDiff > 3 {
				continue
			}
			jacc := float64(shared) / float64(max(union, 1))
			lev := 1.0
			if lenDiff <= max(4, len(qLow)/2) {
				lev = float64(levenshtein(qLow, low)) / float64(max(len(qLow), len(low), 1))
			}
			score = 55*jacc + 45*(1-lev)
			if score < 40 {
				continue
			}
		}
		switch {
		case qNS != "" && ns == qNS:
			score += 8
		case qNS != "" && (strings.HasSuffix(ns, "."+qNS) || strings.HasSuffix(qNS, "."+ns)):
			score += 4
		}
		score -= float64(strings.Count(n, ".")) * 0.5 // prefer shallower names on ties
		if len(best) == k && score <= worst {
			continue
		}
		best = append(best, cand{n, score})
		sort.SliceStable(best, func(i, j int) bool { return best[i].score > best[j].score })
		if len(best) > k {
			best = best[:k]
		}
		worst = best[len(best)-1].score
	}
	out := make([]string, len(best))
	for i, c := range best {
		out[i] = c.name
	}
	return out
}

func splitName(n string) (ns, last string) {
	if i := strings.LastIndexByte(n, '.'); i >= 0 {
		return n[:i], n[i+1:]
	}
	return "", n
}

func tokens(s string) []string {
	var out []string
	for _, t := range strings.FieldsFunc(strings.ToLower(s), func(r rune) bool { return r == '_' || r == '\'' }) {
		out = append(out, t)
	}
	return out
}

func overlap(a, b []string) (shared, union int) {
	seen := map[string]int{}
	for _, t := range a {
		seen[t] |= 1
	}
	for _, t := range b {
		seen[t] |= 2
	}
	for _, v := range seen {
		if v == 3 {
			shared++
		}
	}
	return shared, len(seen)
}

func levenshtein(a, b string) int {
	ra, rb := []rune(a), []rune(b)
	prev := make([]int, len(rb)+1)
	cur := make([]int, len(rb)+1)
	for j := range prev {
		prev[j] = j
	}
	for i := 1; i <= len(ra); i++ {
		cur[0] = i
		for j := 1; j <= len(rb); j++ {
			cost := 1
			if ra[i-1] == rb[j-1] {
				cost = 0
			}
			cur[j] = min(prev[j]+1, cur[j-1]+1, prev[j-1]+cost)
		}
		prev, cur = cur, prev
	}
	return prev[len(rb)]
}

func abs(x int) int {
	if x < 0 {
		return -x
	}
	return x
}

var reUnknownName = regexp.MustCompile("(?i)unknown (?:identifier|constant|declaration)\\s*[`'«]([^`'»\\s]+)[`'»]")

// UnknownIdents extracts the identifiers from "unknown identifier"
// diagnostics, in order, without duplicates (at most 3).
func UnknownIdents(ds []Diagnostic) []string {
	var out []string
	seen := map[string]bool{}
	for _, d := range ds {
		if d.Kind != KindUnknownIdent {
			continue
		}
		m := reUnknownName.FindStringSubmatch(d.Data)
		if m == nil || seen[m[1]] {
			continue
		}
		seen[m[1]] = true
		out = append(out, m[1])
		if len(out) == 3 {
			break
		}
	}
	return out
}

// DumpNames writes every declaration name available after importing
// cfg.Imports to path, using Harness's #harness_dump_names, and returns
// how many there are.
//
// It runs a fresh one-shot `lean` process, like the Verifier: inside the
// sandbox the REPL workers cannot write files the server could read (their
// /tmp is private and the project is read-only), so this process gets its
// own temporary directory, the only writable path, and the list is copied
// out of it. Only server-written code runs here.
func DumpNames(ctx context.Context, cfg Config, path string) (int, error) {
	cfg = cfg.withDefaults()
	if err := cfg.Sandbox.Check(); err != nil {
		return 0, err
	}
	if cfg.Env == nil {
		env, err := ResolveEnv(ctx, cfg.ProjectDir)
		if err != nil {
			return 0, err
		}
		cfg.Env = env
	}
	cfg.Env = ScrubEnv(cfg.Env)
	sysroot := envValue(cfg.Env, "LEAN_SYSROOT")
	if sysroot == "" {
		return 0, errors.New("lean: LEAN_SYSROOT missing from environment")
	}

	dir, err := os.MkdirTemp("", "quod-names-")
	if err != nil {
		return 0, err
	}
	defer os.RemoveAll(dir)
	out := filepath.Join(dir, "names.txt")
	var src strings.Builder
	for _, m := range cfg.Imports {
		fmt.Fprintf(&src, "import %s\n", m)
	}
	fmt.Fprintf(&src, "\n#harness_dump_names %q\n", out)
	file := filepath.Join(dir, "DumpNames.lean")
	if err := os.WriteFile(file, []byte(src.String()), 0o600); err != nil {
		return 0, err
	}

	argv, env, err := cfg.Sandbox.wrap(cfg, cfg.Env, dir, []mount{{path: dir, writable: true}},
		[]string{filepath.Join(sysroot, "bin", "lean"), file})
	if err != nil {
		return 0, err
	}
	ctx, cancel := context.WithTimeout(ctx, cfg.StartTimeout)
	defer cancel()
	cmd := exec.CommandContext(ctx, argv[0], argv[1:]...)
	cmd.Dir = dir
	cmd.Env = env
	cmd.WaitDelay = 5 * time.Second
	b, runErr := cmd.CombinedOutput()
	if ctx.Err() != nil {
		return 0, fmt.Errorf("lean: dumping names: %w", ctx.Err())
	}
	m := reNamesOK.FindSubmatch(b)
	if m == nil {
		if runErr != nil {
			return 0, fmt.Errorf("lean: dumping names: %v: %s", runErr, tail(string(b), 1000))
		}
		return 0, fmt.Errorf("#harness_dump_names gave no result (is Harness rebuilt?): %s", tail(string(b), 1000))
	}
	n, _ := strconv.Atoi(string(m[1]))
	data, err := os.ReadFile(out)
	if err != nil {
		return 0, err
	}
	if err := os.WriteFile(path, data, 0o600); err != nil {
		return 0, err
	}
	return n, nil
}

var reNamesOK = regexp.MustCompile(`HARNESS_NAMES_OK (\d+)`)

// SignaturesCode is the Lean code Signatures runs: one #check per name.
func SignaturesCode(names []string) string {
	var b strings.Builder
	for _, n := range names {
		fmt.Fprintf(&b, "#check %s\n", n)
	}
	return b.String()
}

// Signatures returns `#check` output ("name {args} : type") per name.
// query runs read-only code on the job's worker (pipeline.Checker.Query).
func Signatures(names []string, query func(code string) (*Result, error)) (map[string]string, error) {
	res, err := query(SignaturesCode(names))
	if err != nil {
		return nil, err
	}
	out := map[string]string{}
	for _, m := range res.Messages {
		if i := m.Pos.Line - 1; m.Severity == "info" && i >= 0 && i < len(names) {
			out[names[i]] = strings.Join(strings.Fields(m.Data), " ")
		}
	}
	return out, nil
}

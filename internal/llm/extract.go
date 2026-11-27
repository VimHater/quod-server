package llm

import (
	"regexp"
	"strings"
	"unicode/utf8"
)

var (
	reFence      = regexp.MustCompile("(?s)```[ \t]*([A-Za-z0-9_+-]*)[ \t]*\n(.*?)\n?```")
	reTheoremHdr = regexp.MustCompile(`^\s*(?:theorem|lemma)\s+[^\s:(\[{]+\s*`)
	reSorryTail  = regexp.MustCompile(`(?s):=\s*(?:by\s*)?(?:sorry)?\s*$`)
	reByStart    = regexp.MustCompile(`(?s)^.*?:=\s*by\b`)
)

// CodeBlocks returns the bodies of fenced code blocks, preferring blocks
// tagged lean/lean4 when any exist.
func CodeBlocks(text string) []string {
	var lean, other []string
	for _, m := range reFence.FindAllStringSubmatch(text, -1) {
		lang := strings.ToLower(m[1])
		if lang == "lean" || lang == "lean4" {
			lean = append(lean, m[2])
		} else {
			other = append(other, m[2])
		}
	}
	if len(lean) > 0 {
		return lean
	}
	return other
}

// lastBlock returns the last code block, or the whole text if there is none.
func lastBlock(text string) string {
	bs := CodeBlocks(text)
	if len(bs) == 0 {
		return trimBlankLines(text)
	}
	return trimBlankLines(bs[len(bs)-1])
}

// ExtractProofBody pulls the tactic script out of a prover reply. If the
// model restated the theorem anyway, everything up to `:= by` is dropped.
func ExtractProofBody(reply string) string {
	code := lastBlock(reply)
	if reTheoremHdr.MatchString(firstCodeLine(code)) {
		if loc := reByStart.FindStringIndex(code); loc != nil {
			code = code[loc[1]:]
		}
	}
	// Keep indentation: lean.NormalizeBody dedents using every line.
	return trimBlankLines(code)
}

// ExtractSignature pulls `<binders> : <prop>` out of a formalizer reply of
// the form ```lean theorem NAME <binders> : <prop> := by sorry```. Lines
// before the theorem (imports, opens) are dropped; ok is false if no
// theorem header was found.
func ExtractSignature(reply string) (sig string, ok bool) {
	code := lastBlock(reply)
	lines := strings.Split(code, "\n")
	start := -1
	for i, l := range lines {
		if reTheoremHdr.MatchString(l) {
			start = i
			break
		}
	}
	if start < 0 {
		return "", false
	}
	code = strings.Join(lines[start:], "\n")
	code = reTheoremHdr.ReplaceAllString(code, "")
	code = reSorryTail.ReplaceAllString(code, "")
	return strings.TrimSpace(code), true
}

// ClaimsFalse reports whether a prover reply (or the body extracted from it)
// says the theorem is false instead of proving it: a first line FALSE,
// optionally followed by punctuation and a reason.
func ClaimsFalse(reply string) bool {
	first := strings.TrimSpace(firstCodeLine(reply))
	first = strings.Trim(first, "*`_ ")
	rest, ok := strings.CutPrefix(first, "FALSE")
	if !ok {
		return false
	}
	rest = strings.TrimSpace(rest)
	if rest == "" {
		return true
	}
	r, _ := utf8.DecodeRuneInString(rest)
	return strings.ContainsRune(".:-—–(,", r)
}

// Notes returns the reply text outside code blocks.
func Notes(reply string) string {
	return strings.TrimSpace(reFence.ReplaceAllString(reply, ""))
}

func firstCodeLine(code string) string {
	for _, l := range strings.Split(code, "\n") {
		t := strings.TrimSpace(l)
		if t != "" && !strings.HasPrefix(t, "--") {
			return t
		}
	}
	return ""
}

// trimBlankLines removes leading/trailing blank lines but keeps the
// indentation of the first non-blank line.
func trimBlankLines(s string) string {
	lines := strings.Split(strings.ReplaceAll(s, "\r\n", "\n"), "\n")
	for len(lines) > 0 && strings.TrimSpace(lines[0]) == "" {
		lines = lines[1:]
	}
	for len(lines) > 0 && strings.TrimSpace(lines[len(lines)-1]) == "" {
		lines = lines[:len(lines)-1]
	}
	return strings.Join(lines, "\n")
}

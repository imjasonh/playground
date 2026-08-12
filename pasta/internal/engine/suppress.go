package engine

import (
	"fmt"
	"regexp"
	"sort"
	"strings"

	"github.com/imjasonh/pasta/internal/dsl"
	"github.com/imjasonh/pasta/internal/effect"
	"github.com/imjasonh/pasta/internal/tsutil"
)

// unusedIgnoreRule is the synthetic rule id on diagnostics emitted when
// a `pasta:ignore` names a finding that never occurred on that line
// (or a bare ignore suppressed nothing). Severity is always warning so
// `-fail-on=warning` turns stale suppressions into CI failures.
const unusedIgnoreRule = "unused_ignore"

// suppression records the rules disabled on a single source line via a
// `pasta:ignore` directive. all=true means every rule is suppressed
// (`// pasta:ignore` with no rule list); otherwise only the names in
// rules are suppressed.
//
// usedAll / usedRules track whether a match on this line was actually
// suppressed during the run — unusedIgnoreDiagnostics turns leftovers
// into warnings.
type suppression struct {
	all   bool
	rules map[string]bool

	// Byte range covering the pasta:ignore directive(s) on this line,
	// used as the diagnostic anchor for unused-ignore warnings.
	start, end uint32

	usedAll   bool
	usedRules map[string]bool
}

// directiveRe matches the `pasta:ignore` token itself (no tail). We
// use FindAll positions and slice the tail manually — that way two
// directives on the same line (`// pasta:ignore foo pasta:ignore bar`)
// each get their own tail, instead of the first match greedily
// consuming the rest of the line and leaking the literal words
// `pasta` and `ignore` into the rule-name list.
//
// No comment-leader requirement: callers only invoke us against text
// already known to be a comment (per the language's `comment_types`),
// so a string literal like
// `log("user typed pasta:ignore go_iferr")` can never reach us.
var directiveRe = regexp.MustCompile(`pasta:ignore\b`)

// nameRe matches an identifier — used to pluck rule names from a
// directive's tail, which is a comma- or whitespace-separated list.
// Junk like comment terminators (`*/`, `-->`) is naturally filtered
// out because it doesn't match the identifier pattern.
var nameRe = regexp.MustCompile(`[A-Za-z_][A-Za-z0-9_]*`)

// parseSuppressions walks the parsed tree and returns a map from
// 1-based source line number to the rules suppressed on that line by
// a `pasta:ignore` directive. Only nodes whose Type() is in
// commentTypes are scanned, so the directive can never fire from
// inside a string literal, regex, or other source text — eliminating
// the obvious false-positive class of a plain text scanner.
//
// Forms recognized:
//
//	x := foo() // pasta:ignore                  — suppress every rule on this line
//	x := foo() // pasta:ignore go_iferr         — suppress one rule
//	x := foo() // pasta:ignore go_iferr, go_negcmp  — suppress several
//
// In a multi-line block comment the directive applies to whichever
// line the directive itself sits on, not to the whole comment range.
//
// Suppression skips both the diagnostic and the rewrite for matching
// matches; fact emission still happens, since facts are internal
// state and dropping them would change other rules' behavior in
// surprising ways.
//
// Returns nil when the tree has no root, the language declares no
// comment types, or no directives are found — `markSuppressed` handles
// the nil case.
func parseSuppressions(root tsutil.Node, commentTypes map[string]bool) map[int]suppression {
	if !root.IsValid() || len(commentTypes) == 0 {
		return nil
	}
	var out map[int]suppression
	tsutil.Walk(root, func(n tsutil.Node) bool {
		if !commentTypes[n.Type()] {
			return true
		}
		scanComment(n, &out)
		// A comment's named children (if any) cannot themselves be
		// comments under any grammar we ship, but skipping descent
		// is the defensive choice — guarantees we never double-
		// scan the same span.
		return false
	})
	return out
}

func scanComment(n tsutil.Node, out *map[int]suppression) {
	text := n.Text()
	starts := directiveSpans(text)
	for i, m := range starts {
		// Tail runs from the end of THIS directive to the start of
		// the NEXT one, capped at the next newline. Slicing this
		// way (instead of letting the regex's `.*` greedily eat
		// the rest of the line) prevents a second `pasta:ignore`
		// on the same line from being parsed as rule names.
		tailStart := m[1]
		tailEnd := len(text)
		if i+1 < len(starts) {
			tailEnd = starts[i+1][0]
		}
		if nl := strings.IndexByte(text[tailStart:tailEnd], '\n'); nl >= 0 {
			tailEnd = tailStart + nl
		}
		// Truncate before a nested comment leader so testdata markers
		// like `# pasta:ignore foo # want "…"` don't treat `want` as
		// a rule name. The byte anchor still covers only the
		// directive + rule list.
		tail := text[tailStart:tailEnd]
		if stop := indexTailStop(tail); stop >= 0 {
			tailEnd = tailStart + stop
			tail = text[tailStart:tailEnd]
		}
		line := effect.ComputeLine(n.Src, n.StartByte()+uint32(m[0]))
		s := parseSuppressionTail(tail)
		s.start = n.StartByte() + uint32(m[0])
		s.end = n.StartByte() + uint32(tailEnd)
		// Trim trailing whitespace from the end anchor so the
		// diagnostic points at the directive / rule list, not the
		// padding before a following comment or newline.
		for s.end > s.start && isSpace(n.Src[s.end-1]) {
			s.end--
		}
		addSuppression(out, line, s)
	}
}

// directiveSpans returns [start,end) indexes of `pasta:ignore` tokens
// that are not inside double-quoted regions of the comment. That way a
// `# want "unused pasta:ignore"` marker cannot itself become a
// suppression directive.
func directiveSpans(text string) [][]int {
	all := directiveRe.FindAllStringIndex(text, -1)
	if len(all) == 0 {
		return nil
	}
	out := make([][]int, 0, len(all))
	for _, m := range all {
		if inDoubleQuotes(text, m[0]) {
			continue
		}
		out = append(out, m)
	}
	return out
}

// inDoubleQuotes reports whether offset sits inside a "…" region of s,
// using a simple backslash-aware scan (good enough for want markers
// and ordinary comment prose).
func inDoubleQuotes(s string, offset int) bool {
	in := false
	esc := false
	for i := 0; i < offset && i < len(s); i++ {
		c := s[i]
		if esc {
			esc = false
			continue
		}
		if in && c == '\\' {
			esc = true
			continue
		}
		if c == '"' {
			in = !in
		}
	}
	return in
}

// indexTailStop returns the index of a nested comment leader inside a
// directive tail, or -1 if none. Leaders recognized: //, #, --, <!--.
func indexTailStop(tail string) int {
	stop := -1
	consider := func(i int) {
		if i >= 0 && (stop < 0 || i < stop) {
			stop = i
		}
	}
	consider(strings.Index(tail, "//"))
	consider(strings.Index(tail, "#"))
	consider(strings.Index(tail, "--"))
	consider(strings.Index(tail, "<!--"))
	return stop
}

func isSpace(b byte) bool {
	return b == ' ' || b == '\t' || b == '\r' || b == '\n'
}

func parseSuppressionTail(tail string) suppression {
	names := nameRe.FindAllString(tail, -1)
	if len(names) == 0 {
		return suppression{all: true}
	}
	rules := make(map[string]bool, len(names))
	for _, n := range names {
		rules[n] = true
	}
	return suppression{rules: rules}
}

// addSuppression merges incoming into out[line] rather than
// overwriting. Two comment nodes on the same line each carrying a
// directive — `/* pasta:ignore foo */ /* pasta:ignore bar */` — both
// take effect after the merge.
func addSuppression(out *map[int]suppression, line int, incoming suppression) {
	if *out == nil {
		*out = map[int]suppression{}
	}
	existing, ok := (*out)[line]
	if !ok {
		(*out)[line] = incoming
		return
	}
	(*out)[line] = mergeSuppression(existing, incoming)
}

// mergeSuppression unions two suppression entries. `all` wins over
// any rule list — once every rule on the line is suppressed, naming
// individual ones adds nothing. Byte ranges are unioned so unused-
// ignore diagnostics can still highlight the comments.
func mergeSuppression(a, b suppression) suppression {
	start, end := a.start, a.end
	if b.start < start {
		start = b.start
	}
	if b.end > end {
		end = b.end
	}
	if a.all || b.all {
		return suppression{all: true, start: start, end: end}
	}
	out := suppression{
		rules: make(map[string]bool, len(a.rules)+len(b.rules)),
		start: start,
		end:   end,
	}
	for n := range a.rules {
		out.rules[n] = true
	}
	for n := range b.rules {
		out.rules[n] = true
	}
	return out
}

// markSuppressed reports whether rule is suppressed at the given
// 1-based line, and if so records that the suppression was used so
// unusedIgnoreDiagnostics will not warn about it.
func markSuppressed(suppress map[int]suppression, rule string, line int) bool {
	if len(suppress) == 0 {
		return false
	}
	e, ok := suppress[line]
	if !ok {
		return false
	}
	if e.all {
		e.usedAll = true
		suppress[line] = e
		return true
	}
	if !e.rules[rule] {
		return false
	}
	if e.usedRules == nil {
		e.usedRules = map[string]bool{}
	}
	e.usedRules[rule] = true
	suppress[line] = e
	return true
}

// isSuppressed reports whether rule is suppressed at the given 1-based
// line without recording usage. Prefer markSuppressed when a finding
// is actually being dropped.
func isSuppressed(suppress map[int]suppression, rule string, line int) bool {
	if len(suppress) == 0 {
		return false
	}
	e, ok := suppress[line]
	if !ok {
		return false
	}
	return e.all || e.rules[rule]
}

// unusedIgnoreDiagnostics returns a warning for every pasta:ignore
// that never suppressed a diagnostic or rewrite on its line.
//
// Bare `pasta:ignore` warns when nothing on the line was suppressed.
// Named forms warn once per listed rule that never matched.
func unusedIgnoreDiagnostics(suppress map[int]suppression) []effect.Diagnostic {
	if len(suppress) == 0 {
		return nil
	}
	lines := make([]int, 0, len(suppress))
	for ln := range suppress {
		lines = append(lines, ln)
	}
	sort.Ints(lines)

	var out []effect.Diagnostic
	for _, ln := range lines {
		e := suppress[ln]
		if e.all {
			if !e.usedAll {
				out = append(out, effect.Diagnostic{
					Rule:      unusedIgnoreRule,
					Message:   "unused ignore: no finding on this line",
					Severity:  dsl.SeverityWarning,
					StartByte: e.start,
					EndByte:   e.end,
					LineNum:   ln,
				})
			}
			continue
		}
		names := make([]string, 0, len(e.rules))
		for n := range e.rules {
			names = append(names, n)
		}
		sort.Strings(names)
		for _, n := range names {
			if e.usedRules[n] {
				continue
			}
			out = append(out, effect.Diagnostic{
				Rule:      unusedIgnoreRule,
				Message:   fmt.Sprintf("unused ignore: no %q finding on this line", n),
				Severity:  dsl.SeverityWarning,
				StartByte: e.start,
				EndByte:   e.end,
				LineNum:   ln,
			})
		}
	}
	return out
}

// hasPastaIgnore reports whether src contains the directive token.
// Used to force a parse when the prefilter would otherwise skip a
// file that may only need unused-ignore warnings.
func hasPastaIgnore(src []byte) bool {
	return directiveRe.Match(src)
}

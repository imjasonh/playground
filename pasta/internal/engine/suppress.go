package engine

import (
	"fmt"
	"regexp"
	"sort"
	"strings"
	"unicode"
	"unicode/utf8"

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
// Only comment text is scanned (per the language's `comment_types`),
// so a string literal like `log("user typed pasta:ignore go_iferr")`
// never reaches us. Within a comment, the match must also sit in a
// directive position (see directiveSpans) — prose that merely mentions
// the token is ignored.
var directiveRe = regexp.MustCompile(`pasta:ignore\b`)

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
		// the NEXT one, capped at the next newline.
		tailStart := m[1]
		tailEnd := len(text)
		if i+1 < len(starts) {
			tailEnd = starts[i+1][0]
		}
		if nl := strings.IndexByte(text[tailStart:tailEnd], '\n'); nl >= 0 {
			tailEnd = tailStart + nl
		}
		tail := text[tailStart:tailEnd]
		s, consumed := parseSuppressionTail(tail)
		tailEnd = tailStart + consumed
		line := effect.ComputeLine(n.Src, n.StartByte()+uint32(m[0]))
		s.start = n.StartByte() + uint32(m[0])
		s.end = n.StartByte() + uint32(tailEnd)
		for s.end > s.start && isSpace(n.Src[s.end-1]) {
			s.end--
		}
		addSuppression(out, line, s)
	}
}

// directiveSpans returns [start,end) indexes of active `pasta:ignore`
// tokens in a comment. Matches inside quotes / backticks are skipped,
// and a match only counts when the text before it on the same line
// (after comment decorations) is empty or prior pasta:ignore
// directives — so documentation that mentions the token mid-sentence
// does not suppress anything.
func directiveSpans(text string) [][]int {
	all := directiveRe.FindAllStringIndex(text, -1)
	if len(all) == 0 {
		return nil
	}
	out := make([][]int, 0, len(all))
	for _, m := range all {
		if inQuotedRegion(text, m[0]) {
			continue
		}
		if !isDirectivePosition(text, m[0]) {
			continue
		}
		out = append(out, m)
	}
	return out
}

// isDirectivePosition reports whether offset is a real suppression
// site: on its line, after stripping leading comment decorations
// (`//`, `#`, `--`, `/*`, `<!--`, `*`), only prior `pasta:ignore`
// directives (and their rule lists) may appear before offset.
func isDirectivePosition(text string, offset int) bool {
	lineStart := 0
	if i := strings.LastIndexByte(text[:offset], '\n'); i >= 0 {
		lineStart = i + 1
	}
	prefix := stripLeadingCommentDecorations(text[lineStart:offset])
	return onlyPriorDirectives(prefix)
}

// stripLeadingCommentDecorations removes comment leaders, block-comment
// star columns, and whitespace from the start of s. Mid-line `//` after
// other text is left alone so doc examples like
// `// x := foo() // pasta:ignore` are not treated as directives.
func stripLeadingCommentDecorations(s string) string {
	i := 0
	for i < len(s) {
		if isSpace(s[i]) || s[i] == '*' {
			i++
			continue
		}
		switch {
		case strings.HasPrefix(s[i:], "//"):
			i += 2
		case strings.HasPrefix(s[i:], "/*"):
			i += 2
		case strings.HasPrefix(s[i:], "<!--"):
			i += 4
		case strings.HasPrefix(s[i:], "--"):
			i += 2
		case s[i] == '#':
			i++
		default:
			return s[i:]
		}
	}
	return ""
}

// onlyPriorDirectives reports whether s is empty or a sequence of
// `pasta:ignore` tokens with comma/whitespace-separated rule names.
func onlyPriorDirectives(s string) bool {
	i := 0
	for i < len(s) {
		for i < len(s) && isSpace(s[i]) {
			i++
		}
		if i >= len(s) {
			return true
		}
		const tok = "pasta:ignore"
		if !strings.HasPrefix(s[i:], tok) {
			return false
		}
		i += len(tok)
		if i < len(s) {
			if r, _ := utf8.DecodeRuneInString(s[i:]); unicode.IsLetter(r) || unicode.IsDigit(r) || r == '_' {
				return false // pasta:ignored…
			}
		}
		for i < len(s) {
			for i < len(s) && isSpace(s[i]) {
				i++
			}
			if i >= len(s) {
				break
			}
			if s[i] == ',' {
				i++
				continue
			}
			if isIdentStart(s[i]) {
				for i < len(s) && isIdentCont(s[i]) {
					i++
				}
				continue
			}
			break
		}
	}
	for i < len(s) && isSpace(s[i]) {
		i++
	}
	return i >= len(s)
}

// inQuotedRegion reports whether offset sits inside a ", ', or `
// quoted span of s (backslash escapes honored inside " and ').
func inQuotedRegion(s string, offset int) bool {
	var quote byte // 0 = outside
	esc := false
	for i := 0; i < offset && i < len(s); i++ {
		c := s[i]
		if quote == 0 {
			if c == '"' || c == '\'' || c == '`' {
				quote = c
			}
			continue
		}
		if quote == '`' {
			if c == '`' {
				quote = 0
			}
			continue
		}
		if esc {
			esc = false
			continue
		}
		if c == '\\' {
			esc = true
			continue
		}
		if c == quote {
			quote = 0
		}
	}
	return quote != 0
}

func isSpace(b byte) bool {
	return b == ' ' || b == '\t' || b == '\r' || b == '\n'
}

func isIdentStart(b byte) bool {
	return b == '_' || (b >= 'A' && b <= 'Z') || (b >= 'a' && b <= 'z')
}

func isIdentCont(b byte) bool {
	return isIdentStart(b) || (b >= '0' && b <= '9')
}

// parseSuppressionTail reads a comma/whitespace-separated rule-name
// list from the start of tail and stops at the first other character
// (em dash, nested `# want`, prose, …). The returned consumed length
// covers only the list (plus leading whitespace), so anchors and
// unused-ignore warnings stay on the directive — not the explanation.
func parseSuppressionTail(tail string) (suppression, int) {
	i := 0
	for i < len(tail) && isSpace(tail[i]) {
		i++
	}
	if i >= len(tail) || !isIdentStart(tail[i]) {
		// Bare ignore. Trailing prose (` — constant URL`) is ignored.
		return suppression{all: true}, i
	}
	rules := map[string]bool{}
	for i < len(tail) {
		for i < len(tail) && isSpace(tail[i]) {
			i++
		}
		if i >= len(tail) {
			break
		}
		if tail[i] == ',' {
			i++
			continue
		}
		if !isIdentStart(tail[i]) {
			break
		}
		j := i + 1
		for j < len(tail) && isIdentCont(tail[j]) {
			j++
		}
		rules[tail[i:j]] = true
		i = j
	}
	if len(rules) == 0 {
		return suppression{all: true}, i
	}
	return suppression{rules: rules}, i
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
// file that may only need unused-ignore warnings. This is a cheap
// byte scan — false positives only cost an extra parse.
func hasPastaIgnore(src []byte) bool {
	return directiveRe.Match(src)
}

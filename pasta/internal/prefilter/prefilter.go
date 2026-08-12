// Package prefilter cheaply rejects source files that cannot match any
// applicable rule, so the engine can skip the expensive tree-sitter parse.
//
// A rule contributes substring constraints from:
//
//   - explicit `require_substring` on the rule
//   - `eq` / `token_eq` where-predicates with a literal (non-@) second arg
//   - `within` rewrite tokens (the token must appear in source to fire)
//   - simple `matches` regexes that are a literal or `|`-alternation of
//     literals (e.g. `==|!=`)
//
// Within one rule, literal `eq`/`token_eq`/`within`/`require_substring`
// constraints are AND-ed; simple `matches` alternatives are OR-ed. Across
// rules, a file is kept if ANY rule's filter passes — or if any rule has
// no usable filter (we can't prove it won't match).
package prefilter

import (
	"bytes"
	"strings"
	"unicode"

	"github.com/imjasonh/pasta/internal/dsl"
)

// Filter is the content-sniff constraint for one rule.
type Filter struct {
	// AllOf must every be present (byte substring) for the rule to
	// possibly match. Empty means no AND constraint.
	AllOf []string
	// AnyOf, when non-empty, requires at least one entry to be present.
	// Used for simple regex alternations from `matches`.
	AnyOf []string
}

// Empty reports whether the filter has no constraints — the file cannot
// be rejected on this rule's behalf.
func (f Filter) Empty() bool {
	return len(f.AllOf) == 0 && len(f.AnyOf) == 0
}

// Match reports whether src satisfies the filter.
func (f Filter) Match(src []byte) bool {
	for _, s := range f.AllOf {
		if !bytes.Contains(src, []byte(s)) {
			return false
		}
	}
	if len(f.AnyOf) == 0 {
		return true
	}
	for _, s := range f.AnyOf {
		if bytes.Contains(src, []byte(s)) {
			return true
		}
	}
	return false
}

// ForRule builds a Filter from a rule's explicit require_substring plus
// inferred literals. The result may be Empty when nothing useful can be
// inferred — callers must treat that as "may match".
func ForRule(rule *dsl.Rule) Filter {
	if rule == nil {
		return Filter{}
	}
	allSeen := map[string]bool{}
	var allOf []string
	addAll := func(s string) {
		s = strings.TrimSpace(s)
		if s == "" || strings.HasPrefix(s, "@") {
			return
		}
		if allSeen[s] {
			return
		}
		allSeen[s] = true
		allOf = append(allOf, s)
	}
	for _, s := range rule.RequireSubstring {
		addAll(s)
	}
	var anyOf []string
	anySeen := map[string]bool{}
	addAny := func(s string) {
		s = strings.TrimSpace(s)
		if s == "" || strings.HasPrefix(s, "@") {
			return
		}
		if anySeen[s] {
			return
		}
		anySeen[s] = true
		anyOf = append(anyOf, s)
	}

	walkPattern(&rule.Match, func(p *dsl.Pattern) {
		for _, w := range p.Where {
			switch w.Op {
			case "eq", "token_eq":
				if len(w.Args) >= 2 {
					addAll(w.Args[1].Str)
				}
			case "matches":
				if len(w.Args) >= 2 {
					lits, ok := simpleAlternationLiterals(w.Args[1].Str)
					if ok {
						for _, lit := range lits {
							addAny(lit)
						}
					}
				}
			}
		}
	})
	if rule.Rewrite != nil {
		for _, e := range rule.Rewrite.Edits {
			if e.Within != "" && e.Token != "" {
				addAll(e.Token)
			}
		}
	}
	return Filter{AllOf: allOf, AnyOf: anyOf}
}

// MayMatch reports whether src could match at least one of the filters.
// An empty filter list means "no applicable rules" → false. A single
// empty filter means "unfilterable rule" → true.
func MayMatch(src []byte, filters []Filter) bool {
	if len(filters) == 0 {
		return false
	}
	for _, f := range filters {
		if f.Empty() || f.Match(src) {
			return true
		}
	}
	return false
}

// ForRules is a convenience over ForRule + MayMatch.
func ForRules(rules []*dsl.Rule) []Filter {
	out := make([]Filter, 0, len(rules))
	for _, r := range rules {
		out = append(out, ForRule(r))
	}
	return out
}

func walkPattern(p *dsl.Pattern, fn func(*dsl.Pattern)) {
	if p == nil {
		return
	}
	fn(p)
	for _, c := range p.Fields {
		walkChild(&c, fn)
	}
	for i := range p.Children {
		walkChild(&p.Children[i], fn)
	}
	for i := range p.Adjacent {
		walkChild(&p.Adjacent[i], fn)
	}
	if p.Preceding != nil {
		walkChild(p.Preceding, fn)
	}
}

func walkChild(c *dsl.Child, fn func(*dsl.Pattern)) {
	if c == nil {
		return
	}
	if c.Pattern != nil {
		walkPattern(c.Pattern, fn)
	}
	// Inline pattern-form fields on the child.
	if sub := c.AsPattern(); sub != nil && sub != c.Pattern {
		walkPattern(sub, fn)
	}
	if c.Preceding != nil {
		walkChild(c.Preceding, fn)
	}
}

// simpleAlternationLiterals accepts patterns like `==`, `!=`, `==|!=`,
// `gets` — a sequence of `|`-separated literals with no regex
// metacharacters. Returns ok=false for anything else so we don't infer
// wrong constraints from complex regexes.
func simpleAlternationLiterals(pat string) ([]string, bool) {
	if pat == "" {
		return nil, false
	}
	parts := strings.Split(pat, "|")
	out := make([]string, 0, len(parts))
	for _, p := range parts {
		if p == "" || !isLiteralSubstring(p) {
			return nil, false
		}
		out = append(out, p)
	}
	return out, true
}

func isLiteralSubstring(s string) bool {
	for _, r := range s {
		switch r {
		case '.', '*', '+', '?', '(', ')', '[', ']', '{', '}', '^', '$', '\\':
			return false
		}
		if unicode.IsControl(r) {
			return false
		}
	}
	return true
}

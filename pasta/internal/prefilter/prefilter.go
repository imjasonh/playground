// Package prefilter cheaply rejects source files that cannot match any
// applicable rule, so the engine can skip the expensive tree-sitter parse.
//
// A rule contributes substring constraints from:
//
//   - explicit `require_substring` on the rule
//   - `eq` / `token_eq` where-predicates with a literal (non-@) second arg
//   - the literals each `matches` regex requires: `^(Atoi|ParseInt)$`
//     requires Atoi or ParseInt, and `(^|::)Command::new$` requires
//     Command::new
//
// Rewrite `within` tokens are intentionally NOT inferred: diagnostics
// can fire whenever the pattern matches even if the rewrite token is
// absent (`applyWithin` no-ops). Inferring them as AND constraints
// would false-negative diagnose-only hits.
//
// A rule's where-predicates all hold on a match, and the text `matches`
// tests is a node's, which is part of the file. So within one rule every
// constraint is AND-ed, and the literals of one alternative in a regex
// are OR-ed. Across rules, a file is kept if ANY rule's filter passes — or if any
// rule has no usable filter (we can't prove it won't match).
package prefilter

import (
	"bytes"
	"strings"

	"github.com/imjasonh/playground/pasta/internal/dsl"
)

// Filter is the content-sniff constraint for one rule.
type Filter struct {
	// AllOf must every be present (byte substring) for the rule to
	// possibly match. Empty means no AND constraint.
	AllOf []string
	// AnyOf holds groups from `matches` regexes. Each group needs at
	// least one of its entries present.
	AnyOf [][]string
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
	for _, g := range f.AnyOf {
		if !containsAny(src, g) {
			return false
		}
	}
	return true
}

func containsAny(src []byte, ss []string) bool {
	for _, s := range ss {
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

	var anyOf [][]string
	dsl.WalkPattern(&rule.Match, func(p *dsl.Pattern) {
		for _, w := range p.Where {
			switch w.Op {
			case "eq", "token_eq":
				if len(w.Args) >= 2 {
					addAll(w.Args[1].Str)
				}
			case "matches":
				if len(w.Args) >= 2 {
					for _, g := range regexLiterals(w.Args[1].Str) {
						if len(g) == 1 {
							addAll(g[0])
						} else {
							anyOf = append(anyOf, g)
						}
					}
				}
			}
		}
	})
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

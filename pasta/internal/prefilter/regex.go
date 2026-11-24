package prefilter

import (
	"regexp/syntax"
	"slices"
	"strings"
	"unicode/utf8"
)

// maxSet bounds the strings in one set, so an alternation can't make a
// filter that costs more than it saves. maxClass bounds a character
// class, whose one-character literals reject few files.
const (
	maxSet   = 32
	maxClass = 8
)

// regexLiterals returns groups of literals for the regular expression
// pat: every string pat matches contains at least one literal from each
// group. It returns no groups when pat requires no literal or doesn't
// parse.
func regexLiterals(pat string) [][]string {
	re, err := syntax.Parse(pat, syntax.Perl)
	if err != nil {
		return nil
	}
	return required(re)
}

// required returns groups of literals that every match of re contains
// one of each.
func required(re *syntax.Regexp) [][]string {
	if set, ok := exact(re); ok {
		if slices.Contains(set, "") {
			return nil
		}
		return [][]string{minimal(set)}
	}
	switch re.Op {
	case syntax.OpCapture, syntax.OpPlus:
		return required(re.Sub[0])
	case syntax.OpRepeat:
		if re.Min >= 1 {
			return required(re.Sub[0])
		}
	case syntax.OpConcat:
		return requiredConcat(re.Sub)
	case syntax.OpAlternate:
		var union []string
		for _, sub := range re.Sub {
			g := best(required(sub))
			if g == nil {
				return nil
			}
			union = appendNew(union, g...)
		}
		if len(union) > maxSet {
			return nil
		}
		return [][]string{minimal(union)}
	}
	return nil
}

// requiredConcat joins runs of adjacent subexpressions that each match
// a known set of strings into one set, so `^Add(Int32|Int64)$` requires
// AddInt32 or AddInt64 rather than Add alone.
func requiredConcat(subs []*syntax.Regexp) [][]string {
	var groups [][]string
	run := []string{""}
	flush := func() {
		if !slices.Contains(run, "") {
			groups = append(groups, minimal(run))
		}
		run = []string{""}
	}
	for _, sub := range subs {
		set, ok := exact(sub)
		if !ok {
			flush()
			groups = append(groups, required(sub)...)
			continue
		}
		if next, ok := product(run, set); ok {
			run = next
			continue
		}
		flush()
		run = set
	}
	flush()
	return groups
}

// exact returns every string re matches, when there are at most maxSet
// of them. Assertions such as ^ and \b match the empty string.
func exact(re *syntax.Regexp) ([]string, bool) {
	switch re.Op {
	case syntax.OpEmptyMatch, syntax.OpBeginLine, syntax.OpEndLine,
		syntax.OpBeginText, syntax.OpEndText,
		syntax.OpWordBoundary, syntax.OpNoWordBoundary:
		return []string{""}, true
	case syntax.OpLiteral:
		if re.Flags&syntax.FoldCase != 0 {
			return nil, false
		}
		return []string{string(re.Rune)}, true
	case syntax.OpCharClass:
		var set []string
		for i := 0; i+1 < len(re.Rune); i += 2 {
			lo, hi := re.Rune[i], re.Rune[i+1]
			if hi-lo >= maxClass || len(set)+int(hi-lo)+1 > maxClass {
				return nil, false
			}
			for r := lo; r <= hi; r++ {
				if !utf8.ValidRune(r) {
					return nil, false
				}
				set = append(set, string(r))
			}
		}
		return set, len(set) > 0
	case syntax.OpCapture:
		return exact(re.Sub[0])
	case syntax.OpQuest:
		set, ok := exact(re.Sub[0])
		if !ok || len(set) >= maxSet {
			return nil, false
		}
		return appendNew(set, ""), true
	case syntax.OpConcat:
		set := []string{""}
		for _, sub := range re.Sub {
			s, ok := exact(sub)
			if !ok {
				return nil, false
			}
			if set, ok = product(set, s); !ok {
				return nil, false
			}
		}
		return set, true
	case syntax.OpAlternate:
		var set []string
		for _, sub := range re.Sub {
			s, ok := exact(sub)
			if !ok {
				return nil, false
			}
			set = appendNew(set, s...)
			if len(set) > maxSet {
				return nil, false
			}
		}
		return set, true
	}
	return nil, false
}

// product returns every string of a followed by a string of b, unless
// there are more than maxSet of them.
func product(a, b []string) ([]string, bool) {
	if len(a)*len(b) > maxSet {
		return nil, false
	}
	var out []string
	for _, x := range a {
		for _, y := range b {
			out = appendNew(out, x+y)
		}
	}
	return out, true
}

// best returns the group whose shortest literal is longest, since a
// longer literal rejects more files, and of those the smallest group.
func best(groups [][]string) []string {
	var out []string
	for _, g := range groups {
		if out == nil || shortest(g) > shortest(out) ||
			shortest(g) == shortest(out) && len(g) < len(out) {
			out = g
		}
	}
	return out
}

// minimal drops each literal that contains another, since a file that
// contains it contains the other too.
func minimal(set []string) []string {
	var out []string
	for i, s := range set {
		if !slices.ContainsFunc(set, func(o string) bool {
			return o != s && strings.Contains(s, o)
		}) && !slices.Contains(set[:i], s) {
			out = append(out, s)
		}
	}
	return out
}

func shortest(set []string) int {
	n := -1
	for _, s := range set {
		if n < 0 || len(s) < n {
			n = len(s)
		}
	}
	return n
}

func appendNew(set []string, ss ...string) []string {
	for _, s := range ss {
		if !slices.Contains(set, s) {
			set = append(set, s)
		}
	}
	return set
}

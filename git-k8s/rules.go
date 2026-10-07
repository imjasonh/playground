package gitk8s

import (
	"maps"
	"path"
	"slices"
	"strings"
)

// Match reports whether a branch name matches a glob pattern.
//
// Patterns match /-separated segments. A ** segment matches zero or more
// segments. Within a segment, * matches any run of characters, ? matches one
// character, and [a-z] matches a character class, as in path.Match.
func Match(pattern, branch string) bool {
	return matchSegments(strings.Split(pattern, "/"), strings.Split(branch, "/"))
}

func matchSegments(pattern, segments []string) bool {
	if len(pattern) == 0 {
		return len(segments) == 0
	}
	if pattern[0] == "**" {
		for i := range len(segments) + 1 {
			if matchSegments(pattern[1:], segments[i:]) {
				return true
			}
		}
		return false
	}
	if len(segments) == 0 {
		return false
	}
	ok, err := path.Match(pattern[0], segments[0])
	return err == nil && ok && matchSegments(pattern[1:], segments[1:])
}

// FindRule returns the first rule that matches branch, or nil.
func FindRule(rules []BranchRule, branch string) *BranchRule {
	for i := range rules {
		if Match(rules[i].Match, branch) {
			return &rules[i]
		}
	}
	return nil
}

// DesiredBranches returns the spec of a Branch object for each branch in heads,
// a map from branch name to commit SHA, that a rule selects. A branch whose
// rule names a parent gets the merge policy of the rule that matches the
// parent, so each Branch object carries the policy that applies to it. The
// result is sorted by branch name.
func DesiredBranches(repository string, rules []BranchRule, heads map[string]string) []BranchSpec {
	var out []BranchSpec
	for _, branch := range slices.Sorted(maps.Keys(heads)) {
		rule := FindRule(rules, branch)
		if rule == nil {
			continue
		}
		spec := BranchSpec{Repository: repository, Branch: branch, Head: heads[branch]}
		if rule.Parent != "" && rule.Parent != branch {
			spec.Parent = rule.Parent
			spec.ParentHead = heads[rule.Parent]
			if pr := FindRule(rules, rule.Parent); pr != nil {
				spec.Merge = pr.Merge
			}
		}
		out = append(out, spec)
	}
	return out
}

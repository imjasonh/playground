package gitk8s

import (
	"reflect"
	"testing"
)

func TestMatch(t *testing.T) {
	for _, c := range []struct {
		pattern, branch string
		want            bool
	}{
		{"main", "main", true},
		{"main", "mainline", false},
		{"c/**", "c/add", true},
		{"c/**", "c/a/b", true},
		{"c/*", "c/a/b", false},
		{"c/*", "c/add", true},
		{"release-*", "release-1.2", true},
		{"release-*", "release/1.2", false},
		{"**/fix", "a/b/fix", true},
		{"**/fix", "fix", true},
		{"a/**/z", "a/z", true},
		{"a/**/z", "a/b/c/z", true},
		{"v?", "v1", true},
		{"v?", "v10", false},
		{"v[0-9]", "v7", true},
		{"dependabot/**", "dependabot/go_modules/x-1.2", true},
	} {
		if got := Match(c.pattern, c.branch); got != c.want {
			t.Errorf("Match(%q, %q) = %v, want %v", c.pattern, c.branch, got, c.want)
		}
	}
}

func TestDesiredBranches(t *testing.T) {
	policy := &MergePolicy{Checks: []CheckPolicy{{Name: "gofmt", MayPush: true}}}
	rules := []BranchRule{
		{Match: "main", Merge: policy},
		{Match: "c/**", Parent: "main"},
		{Match: "orphan/**", Parent: "missing"},
		{Match: "self", Parent: "self"},
	}
	heads := map[string]string{
		"main":      "m1",
		"c/add":     "c1",
		"feature/x": "f1",
		"orphan/a":  "o1",
		"self":      "s1",
	}
	got := DesiredBranches("app", rules, heads)
	want := []GitBranchSpec{
		{Repository: "app", Branch: "c/add", Head: "c1", Parent: "main", ParentHead: "m1", Merge: policy},
		{Repository: "app", Branch: "main", Head: "m1"},
		{Repository: "app", Branch: "orphan/a", Head: "o1", Parent: "missing"},
		{Repository: "app", Branch: "self", Head: "s1"},
	}
	if !reflect.DeepEqual(got, want) {
		t.Errorf("DesiredBranches =\n%+v\nwant\n%+v", got, want)
	}
}

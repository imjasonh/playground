package engine

import (
	"testing"

	"github.com/imjasonh/playground/pasta/internal/dsl"
)

func TestRuleAppliesToFile_exclude(t *testing.T) {
	rule := &dsl.Rule{FileExclude: []string{"ios/**/project.yml"}}
	cases := []struct {
		path string
		want bool
	}{
		{path: "ios/project.yml", want: false},
		{path: "ios/nested/project.yml", want: false},
		{path: "/abs/ios/project.yml", want: false},
		{path: "hello-macos/project.yml", want: true},
		{path: "onramp/project.yml", want: true},
		{path: "ios/AGENTS.md", want: true},
	}
	for _, tc := range cases {
		got := ruleAppliesToFile(rule, tc.path)
		if got != tc.want {
			t.Errorf("ruleAppliesToFile(%q) = %v, want %v", tc.path, got, tc.want)
		}
	}
}

func TestRuleAppliesToFile_matchAndExclude(t *testing.T) {
	rule := &dsl.Rule{
		FileMatch:   []string{"*_test.go"},
		FileExclude: []string{"vendor/**"},
	}
	if !ruleAppliesToFile(rule, "pkg/foo_test.go") {
		t.Error("include match should apply")
	}
	if ruleAppliesToFile(rule, "pkg/foo.go") {
		t.Error("basename miss should skip")
	}
	if ruleAppliesToFile(rule, "vendor/pkg/foo_test.go") {
		t.Error("exclude should win over include")
	}
}

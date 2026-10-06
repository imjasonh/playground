package main

import (
	"strings"
	"testing"
)

func TestGateProblems(t *testing.T) {
	const head, parent, old = "aaaaaaa1", "bbbbbbb2", "ccccccc3"
	passed := func(commit, parentCommit string, outputs map[string]string) checkResult {
		return checkResult{Commit: commit, ParentCommit: parentCommit, State: "Passed", Outputs: outputs}
	}
	landed := func(edit func(map[string]checkResult)) *branchRec {
		checks := map[string]checkResult{
			"base":   passed(head, parent, nil),
			"gofmt":  passed(head, "", nil),
			"risk":   passed(head, parent, map[string]string{"level": "low"}),
			"gotest": passed(head, "", nil),
		}
		if edit != nil {
			edit(checks)
		}
		return &branchRec{Head: head, ParentHead: parent, Checks: checks}
	}
	high := map[string]string{"level": "high"}
	for _, c := range []struct {
		name   string
		b      *branchRec
		gotest bool
		parent string
		// want is part of a problem that gateProblems must report, or ""
		// for none.
		want string
	}{
		{"passed", landed(nil), true, "", ""},
		{"parent from the Landed event", landed(nil), true, parent, ""},
		{"gate without gotest", landed(func(cs map[string]checkResult) { delete(cs, "gotest") }), false, "", ""},
		{"no gotest result", landed(func(cs map[string]checkResult) { delete(cs, "gotest") }), true, "", "gotest has no result"},
		{"result for another head", landed(func(cs map[string]checkResult) { cs["gofmt"] = passed(old, "", nil) }), true, "", "gofmt is for"},
		{"failed check", landed(func(cs map[string]checkResult) { cs["gotest"] = checkResult{Commit: head, State: "Failed"} }), true, "", "gotest is Failed"},
		{"base behind", landed(func(cs map[string]checkResult) {
			cs["base"] = passed(head, parent, map[string]string{"behind": "true"})
		}), true, "", "base ran against"},
		{"base against an older parent", landed(func(cs map[string]checkResult) { cs["base"] = passed(head, old, nil) }), true, "", "base ran against"},
		{"risk against an older parent", landed(func(cs map[string]checkResult) { cs["risk"] = passed(head, old, map[string]string{"level": "low"}) }), true, "", "risk ran against"},
		{"landed on another parent", landed(nil), true, old, "not the parent's head"},
		{"high risk without approval", landed(func(cs map[string]checkResult) { cs["risk"] = passed(head, parent, high) }), true, "", `risk is "high"`},
		{"high risk with approval", landed(func(cs map[string]checkResult) {
			cs["risk"], cs["approval"] = passed(head, parent, high), passed(head, "", nil)
		}), true, "", ""},
		{"high risk with an approval result for another head", landed(func(cs map[string]checkResult) {
			cs["risk"], cs["approval"] = passed(head, parent, high), passed(old, "", nil)
		}), true, "", `risk is "high"`},
	} {
		t.Run(c.name, func(t *testing.T) {
			problems := strings.Join(gateProblems(c.b, c.gotest, c.parent), "; ")
			switch {
			case c.want == "" && problems != "":
				t.Errorf("problems: %s", problems)
			case c.want != "" && !strings.Contains(problems, c.want):
				t.Errorf("problems: %q, want %q", problems, c.want)
			}
		})
	}
}

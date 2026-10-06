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
		{"carried rating and approval on top of the parent's head", landed(func(cs map[string]checkResult) {
			cs["risk"] = checkResult{Commit: head, MergeBase: parent, State: "Passed", Outputs: high}
			cs["approval"] = checkResult{Commit: head, MergeBase: parent, State: "Passed"}
		}), true, parent, ""},
		{"rating on top of an older merge base", landed(func(cs map[string]checkResult) {
			cs["risk"] = checkResult{Commit: head, MergeBase: old, State: "Passed", Outputs: map[string]string{"level": "low"}}
		}), true, parent, "risk holds for the change on top of"},
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

func TestLandedApproval(t *testing.T) {
	g := &gitRepo{dir: t.TempDir()}
	run := func(args ...string) string {
		t.Helper()
		out, err := g.git(nil, args...)
		if err != nil {
			t.Fatal(err)
		}
		return out
	}
	commit := func(files map[string]string, msg string) string {
		t.Helper()
		if err := g.write(files); err != nil {
			t.Fatal(err)
		}
		sha, err := g.commit(author{"dev", "dev@example.com"}, msg)
		if err != nil {
			t.Fatal(err)
		}
		return sha
	}
	run("init", "-q", "-b", "main")
	base := commit(map[string]string{"a.txt": "a\n", "b.txt": "b\n"}, "Initial commit")
	parent := commit(map[string]string{"b.txt": "b2\n"}, "Change b")
	run("checkout", "-q", "-b", "c/x", base)
	// The reviewer approves head, and the base check merges main into it
	// as merged. Then the developer pushes changed, which changes code.
	head := commit(map[string]string{"feat.txt": "feat\n"}, "Add feat")
	run("merge", "-q", "--no-ff", "-m", "Merge main into c/x", parent)
	merged := run("rev-parse", "HEAD")
	changed := commit(map[string]string{"feat.txt": "feat2\n"}, "Change feat")

	for _, c := range []struct {
		name     string
		approve  string
		landed   string
		approved []string
		parent   string
		carried  bool
		// want is part of the problem that landedApproval must report, or
		// "" for none.
		want string
	}{
		// On main, the approval check passes only for the head that the
		// annotation names, so every landing is direct.
		{name: "approval of the landed head", approve: head, landed: head, approved: []string{head}, parent: base},
		{name: "approval of the landed merge", approve: merged, landed: merged, approved: []string{head, merged}, parent: parent},
		{name: "approval by a prefix of the landed head", approve: merged[:12], landed: merged, approved: []string{merged}, parent: parent},
		{name: "approval carried to the merge", approve: head, landed: merged, approved: []string{head}, parent: parent, carried: true},
		{name: "abbreviated parent's head", approve: head, landed: merged, approved: []string{head}, parent: parent[:12], carried: true},
		{name: "carried to a head that changes code", approve: head, landed: changed, approved: []string{head}, parent: parent, carried: true, want: "but the landed head has"},
		{name: "carried onto another parent's head", approve: head, landed: merged, approved: []string{head}, parent: base, carried: true, want: "but the landed head has"},
		{name: "carried without the parent's head", approve: head, landed: merged, approved: []string{head}, carried: true, want: "no parent head"},
		{name: "prefix of an earlier head", approve: head[:12], landed: merged, approved: []string{head}, parent: parent, want: "doesn't name the landed head"},
		{name: "head that the reviewer didn't approve", approve: merged, landed: merged, approved: []string{head}, parent: parent, want: "doesn't name the landed head"},
		{name: "no approval", landed: merged, approved: []string{head}, parent: parent, want: "doesn't name the landed head"},
	} {
		t.Run(c.name, func(t *testing.T) {
			approved := map[string]bool{}
			for _, h := range c.approved {
				approved[h] = true
			}
			carried, problem := landedApproval(g, &branchRec{Head: c.landed, Approve: c.approve}, approved, c.parent)
			if carried != c.carried {
				t.Errorf("carried = %v, want %v", carried, c.carried)
			}
			switch {
			case c.want == "" && problem != "":
				t.Errorf("problem: %s", problem)
			case c.want != "" && !strings.Contains(problem, c.want):
				t.Errorf("problem: %q, want %q", problem, c.want)
			}
		})
	}
}

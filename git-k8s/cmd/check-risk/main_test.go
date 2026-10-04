package main

import (
	"cmp"
	"strings"
	"testing"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/checks"
	"github.com/imjasonh/playground/git-k8s/internal/git"
	"github.com/imjasonh/playground/git-k8s/internal/gittest"
	"github.com/imjasonh/playground/kube"
)

// rate commits base on main, and change on c/x with message, and rates c/x.
func rate(t *testing.T, base, change map[string]string, message string) *gitk8s.CheckResult {
	t.Helper()
	srv := gittest.NewServer(t, "")
	w := srv.NewWork(t, "app")
	w.Write("README.md", "hello\n")
	for path, content := range base {
		w.Write(path, content)
	}
	main := w.Commit("main")
	w.Push("main")
	w.Branch("c/x", main)
	for path, content := range change {
		w.Write(path, content)
	}
	head := w.Commit(message)
	w.Push("c/x")

	b := &Branch{Object: kube.Meta("app-c-x", nil)}
	b.Namespace = "default"
	b.Spec = gitk8s.GitBranchSpec{
		Repository: "app", Branch: "c/x", Head: head, Parent: "main", ParentHead: main,
		Merge: &gitk8s.MergePolicy{Checks: []gitk8s.CheckPolicy{{Name: "risk"}}},
	}
	repo, secret := srv.Repository("app")
	ctx, _ := kube.Fake(t.Context(), b, repo, secret)
	if err := checks.NewReconciler[Branch](check, &checks.Config{CacheDir: t.TempDir()}).Reconcile(ctx, b); err != nil {
		t.Fatal(err)
	}
	return b.Status.Checks.Result
}

func TestRisk(t *testing.T) {
	*maxLines, *sensitive = 10, "auth/**, **/*.pem"
	for _, c := range []struct {
		name   string
		files  map[string]string
		level  string
		reason string
	}{
		{"small", map[string]string{"docs/a.md": "a\nb\n"}, "low", "changes 2 lines in 1 files"},
		{"big", map[string]string{"big.txt": strings.Repeat("x\n", 11)}, "high", "changes 11 lines, more than 10"},
		{"sensitive", map[string]string{"auth/policy.go": "package auth\n"}, "high", "touches auth/policy.go"},
		{"sensitive glob", map[string]string{"certs/server.pem": "key\n"}, "high", "touches certs/server.pem"},
	} {
		t.Run(c.name, func(t *testing.T) {
			res := rate(t, nil, c.files, "change")
			if res.State != gitk8s.Passed || res.Outputs["level"] != c.level || !strings.Contains(res.Message, c.reason) {
				t.Errorf("result = %+v, want level %s and %q", res, c.level, c.reason)
			}
			if res.ParentCommit == "" {
				t.Error("risk results depend on the parent's head")
			}
		})
	}
}

const goMod = `module example.com/app

go 1.24

require (
	example.com/a v1.2.3
	example.com/b v0.4.0
)

replace example.com/fork => example.com/forked v1.0.0
`

func TestRiskOfModules(t *testing.T) {
	*maxLines, *sensitive = 10, ""
	base := map[string]string{
		"go.mod":       goMod,
		"tools/go.mod": "module example.com/app/tools\n\ngo 1.24\n\nrequire example.com/t v1.0.0\n",
	}
	edit := func(old, new string) map[string]string {
		return map[string]string{"go.mod": strings.Replace(goMod, old, new, 1)}
	}
	sums := edit("a v1.2.3", "a v1.2.4")
	sums["go.sum"] = strings.Repeat("example.com/a v1.2.4 h1:abc=\n", 12)
	for _, c := range []struct {
		name    string
		change  map[string]string
		message string
		level   string
		reason  string
	}{
		{name: "patch release", change: sums, level: "low", reason: "changes 2 lines in 2 files, not counting go.sum"},
		{name: "minor release of v0", change: edit("b v0.4.0", "b v0.5.0"), level: "low", reason: "changes 2 lines in 1 files"},
		{name: "module that another go.mod requires", change: edit(")", "\texample.com/t v1.1.0\n)"), level: "low"},
		{name: "local replacement", change: edit("replace", "replace example.com/b => ./b\nreplace"), level: "low"},
		{name: "new go.mod", change: map[string]string{"svc/go.mod": "module example.com/app/svc\n\ngo 1.26\n\nrequire example.com/a v1.2.3\n"}, level: "low"},
		{name: "new module", change: edit(")", "\texample.com/c v1.0.0\n)"), level: "high", reason: "adds module example.com/c"},
		{name: "major version path", change: edit("example.com/a v1.2.3", "example.com/a/v2 v2.0.0"), level: "high", reason: "moves example.com/a to example.com/a/v2"},
		{name: "v0 to v1", change: edit("b v0.4.0", "b v1.0.0"), level: "high", reason: "moves example.com/b to v1.0.0, a new major version"},
		{name: "prerelease", change: edit("a v1.2.3", "a v1.3.0-rc.1"), level: "high", reason: "moves example.com/a to v1.3.0-rc.1, which isn't a release"},
		{name: "pseudo-version", change: edit("a v1.2.3", "a v1.2.4-0.20260102030405-abcdefabcdef"), level: "high", reason: "which isn't a release"},
		{name: "replacement", change: edit("replace", "replace example.com/a => example.com/fork/a v1.2.3\nreplace"), level: "high", reason: "replaces example.com/a with example.com/fork/a@v1.2.3"},
		{name: "dropped replacement", change: edit("replace example.com/fork => example.com/forked v1.0.0\n", ""), level: "high", reason: "stops replacing example.com/fork with example.com/forked@v1.0.0"},
		{name: "go line", change: edit("go 1.24", "go 1.25"), level: "high", reason: "changes the go line in go.mod from 1.24 to 1.25"},
		{name: "toolchain line", change: edit("go 1.24\n", "go 1.24\n\ntoolchain go1.26.1\n"), level: "high", reason: "changes the toolchain line in go.mod from none to go1.26.1"},
		{name: "unreadable go.mod", change: map[string]string{"go.mod": "this isn't a go.mod file\n"}, level: "high", reason: "changes go.mod, which check-risk can't read"},
		{
			name:    "agent commit",
			change:  map[string]string{"main.go": "package main\n"},
			message: "Apply changes from the deps agent\n\n" + git.FixerTrailer + ": deps\n" + git.AgentTrailer + ": deps",
			level:   "high",
			reason:  "has 1 commit from an AI agent",
		},
	} {
		t.Run(c.name, func(t *testing.T) {
			res := rate(t, base, c.change, cmp.Or(c.message, "change"))
			if res.State != gitk8s.Passed || res.Outputs["level"] != c.level || !strings.Contains(res.Message, c.reason) {
				t.Errorf("result = %+v, want level %s and %q", res, c.level, c.reason)
			}
		})
	}
}

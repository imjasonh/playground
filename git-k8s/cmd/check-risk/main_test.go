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

const toolsMod = "module example.com/app/tools\n\ngo 1.24\n\nrequire (\n\texample.com/b v0.3.0\n\texample.com/t v1.0.0\n)\n\nreplace example.com/t => ../t\n"

func TestRiskOfModules(t *testing.T) {
	*maxLines, *sensitive = 10, ""
	base := map[string]string{
		"go.mod":       goMod,
		"tools/go.mod": toolsMod,
		"dup/go.mod":   "module example.com/app/dup\n\ngo 1.24\n\nrequire (\n\texample.com/d v1.0.0\n\texample.com/d v1.2.0\n\texample.com/d v1.1.0\n)\n",
	}
	edit := func(old, new string) map[string]string {
		return map[string]string{"go.mod": strings.Replace(goMod, old, new, 1)}
	}
	with := func(change map[string]string, path, content string) map[string]string {
		change[path] = content
		return change
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
		{name: "local replacement in a subdirectory", change: map[string]string{"tools/go.mod": toolsMod + "replace example.com/u => ../u\n"}, level: "low"},
		{name: "module that a go.mod file at the merge base declares", change: edit(")", "\texample.com/app/tools v0.1.0\n)"), level: "low"},
		{
			name:   "new module in a directory in the repository",
			change: with(edit(")", "\texample.com/app/svc v0.0.0\n)\n\nreplace example.com/app/svc => ./svc\n"), "svc/go.mod", "module example.com/app/svc\n\ngo 1.24\n"),
			level:  "low",
		},
		{
			name:   "outside module that a new go.mod file declares",
			change: with(edit(")", "\tgithub.com/attacker/evil v1.0.0\n)"), "x/go.mod", "module github.com/attacker/evil\n"),
			level:  "high", reason: "adds module github.com/attacker/evil",
		},
		{
			name:   "new module in a directory outside the repository",
			change: edit(")", "\texample.com/evil v1.0.0\n)\n\nreplace example.com/evil => ../evil\n"),
			level:  "high", reason: "adds module example.com/evil; replaces example.com/evil with ../evil, which is outside the repository",
		},
		{
			name:   "replacement of another version with a directory in the repository",
			change: edit(")", "\texample.com/c v1.1.0\n)\n\nreplace example.com/c v1.0.0 => ./c\n"),
			level:  "high", reason: "adds module example.com/c",
		},
		{name: "replacement with a directory outside the repository", change: edit("replace", "replace example.com/a => ../../outside/a\nreplace"), level: "high", reason: "replaces example.com/a with ../../outside/a, which is outside the repository"},
		{name: "replacement with the parent directory", change: map[string]string{"tools/go.mod": toolsMod + "replace example.com/u => ../..\n"}, level: "high", reason: "replaces example.com/u with ../.., which is outside the repository"},
		{name: "replacement with an absolute directory", change: edit("replace", "replace example.com/a => /go/pkg/mod/github.com/attacker/a@v1.0.0\nreplace"), level: "high", reason: "which is outside the repository"},
		{name: "replacement with a directory on a Windows drive", change: edit("replace", "replace example.com/a => C:/mods/a\nreplace"), level: "high", reason: "which is outside the repository"},
		{name: "replacement that another directory makes", change: edit("replace", "replace example.com/t => ../t\nreplace"), level: "high", reason: "replaces example.com/t with ../t, which is outside the repository"},
		{
			name: "go.work",
			change: map[string]string{
				"go.work":     "go 1.24\n\nuse .\n\nreplace example.com/a => github.com/attacker/a v1.0.0\n",
				"go.work.sum": "github.com/attacker/a v1.0.0 h1:abc=\n",
			},
			level: "high", reason: "changes go.work",
		},
		{name: "new go.mod", change: map[string]string{"svc/go.mod": "module example.com/app/svc\n\ngo 1.26\n\nrequire example.com/a v1.2.3\n"}, level: "low"},
		{name: "new module", change: edit(")", "\texample.com/c v1.0.0\n)"), level: "high", reason: "adds module example.com/c"},
		{name: "major version path", change: edit("example.com/a v1.2.3", "example.com/a/v2 v2.0.0"), level: "high", reason: "moves example.com/a to example.com/a/v2"},
		{name: "v0 to v1", change: edit("b v0.4.0", "b v1.0.0"), level: "high", reason: "moves example.com/b to v1.0.0, a new major version"},
		{name: "downgrade", change: edit("a v1.2.3", "a v1.2.0"), level: "high", reason: "downgrades example.com/a from v1.2.3 to v1.2.0"},
		{name: "downgrade to a version that another go.mod file requires", change: edit("b v0.4.0", "b v0.3.0"), level: "high", reason: "downgrades example.com/b from v0.4.0 to v0.3.0"},
		{name: "upgrade to a version older than another go.mod file's", change: map[string]string{"tools/go.mod": strings.Replace(toolsMod, "b v0.3.0", "b v0.3.1", 1)}, level: "low"},
		{
			name:   "downgrade from the highest of several requirements",
			change: map[string]string{"dup/go.mod": "module example.com/app/dup\n\ngo 1.24\n\nrequire example.com/d v1.1.5\n"},
			level:  "high", reason: "downgrades example.com/d from v1.2.0 to v1.1.5",
		},
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

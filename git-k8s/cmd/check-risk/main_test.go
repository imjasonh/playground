package main

import (
	"cmp"
	"context"
	"maps"
	"os"
	"path/filepath"
	"strings"
	"testing"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/checks"
	"github.com/imjasonh/playground/git-k8s/internal/git"
	"github.com/imjasonh/playground/git-k8s/internal/gittest"
	"github.com/imjasonh/playground/kube"
)

// symlinkTo and submoduleAt start the contents of files that rate writes as
// a symbolic link to the rest of the contents, and as a submodule at the
// commit that the rest names.
const (
	symlinkTo   = "\x00symlink "
	submoduleAt = "\x00submodule "
)

// write writes content to path in w's working tree.
func write(t *testing.T, w *gittest.Work, path, content string) {
	t.Helper()
	target, link := strings.CutPrefix(content, symlinkTo)
	commit, sub := strings.CutPrefix(content, submoduleAt)
	if !link && !sub {
		w.Write(path, content)
		return
	}
	full := filepath.Join(w.Dir, path)
	if err := os.RemoveAll(full); err != nil {
		t.Fatal(err)
	}
	if err := os.MkdirAll(filepath.Dir(full), 0o755); err != nil {
		t.Fatal(err)
	}
	if link {
		if err := os.Symlink(target, full); err != nil {
			t.Fatal(err)
		}
		return
	}
	// git add -A keeps a submodule only while its directory exists.
	if err := os.Mkdir(full, 0o755); err != nil {
		t.Fatal(err)
	}
	w.Git("update-index", "--add", "--cacheinfo", "160000,"+commit+","+path)
}

// rate commits base on main, and change on c/x with message, and rates c/x.
func rate(t *testing.T, base, change map[string]string, messages ...string) *gitk8s.CheckResult {
	t.Helper()
	srv := gittest.NewServer(t, "")
	w := srv.NewWork(t, "app")
	w.Write("README.md", "hello\n")
	for path, content := range base {
		write(t, w, path, content)
	}
	main := w.Commit("main")
	w.Push("main")
	w.Branch("c/x", main)
	for path, content := range change {
		write(t, w, path, content)
	}
	var head string
	for _, message := range messages {
		head = w.Commit(message)
	}
	w.Push("c/x")

	b := &Branch{Object: kube.Meta("app-c-x", nil)}
	b.Namespace = "default"
	b.Spec = gitk8s.GitBranchSpec{
		Repository: "app", Branch: "c/x", Head: head, Parent: "main", ParentHead: main,
		Merge: &gitk8s.MergePolicy{Checks: []gitk8s.CheckPolicy{{Name: "risk"}}},
	}
	repo, _ := srv.Repository("app")
	ctx, _ := kube.Fake(t.Context(), b, repo)
	c := check
	c.Remote = srv.RemoteFor
	if err := checks.NewReconciler[Branch](c, &checks.Config{CacheDir: t.TempDir()}).Reconcile(ctx, b); err != nil {
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
			if res.ParentCommit != "" || res.MergeBase == "" {
				t.Errorf("result = %+v, want one for the change on top of its merge base, not for the parent's head", res)
			}
		})
	}
}

func TestRiskOfBinaryFilesAndSubmodules(t *testing.T) {
	*maxLines, *sensitive = 10, ""
	gitmodules := func(url string) string {
		return "[submodule \"lib\"]\n\tpath = lib\n\turl = " + url + "\n"
	}
	good, evil := gitmodules("https://github.com/good/lib"), gitmodules("https://github.com/evil/lib")
	c1, c2 := strings.Repeat("1", 40), strings.Repeat("2", 40)
	for _, c := range []struct {
		name         string
		base, change map[string]string
		level        string
		reason       string
	}{
		{name: "binary file", change: map[string]string{"tools/protoc": "\x7fELF\x02\x01\x01\x00" + strings.Repeat("\x00\x01", 2048)}, level: "high", reason: "changes binary files tools/protoc"},
		{name: "text file with a NUL byte", change: map[string]string{"app.js": "/* \x00 */\n" + strings.Repeat("run();\n", 50)}, level: "high", reason: "changes binary files app.js"},
		{name: "text file with a NUL byte after its first 8,000 bytes", change: map[string]string{"app.js": strings.Repeat("run();\n", 1200) + "/* \x00 */\n"}, level: "high", reason: "changes 1201 lines, more than 10"},
		{name: "new submodule", change: map[string]string{".gitmodules": good, "lib": submoduleAt + c1}, level: "high", reason: "changes .gitmodules; changes submodules lib"},
		{
			name:   "submodule that the change moves to another repository",
			base:   map[string]string{".gitmodules": good, "lib": submoduleAt + c1},
			change: map[string]string{".gitmodules": evil, "lib": submoduleAt + c2},
			level:  "high", reason: "changes .gitmodules; changes submodules lib",
		},
		{
			name:   "submodule that the change moves to another commit",
			base:   map[string]string{".gitmodules": good, "lib": submoduleAt + c1},
			change: map[string]string{"lib": submoduleAt + c2},
			level:  "high", reason: "changes submodules lib",
		},
		{
			name:   "submodule that the change leaves alone",
			base:   map[string]string{".gitmodules": good, "lib": submoduleAt + c1},
			change: map[string]string{"docs/a.md": "a\n"},
			level:  "low", reason: "changes 1 lines in 1 files",
		},
	} {
		t.Run(c.name, func(t *testing.T) {
			res := rate(t, c.base, c.change, "change")
			if res.State != gitk8s.Passed || res.Outputs["level"] != c.level || !strings.Contains(res.Message, c.reason) {
				t.Errorf("result = %+v, want level %s and %q", res, c.level, c.reason)
			}
			if res.ParentCommit != "" || res.MergeBase == "" {
				t.Errorf("result = %+v, want one for the change on top of its merge base, not for the parent's head", res)
			}
		})
	}
}

func TestRiskThatReadsTheMergeBase(t *testing.T) {
	*maxLines, *sensitive = 10, ""
	for _, c := range []struct {
		name         string
		base, change map[string]string
	}{
		{"go.mod", map[string]string{"go.mod": goMod}, map[string]string{"go.mod": strings.Replace(goMod, "b v0.4.0", "b v0.5.0", 1)}},
		{"symbolic link", nil, map[string]string{"a": symlinkTo + "/tmp"}},
	} {
		t.Run(c.name, func(t *testing.T) {
			if res := rate(t, c.base, c.change, "change"); res.ParentCommit == "" || res.MergeBase != "" {
				t.Errorf("result = %+v, want one for the parent's head, because the rating read go.mod files there", res)
			}
		})
	}
}

// TestRiskRatesEachChangeOnce rates a branch, then lands another branch on
// the parent, then merges the parent into the branch, as the base check
// does at the front of the queue.
func TestRiskRatesEachChangeOnce(t *testing.T) {
	*maxLines, *sensitive = 10, ""
	for _, c := range []struct {
		name   string
		change map[string]string
		runs   int
	}{
		{"a change to docs", map[string]string{"docs/a.md": "a\nb\n"}, 1},
		{"a change to go.mod", map[string]string{"go.mod": strings.Replace(goMod, "b v0.4.0", "b v0.5.0", 1)}, 3},
	} {
		t.Run(c.name, func(t *testing.T) {
			srv := gittest.NewServer(t, "")
			w := srv.NewWork(t, "app")
			w.Write("go.mod", goMod)
			start := w.Commit("main")
			w.Push("main")
			w.Branch("c/x", start)
			for path, content := range c.change {
				write(t, w, path, content)
			}
			head := w.Commit("change")
			w.Push("c/x")

			b := &Branch{Object: kube.Meta("app-c-x", nil)}
			b.Namespace = "default"
			b.Spec = gitk8s.GitBranchSpec{
				Repository: "app", Branch: "c/x", Head: head, Parent: "main", ParentHead: start,
				Merge: &gitk8s.MergePolicy{Checks: []gitk8s.CheckPolicy{{Name: "risk"}}},
			}
			repo, _ := srv.Repository("app")
			runs := 0
			counted := check
			counted.Remote = srv.RemoteFor
			counted.Run = func(ctx context.Context, in *checks.Input) (checks.Verdict, error) {
				runs++
				return run(ctx, in)
			}
			r := checks.NewReconciler[Branch](counted, &checks.Config{CacheDir: t.TempDir()})
			reconcileRisk := func() *gitk8s.CheckResult {
				t.Helper()
				ctx, _ := kube.Fake(t.Context(), b, repo)
				if err := r.Reconcile(ctx, b); err != nil {
					t.Fatal(err)
				}
				return b.Status.Checks.Result
			}
			first := reconcileRisk()

			w.Branch("main", start)
			w.Write("other.txt", "other\n")
			w.Commit("land another branch")
			w.Push("main")
			b.Spec.ParentHead = w.Git("rev-parse", "HEAD")
			reconcileRisk()

			w.Branch("c/x", head)
			w.Git("merge", "--quiet", "--no-edit", b.Spec.ParentHead)
			w.Push("c/x")
			b.Spec.Head = w.Git("rev-parse", "HEAD")
			res := reconcileRisk()
			if runs != c.runs || res.Commit != b.Spec.Head || res.Message != first.Message || !maps.Equal(res.Outputs, first.Outputs) {
				t.Errorf("%d runs, result for the merge %+v; want %d runs and the first rating, %+v", runs, res, c.runs, first)
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
		{name: "module that a go.mod file at the merge base declares", change: edit(")", "\texample.com/app/tools v0.1.0\n)"), level: "high", reason: "adds module example.com/app/tools"},
		{name: "module that a go.mod file at the merge base declares, replaced with its directory", change: edit(")", "\texample.com/app/tools v0.1.0\n)\n\nreplace example.com/app/tools => ./tools\n"), level: "low"},
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
		{name: "go.work in a subdirectory", change: map[string]string{"sub/go.work": "go 1.24\n\nuse ..\n"}, level: "high", reason: "changes sub/go.work"},
		{name: "go.work.sum", change: map[string]string{"go.work.sum": strings.Repeat("example.com/a v1.2.4 h1:abc=\n", 12)}, level: "low", reason: "changes 0 lines in 1 files, not counting go.sum"},
		{name: "new go.mod", change: map[string]string{"svc/go.mod": "module example.com/app/svc\n\ngo 1.24\n\nrequire example.com/a v1.2.3\n"}, level: "low"},
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
		{name: "godebug line", change: edit("go 1.24\n", "go 1.24\n\ngodebug x509sha1=1\n"), level: "high", reason: "changes the godebug lines in go.mod from none to x509sha1=1"},
		{name: "unreadable go.mod", change: map[string]string{"go.mod": "this isn't a go.mod file\n"}, level: "high", reason: "changes go.mod, which check-risk can't read"},
		{
			name:    "agent commit",
			change:  map[string]string{"main.go": "package main\n"},
			message: "Apply changes from the deps agent\n\n" + git.FixerTrailer + ": deps\n" + git.AgentTrailer + ": deps",
			level:   "high",
			reason:  "has changes from AI agents",
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

func TestRiskOfModFileLines(t *testing.T) {
	*maxLines, *sensitive = 10, ""
	const svcMod = "module example.com/app/svc\n\ngo 1.24\n"
	godebug := func(lines ...string) string {
		return goMod + "\ngodebug (\n\t" + strings.Join(lines, "\n\t") + "\n)\n"
	}
	root := map[string]string{"go.mod": goMod}
	for _, c := range []struct {
		name         string
		base, change map[string]string
		level        string
		reason       string
	}{
		{name: "new go.mod with the lines of its directory's module", base: root, change: map[string]string{"svc/go.mod": svcMod}, level: "low"},
		{
			name: "new go.mod with another go line", base: root,
			change: map[string]string{"svc/go.mod": strings.Replace(svcMod, "go 1.24", "go 1.99", 1)},
			level:  "high", reason: "changes the go line in svc/go.mod from 1.24 in go.mod to 1.99",
		},
		{
			name: "new go.mod without a go line", base: root,
			change: map[string]string{"svc/go.mod": "module example.com/app/svc\n"},
			level:  "high", reason: "changes the go line in svc/go.mod from 1.24 in go.mod to none",
		},
		{
			name: "new go.mod with a toolchain line", base: root,
			change: map[string]string{"svc/go.mod": svcMod + "\ntoolchain go1.99.1\n"},
			level:  "high", reason: "changes the toolchain line in svc/go.mod from none in go.mod to go1.99.1",
		},
		{
			name: "new go.mod with godebug lines", base: root,
			change: map[string]string{"svc/go.mod": svcMod + "\ngodebug (\n\tx509sha1=1\n\ttlsrsakex=1\n)\n"},
			level:  "high", reason: "changes the godebug lines in svc/go.mod from none in go.mod to tlsrsakex=1, x509sha1=1",
		},
		{
			name:   "new go.mod in a nested module",
			base:   map[string]string{"go.mod": goMod, "svc/go.mod": strings.Replace(svcMod, "go 1.24", "go 1.21", 1)},
			change: map[string]string{"svc/cmd/go.mod": "module example.com/app/svc/cmd\n\ngo 1.24\n"},
			level:  "high", reason: "changes the go line in svc/cmd/go.mod from 1.21 in svc/go.mod to 1.24",
		},
		{name: "new go.mod in no module", change: map[string]string{"svc/go.mod": svcMod}, level: "high", reason: "changes the go line in svc/go.mod from none to 1.24"},
		{
			name:   "go.mod that check-risk can't read at the merge base",
			base:   map[string]string{"go.mod": "this isn't a go.mod file\n"},
			change: root,
			level:  "high", reason: "changes the go line in go.mod from none to 1.24",
		},
		{
			name:   "godebug lines in another order",
			base:   map[string]string{"go.mod": godebug("tlsrsakex=1", "x509sha1=1")},
			change: map[string]string{"go.mod": godebug("x509sha1=1", "tlsrsakex=1")},
			level:  "low",
		},
		{
			name:   "godebug line that a later one overrides",
			base:   map[string]string{"go.mod": godebug("tlsrsakex=1", "tlsrsakex=0")},
			change: map[string]string{"go.mod": godebug("tlsrsakex=0", "tlsrsakex=1")},
			level:  "high", reason: "changes the godebug lines in go.mod from tlsrsakex=0 to tlsrsakex=1",
		},
	} {
		t.Run(c.name, func(t *testing.T) {
			res := rate(t, c.base, c.change, "change")
			if res.State != gitk8s.Passed || res.Outputs["level"] != c.level || !strings.Contains(res.Message, c.reason) {
				t.Errorf("result = %+v, want level %s and %q", res, c.level, c.reason)
			}
		})
	}
}

// TestRiskOfSquashedAgentCommits rates a branch with two commits from agents
// and a commit with the same files and both agent trailers, as a squash
// landing makes. The check is FilesOnly, so the two must get the same result.
func TestRiskOfSquashedAgentCommits(t *testing.T) {
	*maxLines, *sensitive = 10, ""
	fix := func(name string) string {
		return "Apply changes from the " + name + " agent\n\n" + git.FixerTrailer + ": " + name + "\n" + git.AgentTrailer + ": " + name
	}
	change := map[string]string{"main.go": "package main\n"}
	head := rate(t, nil, change, fix("deps"), fix("review"))
	squashed := rate(t, nil, change, "Change main.go\n\n"+git.AgentTrailer+": deps\n"+git.AgentTrailer+": review")
	if head.Outputs["level"] != "high" || head.Message != squashed.Message || !maps.Equal(head.Outputs, squashed.Outputs) {
		t.Errorf("head's result = %+v, squashed commit's = %+v, want the same high rating", head, squashed)
	}
}

func TestRiskOfLinkedReplacements(t *testing.T) {
	*maxLines, *sensitive = 10, ""
	replaceA := func(dir string) string {
		return strings.Replace(goMod, "replace ", "replace example.com/a => "+dir+"\nreplace ", 1)
	}
	const aMod = "module example.com/a\n\ngo 1.24\n"
	c1, c2 := strings.Repeat("1", 40), strings.Repeat("2", 40)
	for _, c := range []struct {
		name         string
		base, change map[string]string
		level        string
		reason       string
	}{
		{
			name:   "symbolic link to a directory outside the repository",
			base:   map[string]string{"go.mod": goMod},
			change: map[string]string{"go.mod": replaceA("./a"), "a": symlinkTo + "../../outside/a"},
			level:  "high", reason: "replaces example.com/a with ./a, which goes through the symbolic link a",
		},
		{
			name:   "symbolic link to an absolute directory",
			base:   map[string]string{"go.mod": goMod},
			change: map[string]string{"go.mod": replaceA("./a"), "a": symlinkTo + "/etc"},
			level:  "high", reason: "replaces example.com/a with ./a, which goes through the symbolic link a",
		},
		{
			name:   "symbolic link at the merge base",
			base:   map[string]string{"go.mod": goMod, "a": symlinkTo + "/tmp/outside"},
			change: map[string]string{"go.mod": replaceA("./a")},
			level:  "high", reason: "replaces example.com/a with ./a, which goes through the symbolic link a",
		},
		{
			name:   "symbolic link in the directory's path",
			base:   map[string]string{"go.mod": goMod},
			change: map[string]string{"go.mod": replaceA("./mods/a"), "mods": symlinkTo + "/tmp"},
			level:  "high", reason: "replaces example.com/a with ./mods/a, which goes through the symbolic link mods",
		},
		{
			name:   "symbolic link in the path from a subdirectory",
			base:   map[string]string{"go.mod": goMod, "tools/go.mod": toolsMod},
			change: map[string]string{"tools/go.mod": toolsMod + "replace example.com/u => ../mods/u\n", "mods": symlinkTo + "/tmp"},
			level:  "high", reason: "replaces example.com/u with ../mods/u, which goes through the symbolic link mods",
		},
		{
			name:   "submodule",
			base:   map[string]string{"go.mod": goMod},
			change: map[string]string{"go.mod": replaceA("./third_party/a"), "third_party/a": submoduleAt + c1},
			level:  "high", reason: "replaces example.com/a with ./third_party/a, which goes through the submodule third_party/a",
		},
		{
			name:   "directory in a submodule",
			base:   map[string]string{"go.mod": goMod, "third_party": submoduleAt + c1},
			change: map[string]string{"go.mod": replaceA("./third_party/a")},
			level:  "high", reason: "replaces example.com/a with ./third_party/a, which goes through the submodule third_party",
		},
		{
			name:   "module that the change requires through a symbolic link",
			base:   map[string]string{"go.mod": goMod},
			change: map[string]string{"go.mod": strings.Replace(goMod, ")", "\texample.com/c v0.0.0\n)\n\nreplace example.com/c => ./c\n", 1), "c": symlinkTo + "/tmp/c"},
			level:  "high", reason: "adds module example.com/c; replaces example.com/c with ./c, which goes through the symbolic link c",
		},
		{
			name:   "directory that the change replaces with a symbolic link",
			base:   map[string]string{"go.mod": replaceA("./a"), "a/go.mod": aMod},
			change: map[string]string{"a": symlinkTo + "/tmp/a"},
			level:  "high", reason: "changes the symbolic link a, which a replacement of example.com/a goes through",
		},
		{
			name:   "parent directory that the change replaces with a symbolic link",
			base:   map[string]string{"go.mod": replaceA("./third_party/a"), "third_party/a/go.mod": aMod},
			change: map[string]string{"third_party": symlinkTo + "/tmp"},
			level:  "high", reason: "changes the symbolic link third_party, which a replacement of example.com/a goes through",
		},
		{
			name:   "symbolic link that the change points elsewhere",
			base:   map[string]string{"go.mod": replaceA("./a"), "a": symlinkTo + "vendored/a"},
			change: map[string]string{"a": symlinkTo + "/tmp/a"},
			level:  "high", reason: "changes the symbolic link a, which a replacement of example.com/a goes through",
		},
		{
			name:   "submodule that the change moves to another commit",
			base:   map[string]string{"go.mod": replaceA("./third_party/a"), "third_party/a": submoduleAt + c1},
			change: map[string]string{"third_party/a": submoduleAt + c2},
			level:  "high", reason: "changes submodules third_party/a",
		},
		{
			name:   "submodule that the change leaves alone",
			base:   map[string]string{"go.mod": replaceA("./third_party/a"), "third_party/a": submoduleAt + c1},
			change: map[string]string{"go.mod": strings.Replace(replaceA("./third_party/a"), "b v0.4.0", "b v0.5.0", 1)},
			level:  "low",
		},
		{
			name:   "symbolic link that no replacement goes through",
			base:   map[string]string{"go.mod": replaceA("./ab"), "ab/go.mod": aMod},
			change: map[string]string{"a": symlinkTo + "/tmp"},
			level:  "low",
		},
	} {
		t.Run(c.name, func(t *testing.T) {
			res := rate(t, c.base, c.change, "change")
			if res.State != gitk8s.Passed || res.Outputs["level"] != c.level || !strings.Contains(res.Message, c.reason) {
				t.Errorf("result = %+v, want level %s and %q", res, c.level, c.reason)
			}
		})
	}
}

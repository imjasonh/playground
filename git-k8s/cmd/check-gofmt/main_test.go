package main

import (
	"strings"
	"testing"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/checks"
	"github.com/imjasonh/playground/git-k8s/internal/git"
	"github.com/imjasonh/playground/git-k8s/internal/gittest"
	"github.com/imjasonh/playground/kube"
)

const unformatted = "package util\nfunc  Add(a,b int)int{return a+b}\n"

func branch(t *testing.T, srv *gittest.Server, files map[string]string) (*Branch, *gittest.Work) {
	w := srv.NewWork(t, "app")
	w.Write("go.mod", "module example.com/app\n")
	main := w.Commit("main")
	w.Push("main")
	w.Branch("c/x", main)
	for path, content := range files {
		w.Write(path, content)
	}
	head := w.Commit("change")
	w.Push("c/x")
	b := &Branch{Object: kube.Meta("app-c-x", nil)}
	b.Namespace = "default"
	b.Spec = gitk8s.GitBranchSpec{
		Repository: "app", Branch: "c/x", Head: head, Parent: "main", ParentHead: main,
		Merge: &gitk8s.MergePolicy{Checks: []gitk8s.CheckPolicy{{Name: "gofmt", MayPush: true}}},
	}
	return b, w
}

func reconcile(t *testing.T, srv *gittest.Server, b *Branch) error {
	t.Helper()
	repo, secret := srv.Repository("app")
	ctx, _ := kube.Fake(t.Context(), b, repo, secret)
	cfg := &checks.Config{CacheDir: t.TempDir(), Identity: git.Identity{Name: "git-k8s", Email: "git-k8s@example.com"}}
	return checks.NewReconciler[Branch](check, cfg).Reconcile(ctx, b)
}

func TestFormatsGoFiles(t *testing.T) {
	srv := gittest.NewServer(t, "")
	b, w := branch(t, srv, map[string]string{
		"util/add.go":           unformatted,
		"vendor/x/x.go":         unformatted,
		"util/testdata/fixture": "not go",
		"util/testdata/bad.go":  unformatted,
	})
	if err := reconcile(t, srv, b); err != nil {
		t.Fatal(err)
	}
	res := b.Status.Checks.Result
	if res.State != gitk8s.Fixed || res.Outputs["files"] != "util/add.go" {
		t.Fatalf("result = %+v, want Fixed for util/add.go only", res)
	}
	fix := w.Fetch("c/x")
	if got := w.Show(fix, "util/add.go"); got != "package util\n\nfunc Add(a, b int) int { return a + b }" {
		t.Errorf("formatted util/add.go = %q", got)
	}
	if got := w.Show(fix, "vendor/x/x.go"); got+"\n" != unformatted {
		t.Errorf("vendor/x/x.go changed to %q", got)
	}
	if msg := w.Git("log", "-1", "--format=%B", fix); !strings.Contains(msg, git.FixerTrailer+": gofmt") {
		t.Errorf("fix message = %q", msg)
	}

	b.Spec.Head = fix
	if err := reconcile(t, srv, b); err != nil {
		t.Fatal(err)
	}
	if res := b.Status.Checks.Result; res.State != gitk8s.Passed {
		t.Errorf("result for the fix = %+v, want Passed", res)
	}
}

func TestSyntaxErrorFails(t *testing.T) {
	srv := gittest.NewServer(t, "")
	b, _ := branch(t, srv, map[string]string{"broken.go": "package main\nfunc {\n"})
	if err := reconcile(t, srv, b); err != nil {
		t.Fatal(err)
	}
	if res := b.Status.Checks.Result; res.State != gitk8s.Failed || !strings.Contains(res.Message, "can't parse broken.go") {
		t.Errorf("result = %+v, want a parse failure", res)
	}
}

func TestIsGo(t *testing.T) {
	for path, want := range map[string]bool{
		"main.go":               true,
		"a/b/c.go":              true,
		"vendor/x.go":           false,
		"a/testdata/x.go":       false,
		"main.go.txt":           false,
		"vendors/ok.go":         true,
		"a/testdata_helpers.go": true,
	} {
		if got := isGo(git.TreeEntry{Mode: "100644", Type: "blob", Path: path}); got != want {
			t.Errorf("isGo(%q) = %v, want %v", path, got, want)
		}
	}
	if isGo(git.TreeEntry{Mode: "120000", Type: "blob", Path: "link.go"}) {
		t.Error("isGo is true for a symlink")
	}
}

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

// setup pushes main with a.txt, moves main ahead with mainEdit, and pushes
// c/x from the first commit with branchEdit. It returns the branch's view.
func setup(t *testing.T, srv *gittest.Server, mainEdit, branchEdit string) (*Branch, *gittest.Work) {
	w := srv.NewWork(t, "app")
	w.Write("a.txt", "one\n")
	base := w.Commit("base")
	w.Write("a.txt", mainEdit)
	parent := w.Commit("main edit")
	w.Push("main")
	w.Branch("c/x", base)
	w.Write("b.txt", branchEdit)
	head := w.Commit("branch edit")
	w.Push("c/x")
	b := &Branch{Object: kube.Meta("app-c-x", nil)}
	b.Namespace = "default"
	b.Spec = gitk8s.GitBranchSpec{
		Repository: "app", Branch: "c/x", Head: head, Parent: "main", ParentHead: parent,
		Merge: &gitk8s.MergePolicy{Checks: []gitk8s.CheckPolicy{{Name: "base", MayPush: true}}},
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

func TestMergesParentIn(t *testing.T) {
	srv := gittest.NewServer(t, "pw")
	b, w := setup(t, srv, "main\n", "branch\n")
	if err := reconcile(t, srv, b); err != nil {
		t.Fatal(err)
	}
	res := b.Status.Checks.Result
	if res.State != gitk8s.Fixed || res.ParentCommit != b.Spec.ParentHead {
		t.Fatalf("result = %+v, want Fixed for both heads", res)
	}
	fix := w.Fetch("c/x")
	if fix != res.Outputs["fix"] {
		t.Fatalf("c/x = %s, want %s", fix, res.Outputs["fix"])
	}
	if parents := w.Git("log", "-1", "--format=%P", fix); parents != b.Spec.Head+" "+b.Spec.ParentHead {
		t.Errorf("merge parents = %q", parents)
	}
	if msg := w.Git("log", "-1", "--format=%B", fix); !strings.Contains(msg, "Merge main into c/x") || !strings.Contains(msg, git.FixerTrailer+": base") {
		t.Errorf("merge message = %q", msg)
	}

	b.Spec.Head = fix
	if err := reconcile(t, srv, b); err != nil {
		t.Fatal(err)
	}
	if res := b.Status.Checks.Result; res.State != gitk8s.Passed {
		t.Errorf("result after the merge = %+v, want Passed", res)
	}
}

func TestPassesWhenParentContainsBranch(t *testing.T) {
	srv := gittest.NewServer(t, "")
	b, w := setup(t, srv, "main\n", "branch\n")
	// main merges the branch and moves on, so it contains the branch.
	w.Branch("main", b.Spec.Head)
	w.Write("c.txt", "later\n")
	b.Spec.ParentHead = w.Commit("main moves past the branch")
	w.Push("main")
	head := b.Spec.Head
	if err := reconcile(t, srv, b); err != nil {
		t.Fatal(err)
	}
	if res := b.Status.Checks.Result; res.State != gitk8s.Passed || !strings.Contains(res.Message, "already contains") {
		t.Errorf("result = %+v, want Passed because main contains the branch", res)
	}
	if got := srv.Heads(t, "app")["c/x"]; got != head {
		t.Errorf("c/x moved to %s; a contained branch needs no merge", got)
	}
}

func TestConflictFails(t *testing.T) {
	srv := gittest.NewServer(t, "")
	b, w := setup(t, srv, "main\n", "branch\n")
	// Make the branch edit the line that main edited.
	w.Write("a.txt", "branch\n")
	b.Spec.Head = w.Commit("conflicting edit")
	w.Push("c/x")
	if err := reconcile(t, srv, b); err != nil {
		t.Fatal(err)
	}
	res := b.Status.Checks.Result
	if res.State != gitk8s.Failed || res.Outputs["conflicts"] != "a.txt" {
		t.Errorf("result = %+v, want Failed with a.txt in conflict", res)
	}
}

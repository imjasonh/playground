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
	b.Spec = gitk8s.TrackedBranchSpec{
		Repository: "app", Branch: "c/x", Head: head, Parent: "main", ParentHead: parent,
		Merge: &gitk8s.MergePolicy{Checks: []gitk8s.CheckPolicy{{Name: "base", MayPush: true}}},
	}
	return b, w
}

// reconcile runs the check with world's objects. A Signer in world makes
// the TrackedRepository name its key.
func reconcile(t *testing.T, srv *gittest.Server, b *Branch, world ...any) error {
	t.Helper()
	repo, _ := srv.Repository("app")
	objs := []any{repo}
	for _, o := range world {
		if s, ok := o.(*gittest.Signer); ok {
			o = s.Sign(repo)
		}
		objs = append(objs, o)
	}
	ctx, _ := kube.Fake(t.Context(), b, objs...)
	c := check
	c.Remote = srv.RemoteFor
	cfg := &checks.Config{CacheDir: t.TempDir(), Identity: git.Identity{Name: "git-k8s", Email: "git-k8s@example.com"}}
	return checks.NewReconciler[Branch](c, cfg).Reconcile(ctx, b)
}

// at returns b's place in its parent's merge queue at its current head, as
// the merge controller writes it.
func at(b *Branch, position int32) *queued {
	q := &queued{Object: kube.Meta(b.Name, nil)}
	q.Namespace = b.Namespace
	q.Status.Queued = &gitk8s.Queued{Head: b.Spec.Head, Position: position}
	return q
}

func TestMergesParentIn(t *testing.T) {
	srv := gittest.NewServer(t, "pw")
	b, w := setup(t, srv, "main\n", "branch\n")
	if err := reconcile(t, srv, b, at(b, 1)); err != nil {
		t.Fatal(err)
	}
	res := b.Status.Checks.Result
	if res.State != gitk8s.Fixed || res.ParentCommit != b.Spec.ParentHead {
		t.Fatalf("result = %+v, want Fixed for both heads", res)
	}
	fix := w.Fetch("c/x")
	if fix != res.Fix {
		t.Fatalf("c/x = %s, want %s", fix, res.Fix)
	}
	if parents := w.Git("log", "-1", "--format=%P", fix); parents != b.Spec.Head+" "+b.Spec.ParentHead {
		t.Errorf("merge parents = %q", parents)
	}
	if msg := w.Git("log", "-1", "--format=%B", fix); !strings.Contains(msg, "Merge main into c/x") || !strings.Contains(msg, git.FixerTrailer+": base") {
		t.Errorf("merge message = %q", msg)
	}

	b.Spec.Head = fix
	if err := reconcile(t, srv, b, at(b, 1)); err != nil {
		t.Fatal(err)
	}
	if res := b.Status.Checks.Result; res.State != gitk8s.Passed {
		t.Errorf("result after the merge = %+v, want Passed", res)
	}
}

func TestSignsMerge(t *testing.T) {
	srv := gittest.NewServer(t, "")
	b, w := setup(t, srv, "main\n", "branch\n")
	signer := gittest.NewSigner(t, "git-k8s@example.com")
	if err := reconcile(t, srv, b, signer, at(b, 1)); err != nil {
		t.Fatal(err)
	}
	fix := w.Fetch("c/x")
	if res := b.Status.Checks.Result; res.State != gitk8s.Fixed || res.Fix != fix {
		t.Fatalf("result = %+v, want Fixed with the pushed merge %s", res, fix)
	}
	if err := signer.Verify(w.Dir, fix); err != nil {
		t.Error(err)
	}
}

func TestMergesParentInAtTheFrontOfTheQueue(t *testing.T) {
	srv := gittest.NewServer(t, "")
	b, _ := setup(t, srv, "main\n", "branch\n")
	head := b.Spec.Head
	old := at(b, 1)
	old.Status.Queued.Head = "0000000"
	for _, step := range []struct {
		name  string
		world []any
	}{
		{"out of the queue", nil},
		{"at the front at an older head", []any{old}},
		{"second in the queue", []any{at(b, 2)}},
	} {
		if err := reconcile(t, srv, b, step.world...); err != nil {
			t.Fatal(err)
		}
		res := b.Status.Checks.Result
		if res.State != gitk8s.Passed || res.Outputs["behind"] != "true" || !strings.Contains(res.Message, "behind main") {
			t.Errorf("%s: result = %+v, want Passed and behind", step.name, res)
		}
		if got := srv.Heads(t, "app")["c/x"]; got != head {
			t.Fatalf("%s: c/x moved to %s before reaching the front of the queue", step.name, got)
		}
	}

	t.Log("At the front, the passing result is stale, so the check runs again and merges main in.")
	if err := reconcile(t, srv, b, at(b, 1)); err != nil {
		t.Fatal(err)
	}
	res := b.Status.Checks.Result
	if res.State != gitk8s.Fixed || srv.Heads(t, "app")["c/x"] != res.Fix {
		t.Errorf("result = %+v, want Fixed with the merge pushed", res)
	}
}

func TestWaitsForTheParentToBeListedAgain(t *testing.T) {
	srv := gittest.NewServer(t, "")
	b, w := setup(t, srv, "main\n", "branch\n")
	w.Branch("main", b.Spec.ParentHead)
	w.Write("c.txt", "later\n")
	w.Commit("main moves after it was listed")
	w.Push("main")
	head := b.Spec.Head
	if err := reconcile(t, srv, b, at(b, 1)); err == nil || !strings.Contains(err.Error(), "waiting for the repository controller") {
		t.Errorf("err = %v, want to wait for main to be listed again", err)
	}
	if got := srv.Heads(t, "app")["c/x"]; got != head {
		t.Errorf("c/x moved to %s; a merge of main's old head would need another merge", got)
	}
}

func TestBehindFailsWithoutPush(t *testing.T) {
	srv := gittest.NewServer(t, "")
	b, _ := setup(t, srv, "main\n", "branch\n")
	b.Spec.Merge.Checks[0].MayPush = false
	head := b.Spec.Head
	if err := reconcile(t, srv, b); err != nil {
		t.Fatal(err)
	}
	if res := b.Status.Checks.Result; res.State != gitk8s.Failed || !strings.Contains(res.Message, "doesn't let this check push") {
		t.Errorf("result = %+v, want Failed because the policy doesn't let the check push the merge", res)
	}
	if got := srv.Heads(t, "app")["c/x"]; got != head {
		t.Errorf("c/x moved to %s", got)
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

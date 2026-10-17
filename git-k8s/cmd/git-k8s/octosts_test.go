package main

import (
	"testing"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/internal/git"
	"github.com/imjasonh/playground/git-k8s/internal/gittest"
	"github.com/imjasonh/playground/git-k8s/internal/mirror"
	"github.com/imjasonh/playground/kube"
)

// newGitHub starts a fake GitHub whose repository acme/app has, on main,
// the trust policies git, which grants contents: write, and checks, which
// grants checks: write. It returns a working repository at main.
func newGitHub(t *testing.T) (*gittest.GitHub, *gittest.Work, string) {
	gh := gittest.NewGitHub(t)
	w := gh.NewWork(t, "app")
	w.Write(".github/chainguard/git.sts.yaml", gittest.TrustPolicy(map[string]string{"contents": "write"}))
	w.Write(".github/chainguard/checks.sts.yaml", gittest.TrustPolicy(map[string]string{"checks": "write"}))
	main := w.Commit("main")
	w.Push("main")
	return gh, w, main
}

// newRepositories returns a repositories controller whose mirror keeps its
// copies in a new directory.
func newRepositories(t *testing.T) *repositories {
	return &repositories{mirror: &mirror.Mirror{Git: &git.Git{}, Dir: t.TempDir()}}
}

func TestListsWithOctoSTS(t *testing.T) {
	gh, w, main := newGitHub(t)
	w.Branch("c/add", main)
	add := w.Commit("add")
	w.Push("c/add")
	repo := gh.Repository("app", gitk8s.OctoSTS{GitIdentity: "git"}, rules()...)
	ctx, rec := kube.Fake(t.Context(), repo)
	if err := newRepositories(t).Reconcile(ctx, repo); err != nil {
		t.Fatal(err)
	}
	heads := map[string]string{}
	for _, b := range kube.Owned[gitk8s.Branch](rec) {
		heads[b.Spec.Branch] = b.Spec.Head
	}
	if len(heads) != 2 || heads["main"] != main || heads["c/add"] != add {
		t.Errorf("tracked heads %v, want main at %s and c/add at %s", heads, main, add)
	}
	if c := kube.FindCondition(repo.Status.Conditions, "Ready"); c == nil || c.Status != kube.True {
		t.Errorf("Ready = %+v", c)
	}
	if ex := gh.Fake.Exchanges(); len(ex) != 1 || ex[0].Scope != "acme/app" || ex[0].Identity != "git" {
		t.Errorf("exchanges = %+v, want one for identity git in acme/app", ex)
	}
}

// The merge controller lands c/x in the mirror's copy, and the mirror pushes
// the landing to GitHub with a token for gitIdentity.
func TestLandsWithOctoSTS(t *testing.T) {
	gh, w, main := newGitHub(t)
	w.Branch("c/x", main)
	w.Write("x.txt", "x\n")
	head := w.Commit("add x")
	w.Push("c/x")
	repo := gh.Repository("app", gitk8s.OctoSTS{GitIdentity: "git"}, rules()...)
	repo.UID = "uid-1"
	r := newRepositories(t)
	sync := func() {
		t.Helper()
		ctx, _ := kube.Fake(t.Context(), repo)
		if err := r.Reconcile(ctx, repo); err != nil {
			t.Fatal(err)
		}
	}
	sync()
	b := &gitk8s.Branch{Object: kube.Meta(gitk8s.BranchObjectName("app", "c/x"), nil)}
	b.Namespace = "default"
	b.Spec = gitk8s.BranchSpec{Repository: "app", Branch: "c/x", Head: head, Parent: "main", ParentHead: main, Merge: policy}
	b.Status.Checks = map[string]gitk8s.CheckResult{
		"base":  {Commit: head, Scope: gitk8s.ScopeParent, ParentCommit: main, State: gitk8s.Passed},
		"gofmt": {Commit: head, Scope: gitk8s.ScopeHead, State: gitk8s.Passed},
	}
	// policy queues branches, and only the front of main's queue lands.
	b.Status.Queued = &gitk8s.Queued{Head: head, Position: 1}
	ctx, _ := kube.Fake(t.Context(), b, repo, parentOf(b, "c/x"))
	if err := (&merger{mirror: r.mirror}).Reconcile(ctx, b); err != nil || b.Status.State != gitk8s.MergeStateLanded {
		t.Fatalf("err = %v, state = %q", err, b.Status.State)
	}
	sync()
	if c := kube.FindCondition(repo.Status.Conditions, "ExternalSynced"); c == nil || c.Status != kube.True {
		t.Errorf("ExternalSynced = %+v", c)
	}
	for _, ex := range gh.Fake.Exchanges() {
		if ex.Identity != "git" {
			t.Errorf("exchanged a token for identity %s, want only git", ex.Identity)
		}
	}
	heads := gh.Heads(t, "app")
	if heads["main"] != head {
		t.Errorf("main = %s, want %s", heads["main"], head)
	}
	if _, ok := heads["c/x"]; ok {
		t.Error("c/x wasn't deleted after it landed")
	}
}

package main

import (
	"strings"
	"testing"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/checks"
	"github.com/imjasonh/playground/git-k8s/internal/gittest"
	"github.com/imjasonh/playground/kube"
)

const head = "0123456789abcdef0123456789abcdef01234567"

func approve(t *testing.T, annotation, approver string, prior *gitk8s.CheckResult) *gitk8s.CheckResult {
	t.Helper()
	b := &Branch{Object: kube.Meta("app-c-x", nil)}
	b.Namespace = "default"
	b.Annotations = map[string]string{}
	if annotation != "" {
		b.Annotations[gitk8s.ApproveAnnotation] = annotation
	}
	if approver != "" {
		b.Annotations[gitk8s.ApprovedByAnnotation] = approver
	}
	b.Spec = gitk8s.GitBranchSpec{
		Repository: "app", Branch: "c/x", Head: head, Parent: "main", ParentHead: "fedcba9876543210fedcba9876543210fedcba98",
		Merge: &gitk8s.MergePolicy{Checks: []gitk8s.CheckPolicy{{Name: "approval"}}},
	}
	b.Status.Checks.Result = prior
	repo := &gitk8s.GitRepository{Object: kube.Meta("app", nil)}
	repo.Namespace = "default"
	ctx, _ := kube.Fake(t.Context(), b, repo)
	if err := checks.NewReconciler[Branch](check, &checks.Config{}).Reconcile(ctx, b); err != nil {
		t.Fatal(err)
	}
	return b.Status.Checks.Result
}

func TestApproval(t *testing.T) {
	if res := approve(t, "", "", nil); res.State != gitk8s.Failed || !strings.Contains(res.Message, "isn't approved") {
		t.Errorf("unapproved: %+v", res)
	}
	if res := approve(t, head[:7], "", nil); res.State != gitk8s.Passed {
		t.Errorf("approved by prefix: %+v", res)
	}
	if res := approve(t, head[:6], "", nil); res.State != gitk8s.Failed {
		t.Errorf("a 6-character prefix approved: %+v", res)
	}
	if res := approve(t, "fedcba98", "", nil); res.State != gitk8s.Failed || !strings.Contains(res.Message, "the approval is for fedcba98") {
		t.Errorf("approval of another commit: %+v", res)
	}
	// The check reruns even with a final result for the head, so a new
	// annotation takes effect.
	prior := &gitk8s.CheckResult{Commit: head, State: gitk8s.Failed, Message: "0123456789ab isn't approved"}
	if res := approve(t, head, "", prior); res.State != gitk8s.Passed {
		t.Errorf("approval after a failure: %+v", res)
	}
}

func TestApprover(t *testing.T) {
	res := approve(t, head[:7], "alice", nil)
	if res.State != gitk8s.Passed || res.Outputs["approver"] != "alice" || !strings.Contains(res.Message, "approved by alice") {
		t.Errorf("approved by alice: %+v", res)
	}
	// An approval from before the admission policy has no approved-by. Its
	// approver output is empty rather than missing, so a gate that compares
	// it evaluates to false instead of failing.
	res = approve(t, head, "", nil)
	if approver, ok := res.Outputs["approver"]; res.State != gitk8s.Passed || !ok || approver != "" {
		t.Errorf("approved without approved-by: %+v", res)
	}
	// Only a passing result names the approver, so a gate that requires an
	// approver doesn't pass once the approval is for another commit.
	prior := &gitk8s.CheckResult{Commit: head, State: gitk8s.Passed, Message: "0123456789ab is approved by alice", Outputs: map[string]string{"approver": "alice"}}
	if res := approve(t, "fedcba98", "alice", prior); res.State != gitk8s.Failed || len(res.Outputs) != 0 {
		t.Errorf("approval of another commit by alice: %+v", res)
	}
	if res := approve(t, "", "", prior); res.State != gitk8s.Failed || len(res.Outputs) != 0 {
		t.Errorf("removed approval: %+v", res)
	}
}

// TestApprovalFollowsTheChange approves a branch's commit after the base
// check merged the parent into the branch, as it does at the front of the
// queue. Then it moves the parent, rebases the branch, and adds code.
func TestApprovalFollowsTheChange(t *testing.T) {
	srv := gittest.NewServer(t, "")
	w := srv.NewWork(t, "app")
	w.Write("README.md", "hello\n")
	start := w.Commit("main")
	w.Push("main")
	w.Branch("c/x", start)
	w.Write("a.txt", "a\n")
	approved := w.Commit("change")
	w.Push("c/x")
	w.Branch("main", start)
	w.Write("other.txt", "other\n")
	parent := w.Commit("land another branch")
	w.Push("main")
	w.Branch("c/x", approved)
	w.Git("merge", "--quiet", "--no-edit", parent)
	merge := w.Git("rev-parse", "HEAD")
	w.Push("c/x")

	b := &Branch{Object: kube.Meta("app-c-x", nil)}
	b.Namespace = "default"
	b.Spec = gitk8s.GitBranchSpec{
		Repository: "app", Branch: "c/x", Head: merge, Parent: "main", ParentHead: parent,
		Merge: &gitk8s.MergePolicy{Checks: []gitk8s.CheckPolicy{{Name: "approval"}}},
	}
	repo, _ := srv.Repository("app")
	c := check
	c.Remote = srv.RemoteFor
	r := checks.NewReconciler[Branch](c, &checks.Config{CacheDir: t.TempDir()})
	reconcile := func(annotation string) *gitk8s.CheckResult {
		t.Helper()
		b.Annotations = map[string]string{gitk8s.ApproveAnnotation: annotation, gitk8s.ApprovedByAnnotation: "alice"}
		ctx, _ := kube.Fake(t.Context(), b, repo)
		if err := r.Reconcile(ctx, b); err != nil {
			t.Fatal(err)
		}
		return b.Status.Checks.Result
	}
	lands := func(res *gitk8s.CheckResult) bool {
		gate := gitk8s.LandingGateChecks(b.Spec.Merge, map[string]gitk8s.CheckResult{"approval": *res}, b.Spec.Head, b.Spec.ParentHead)
		return gate["approval"].State == gitk8s.Passed
	}

	res := reconcile(approved)
	want := gitk8s.Short(approved) + " is approved by alice, and " + gitk8s.Short(merge) + " makes the same change"
	if res.State != gitk8s.Passed || res.Message != want || res.Outputs["approver"] != "alice" || res.MergeBase != parent || !lands(res) {
		t.Errorf("approval of the commit before base's merge: %+v, want %q for the change on top of %s", res, want, gitk8s.Short(parent))
	}
	if res := reconcile(approved[:12]); res.State != gitk8s.Failed || !strings.Contains(res.Message, "the approval is for "+approved[:12]) {
		t.Errorf("approval of the commit before base's merge by a prefix: %+v, want one only for that commit", res)
	}
	if res := reconcile(parent); res.State != gitk8s.Failed || !strings.Contains(res.Message, "doesn't make the same change") {
		t.Errorf("approval of the parent's head: %+v, want one only for an empty change", res)
	}
	if res := reconcile(strings.Repeat("ab", 20)); res.State != gitk8s.Failed || !strings.Contains(res.Message, "isn't in the repository") {
		t.Errorf("approval of a commit that the repository doesn't have: %+v", res)
	}

	// After another branch lands, the approval holds for the change on top
	// of the parent's old head, so the branch doesn't land until base merges
	// the parent again.
	w.Branch("main", parent)
	w.Write("third.txt", "third\n")
	b.Spec.ParentHead = w.Commit("land a third branch")
	w.Push("main")
	if res := reconcile(approved); res.State != gitk8s.Passed || res.MergeBase != parent || lands(res) {
		t.Errorf("approval after the parent moved: %+v, want one for the change on top of %s that doesn't land", res, gitk8s.Short(parent))
	}

	w.Branch("c/x", approved)
	w.Git("rebase", "--quiet", b.Spec.ParentHead)
	b.Spec.Head = w.Git("rev-parse", "HEAD")
	w.Push("c/x")
	if res := reconcile(approved); res.State != gitk8s.Passed || res.MergeBase != b.Spec.ParentHead || !lands(res) {
		t.Errorf("approval after a rebase: %+v", res)
	}

	w.Write("b.txt", "b\n")
	b.Spec.Head = w.Commit("more")
	w.Push("c/x")
	if res := reconcile(approved); res.State != gitk8s.Failed || !strings.Contains(res.Message, "doesn't make the same change") || len(res.Outputs) != 0 || lands(res) {
		t.Errorf("approval after another commit: %+v", res)
	}
}

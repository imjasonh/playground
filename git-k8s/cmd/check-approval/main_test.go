package main

import (
	"strings"
	"testing"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/checks"
	"github.com/imjasonh/playground/kube"
)

const head = "0123456789abcdef0123456789abcdef01234567"

func approve(t *testing.T, annotation string, prior *gitk8s.CheckResult) *gitk8s.CheckResult {
	t.Helper()
	b := &Branch{Object: kube.Meta("app-c-x", nil)}
	b.Namespace = "default"
	if annotation != "" {
		b.Annotations = map[string]string{gitk8s.ApproveAnnotation: annotation}
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
	if res := approve(t, "", nil); res.State != gitk8s.Failed || !strings.Contains(res.Message, "isn't approved") {
		t.Errorf("unapproved: %+v", res)
	}
	if res := approve(t, head[:7], nil); res.State != gitk8s.Passed {
		t.Errorf("approved by prefix: %+v", res)
	}
	if res := approve(t, head[:6], nil); res.State != gitk8s.Failed {
		t.Errorf("a 6-character prefix approved: %+v", res)
	}
	if res := approve(t, "fedcba98", nil); res.State != gitk8s.Failed || !strings.Contains(res.Message, "the approval is for fedcba98") {
		t.Errorf("approval of another commit: %+v", res)
	}
	// The check reruns even with a final result for the head, so a new
	// annotation takes effect.
	prior := &gitk8s.CheckResult{Commit: head, State: gitk8s.Failed, Message: "0123456789ab isn't approved"}
	if res := approve(t, head, prior); res.State != gitk8s.Passed {
		t.Errorf("approval after a failure: %+v", res)
	}
}

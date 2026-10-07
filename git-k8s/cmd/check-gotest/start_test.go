package main

import (
	"errors"
	"testing"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/checks"
	"github.com/imjasonh/playground/kube"
)

func TestReportsWhyThePodDidntStart(t *testing.T) {
	b, repo := branch()
	name := podName("app-c-x", head, 1)
	reconcileWith(t, b, repo)
	if res := b.Status.Checks.Result; res.State != gitk8s.Running || res.Message != "starting Pod "+name {
		t.Fatalf("result = %+v, want Running while kube starts the Pod", res)
	}

	t.Log("When kube couldn't create the Pod, the check reports why and declares the Pod again, so kube retries.")
	denied := errors.New(`applying Pod.v1 default/` + name + `: pods "` + name + `" is forbidden: ` +
		`ValidatingAdmissionPolicy 'git-k8s-check-pods' with binding 'git-k8s-check-pods' denied request: ` +
		`the gotest check can't create or change Pods in namespace default, which doesn't have the label ` +
		`git-k8s.imjasonh.com/check-pods=true (422 Invalid)`)
	ctx, rec := kube.Fake(t.Context(), b, repo, denied)
	if err := checks.NewReconciler[Branch](new(gotest).check(), &checks.Config{}).Reconcile(ctx, b); err != nil {
		t.Fatal(err)
	}
	res := b.Status.Checks.Result
	if want := "starting Pod " + name + "; the last try failed: " + denied.Error(); res.State != gitk8s.Running || res.Message != want {
		t.Errorf("result = %+v, want Running with the message %q", res, want)
	}
	if res.Pod != name || res.Notes["attempt"] != "1" {
		t.Errorf("result = %+v, want the same Pod and attempt", res)
	}
	if pods := kube.Owned[Pod](rec); len(pods) != 1 || pods[0].Name != name {
		t.Errorf("owned Pods = %+v, want the Pod declared again", pods)
	}
}

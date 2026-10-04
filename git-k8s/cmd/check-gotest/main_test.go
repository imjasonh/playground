package main

import (
	"encoding/json"
	"maps"
	"slices"
	"strings"
	"testing"
	"time"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/checks"
	"github.com/imjasonh/playground/kube"
)

const head = "0123456789abcdef0123456789abcdef01234567"

func branch() (*Branch, *gitk8s.GitRepository) {
	b := &Branch{Object: kube.Meta("app-c-x", nil)}
	b.Namespace = "default"
	b.Spec = gitk8s.GitBranchSpec{
		Repository: "app", Branch: "c/x", Head: head, Parent: "main", ParentHead: "fedcba9876543210fedcba9876543210fedcba98",
		Merge: &gitk8s.MergePolicy{Checks: []gitk8s.CheckPolicy{{Name: "gotest"}}},
	}
	repo := &gitk8s.GitRepository{Object: kube.Meta("app", nil), Spec: gitk8s.GitRepositorySpec{
		URL: "http://git.example.com/app.git", SecretRef: &gitk8s.SecretRef{Name: "app-creds"},
	}}
	repo.Namespace = "default"
	return b, repo
}

// reconcileWith runs the check with world holding the Pods that exist.
func reconcileWith(t *testing.T, b *Branch, repo *gitk8s.GitRepository, pods ...*Pod) *kube.Recorder {
	t.Helper()
	world := []any{repo}
	for _, p := range pods {
		world = append(world, p)
	}
	ctx, rec := kube.Fake(t.Context(), b, world...)
	if err := checks.NewReconciler[Branch](check, &checks.Config{}).Reconcile(ctx, b); err != nil {
		t.Fatal(err)
	}
	return rec
}

func TestStartsSandboxedPod(t *testing.T) {
	b, repo := branch()
	rec := reconcileWith(t, b, repo)
	res := b.Status.Checks.Result
	if res.State != gitk8s.Running || res.Outputs["attempt"] != "1" {
		t.Fatalf("result = %+v, want Running on attempt 1", res)
	}
	pods := kube.Owned[Pod](rec)
	if len(pods) != 1 || pods[0].Name != podName("app-c-x", head, 1) || res.Outputs["pod"] != pods[0].Name {
		t.Fatalf("owned Pods = %+v", pods)
	}
	spec := pods[0].Spec
	if *spec.AutomountServiceAccountToken || !*spec.SecurityContext.RunAsNonRoot || spec.RestartPolicy != "Never" {
		t.Errorf("Pod spec isn't locked down: %+v", spec)
	}
	for _, c := range append(spec.InitContainers, spec.Containers...) {
		sc := c.SecurityContext
		if *sc.AllowPrivilegeEscalation || !*sc.ReadOnlyRootFilesystem || !slices.Equal(sc.Capabilities.Drop, []string{"ALL"}) {
			t.Errorf("container %s isn't locked down: %+v", c.Name, sc)
		}
	}
	hasSecret := func(c Container) bool {
		return slices.ContainsFunc(c.Env, func(e EnvVar) bool { return e.ValueFrom != nil })
	}
	if !hasSecret(spec.InitContainers[0]) || hasSecret(spec.Containers[0]) {
		t.Error("only the fetch container can see the repository's credentials")
	}
}

func TestPodNeverSeesSigningKey(t *testing.T) {
	b, repo := branch()
	repo.Spec.SigningKeyRef = &gitk8s.SecretRef{Name: "app-signing"}
	pods := kube.Owned[Pod](reconcileWith(t, b, repo))
	if len(pods) != 1 {
		t.Fatalf("owned Pods = %+v", pods)
	}
	spec, err := json.Marshal(pods[0].Spec)
	if err != nil {
		t.Fatal(err)
	}
	if strings.Contains(string(spec), "app-signing") {
		t.Errorf("the test Pod refers to the signing key's Secret: %s", spec)
	}
}

func pod(phase string, init, test *Terminated) *Pod {
	p := &Pod{Object: kube.Meta(podName("app-c-x", head, 1), nil)}
	p.Namespace = "default"
	p.Status.Phase = phase
	if init != nil {
		s := ContainerStatus{Name: "fetch"}
		s.State.Terminated = init
		p.Status.InitContainerStatuses = []ContainerStatus{s}
	}
	if test != nil {
		s := ContainerStatus{Name: "test"}
		s.State.Terminated = test
		p.Status.ContainerStatuses = []ContainerStatus{s}
	}
	return p
}

func TestReportsPodResult(t *testing.T) {
	b, repo := branch()
	rec := reconcileWith(t, b, repo, pod("Succeeded", &Terminated{}, &Terminated{}))
	if res := b.Status.Checks.Result; res.State != gitk8s.Passed {
		t.Errorf("result = %+v, want Passed", res)
	}
	if rec.RequeueAfter() != time.Second {
		t.Errorf("RequeueAfter = %v; the next reconcile deletes the Pod", rec.RequeueAfter())
	}

	b, repo = branch()
	reconcileWith(t, b, repo, pod("Failed", &Terminated{}, &Terminated{ExitCode: 1, Message: "--- FAIL: TestAdd\nFAIL\texample.com/app\t0.01s"}))
	if res := b.Status.Checks.Result; res.State != gitk8s.Failed || !strings.Contains(res.Message, "--- FAIL: TestAdd") {
		t.Errorf("result = %+v, want Failed with the test output", res)
	}

	b, repo = branch()
	offline := "add_test.go:3:8: example.com/dep@v1.0.0: module lookup disabled by GOPROXY=off"
	reconcileWith(t, b, repo, pod("Failed", &Terminated{}, &Terminated{ExitCode: 1, Message: offline}))
	if res := b.Status.Checks.Result; res.State != gitk8s.Failed || !strings.Contains(res.Message, "vendor the dependencies, or set -goproxy") {
		t.Errorf("result = %+v, want Failed with advice about -goproxy", res)
	}
}

func runningPod(ns, name string) *Pod {
	p := &Pod{Object: kube.Meta(name, maps.Clone(testPodLabels))}
	p.Namespace = ns
	p.Status.Phase = "Running"
	return p
}

func TestWaitsForAPlaceToRun(t *testing.T) {
	defer func(n int) { *maxPods = n }(*maxPods)
	*maxPods = 2
	b, repo := branch()
	others := []*Pod{runningPod("default", "gotest-other1"), runningPod("other", "gotest-other2")}
	rec := reconcileWith(t, b, repo, others...)
	if pods := kube.Owned[Pod](rec); len(pods) != 0 {
		t.Fatalf("owned Pods = %+v, want none while 2 test Pods run", pods)
	}
	res := b.Status.Checks.Result
	if res.State != gitk8s.Running || !strings.Contains(res.Message, "-max-pods is 2") || rec.RequeueAfter() == 0 {
		t.Fatalf("result = %+v, RequeueAfter = %v; want Running, waiting, and a requeue", res, rec.RequeueAfter())
	}

	t.Log("A finished Pod doesn't take a place.")
	others[1].Status.Phase = "Succeeded"
	rec = reconcileWith(t, b, repo, others...)
	if pods := kube.Owned[Pod](rec); len(pods) != 1 {
		t.Fatalf("owned Pods = %+v, want the branch's Pod once a place is free", pods)
	}

	t.Log("A branch keeps the Pod that it already runs when the limit is reached.")
	others[1].Status.Phase = "Running"
	mine := pod("Running", nil, nil)
	rec = reconcileWith(t, b, repo, append(others, mine)...)
	if pods := kube.Owned[Pod](rec); len(pods) != 1 || pods[0].Name != mine.Name {
		t.Fatalf("owned Pods = %+v, want the branch's running Pod", pods)
	}
}

func TestRetriesFailedFetch(t *testing.T) {
	b, repo := branch()
	reconcileWith(t, b, repo, pod("Failed", &Terminated{ExitCode: 128, Message: "fatal: unable to access"}, nil))
	res := b.Status.Checks.Result
	if res.State != gitk8s.Running || res.Outputs["attempt"] != "2" {
		t.Fatalf("result = %+v, want Running on attempt 2", res)
	}
	// The next attempt declares a new Pod, so kube deletes the failed one.
	rec := reconcileWith(t, b, repo)
	if pods := kube.Owned[Pod](rec); len(pods) != 1 || pods[0].Name != podName("app-c-x", head, 2) {
		t.Errorf("owned Pods = %+v, want the attempt 2 Pod", pods)
	}

	b.Status.Checks.Result.Outputs["attempt"] = "3"
	last := pod("Failed", &Terminated{ExitCode: 128, Message: "fatal: unable to access"}, nil)
	last.Name = podName("app-c-x", head, 3)
	reconcileWith(t, b, repo, last)
	if res := b.Status.Checks.Result; res.State != gitk8s.Failed || !strings.Contains(res.Message, "in 3 attempts") {
		t.Errorf("result = %+v, want Failed after 3 attempts", res)
	}
}

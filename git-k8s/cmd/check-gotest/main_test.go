package main

import (
	"cmp"
	"encoding/json"
	"errors"
	"flag"
	"fmt"
	"maps"
	"net/http"
	"net/http/httptest"
	"net/http/httputil"
	"net/url"
	"os"
	"os/exec"
	"path/filepath"
	"slices"
	"strconv"
	"strings"
	"sync"
	"testing"
	"testing/synctest"
	"time"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/checks"
	"github.com/imjasonh/playground/git-k8s/internal/git"
	"github.com/imjasonh/playground/git-k8s/internal/gittest"
	"github.com/imjasonh/playground/git-k8s/internal/images"
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
		URL: "https://git.example.com/app.git", SecretRef: &gitk8s.SecretRef{Name: "app-creds"},
	}}
	repo.Namespace = "default"
	return b, repo
}

// named records that the check named the Pod of attempt at b's head, which
// it does before it starts the Pod.
func named(b *Branch, attempt int) {
	b.Status.Checks.Result = &gitk8s.CheckResult{Commit: b.Spec.Head, State: gitk8s.Running, Pod: podName(b.Name, b.Spec.Head, attempt), Notes: map[string]string{
		"attempt": strconv.Itoa(attempt),
	}}
}

// reconcileWith runs a new check with world holding the Pods that exist.
func reconcileWith(t *testing.T, b *Branch, repo *gitk8s.GitRepository, pods ...*Pod) *kube.Recorder {
	t.Helper()
	world := []any{repo}
	for _, p := range pods {
		world = append(world, p)
	}
	return reconcileIn(t, checks.NewReconciler[Branch](new(gotest).check(), &checks.Config{CoreURL: gitk8s.CoreURL}), b, world...)
}

// reconcileIn runs r on b with world holding the objects that exist.
func reconcileIn(t *testing.T, r kube.Reconciler[Branch], b *Branch, world ...any) *kube.Recorder {
	t.Helper()
	ctx, rec := kube.Fake(t.Context(), b, world...)
	if err := r.Reconcile(ctx, b); err != nil {
		t.Fatal(err)
	}
	return rec
}

// started returns the Pod that the check declares once its result names
// the Pod.
func started(t *testing.T, b *Branch, repo *gitk8s.GitRepository) *Pod {
	t.Helper()
	return startedAt(t, gitk8s.CoreURL, b, repo)
}

// startedAt is started with the core program at coreURL.
func startedAt(t *testing.T, coreURL string, b *Branch, repo *gitk8s.GitRepository) *Pod {
	t.Helper()
	named(b, 1)
	rec := reconcileIn(t, checks.NewReconciler[Branch](new(gotest).check(), &checks.Config{CoreURL: coreURL}), b, repo)
	pods := kube.Owned[Pod](rec)
	if len(pods) != 1 {
		t.Fatalf("owned Pods = %+v, want one", pods)
	}
	return pods[0]
}

func TestStartsSandboxedPod(t *testing.T) {
	b, repo := branch()
	rec := reconcileWith(t, b, repo)
	res := b.Status.Checks.Result
	name := podName("app-c-x", head, 1)
	if res.State != gitk8s.Running || res.Notes["attempt"] != "1" || res.Pod != name {
		t.Fatalf("result = %+v, want Running on attempt 1, naming Pod %s", res, name)
	}
	if pods := kube.Owned[Pod](rec); len(pods) != 0 || rec.RequeueAfter() == 0 {
		t.Fatalf("owned Pods = %+v, RequeueAfter = %v; the check names the Pod before it starts it", pods, rec.RequeueAfter())
	}

	t.Log("Once the result names the Pod, the check starts it.")
	rec = reconcileWith(t, b, repo)
	pods := kube.Owned[Pod](rec)
	if len(pods) != 1 || pods[0].Name != name || b.Status.Checks.Result.Pod != name {
		t.Fatalf("owned Pods = %+v, result = %+v", pods, b.Status.Checks.Result)
	}
	spec := pods[0].Spec
	if *spec.AutomountServiceAccountToken || !*spec.SecurityContext.RunAsNonRoot || spec.RestartPolicy != "Never" {
		t.Errorf("Pod spec isn't locked down: %+v", spec)
	}
	if g := spec.TerminationGracePeriodSeconds; g == nil || *g != 2 {
		t.Error("the Pod's termination grace period isn't 2 seconds, the shortest the kubelet waits for fetch's shell, which ignores SIGTERM")
	}
	for _, c := range append(spec.InitContainers, spec.Containers...) {
		sc := c.SecurityContext
		if *sc.AllowPrivilegeEscalation || !*sc.ReadOnlyRootFilesystem || !slices.Equal(sc.Capabilities.Drop, []string{"ALL"}) {
			t.Errorf("container %s isn't locked down: %+v", c.Name, sc)
		}
	}

	fetcher, tester := spec.InitContainers[0], spec.Containers[0]
	env := map[string]string{}
	for _, e := range fetcher.Env {
		env[e.Name] = e.Value
	}
	if env["URL"] != "http://git-k8s.git-k8s.svc/default/app.git" || env["GIT_ALLOW_PROTOCOL"] != git.AllowProtocol {
		t.Errorf("fetch container's environment = %v, want the copy on the mirror", env)
	}
	var token *ServiceAccountTokenProjection
	for _, v := range spec.Volumes {
		if v.Name == "mirror-token" && v.Projected != nil && len(v.Projected.Sources) == 1 {
			token = v.Projected.Sources[0].ServiceAccountToken
		}
	}
	if token == nil || token.Audience != gitk8s.MirrorAudience {
		t.Fatalf("volumes = %+v, want a token for the mirror", spec.Volumes)
	}
	mountsToken := func(c Container) bool {
		return slices.ContainsFunc(c.VolumeMounts, func(m VolumeMount) bool { return m.Name == "mirror-token" })
	}
	if !slices.Contains(fetcher.VolumeMounts, VolumeMount{Name: "mirror-token", MountPath: filepath.Dir(env["TOKEN_FILE"]), ReadOnly: true}) ||
		filepath.Base(env["TOKEN_FILE"]) != token.Path {
		t.Errorf("fetch container's mounts = %+v, TOKEN_FILE = %s; want the token there, read-only", fetcher.VolumeMounts, env["TOKEN_FILE"])
	}
	if mountsToken(tester) {
		t.Error("the test container can read the token")
	}
}

func TestImagesByDigest(t *testing.T) {
	defer func(goImg, gitImg string) { *goImage, *gitImage = goImg, gitImg }(*goImage, *gitImage)
	for name, want := range map[string]string{"go-image": images.Go, "git-image": images.Git} {
		if got := flag.Lookup(name).DefValue; got != want {
			t.Errorf("-%s defaults to %s, want %s, which names its image by digest", name, got, want)
		}
	}
	t.Log("kube resolves the tag in an image flag before the program starts.")
	for _, name := range []string{"go-image", "git-image"} {
		if err := flag.Lookup(name).Value.Set("registry.example.com/Go"); err == nil {
			t.Errorf("-%s takes registry.example.com/Go, which isn't an image reference, so it isn't an image flag", name)
		}
	}
	t.Log("kube resolves the tags in the Pods that it applies too, so nodes run every image by digest, and pull each once.")
	policies := func() map[string]string {
		t.Helper()
		b, repo := branch()
		spec := started(t, b, repo).Spec
		got := map[string]string{}
		for _, c := range slices.Concat(spec.InitContainers, spec.Containers) {
			got[c.Name] = c.ImagePullPolicy
		}
		return got
	}
	*goImage, *gitImage = "registry.example.com/go:test", "registry.example.com/git:test"
	if got, want := policies(), map[string]string{"fetch": "IfNotPresent", "test": "IfNotPresent"}; !maps.Equal(got, want) {
		t.Errorf("the pull policies are %v, want %v", got, want)
	}
	withGoCache(t)
	if got, want := policies(), map[string]string{"fetch": "IfNotPresent", "build": "IfNotPresent", "upload": "IfNotPresent", "test": "IfNotPresent"}; !maps.Equal(got, want) {
		t.Errorf("with -go-cache, the pull policies are %v, want %v", got, want)
	}
}

func TestPodNeverSeesSigningKey(t *testing.T) {
	b, repo := branch()
	repo.Spec.SigningKeyRef = &gitk8s.SecretRef{Name: "app-signing"}
	spec, err := json.Marshal(started(t, b, repo).Spec)
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
	named(b, 1)
	rec := reconcileWith(t, b, repo, pod("Succeeded", &Terminated{}, &Terminated{}))
	if res := b.Status.Checks.Result; res.State != gitk8s.Passed {
		t.Errorf("result = %+v, want Passed", res)
	}
	if rec.RequeueAfter() != time.Second {
		t.Errorf("RequeueAfter = %v; the next reconcile deletes the Pod", rec.RequeueAfter())
	}

	b, repo = branch()
	named(b, 1)
	reconcileWith(t, b, repo, pod("Failed", &Terminated{}, &Terminated{ExitCode: 1, Message: "--- FAIL: TestAdd\nFAIL\texample.com/app\t0.01s"}))
	if res := b.Status.Checks.Result; res.State != gitk8s.Failed || !strings.Contains(res.Message, "--- FAIL: TestAdd") {
		t.Errorf("result = %+v, want Failed with the test output", res)
	}

	b, repo = branch()
	named(b, 1)
	offline := "add_test.go:3:8: example.com/dep@v1.0.0: module lookup disabled by GOPROXY=off"
	reconcileWith(t, b, repo, pod("Failed", &Terminated{}, &Terminated{ExitCode: 1, Message: offline}))
	if res := b.Status.Checks.Result; res.State != gitk8s.Failed || !strings.Contains(res.Message, "vendor the dependencies, or set -goproxy") {
		t.Errorf("result = %+v, want Failed with advice about -goproxy", res)
	}
}

func TestOutcome(t *testing.T) {
	failedBuild := pod("Pending", &Terminated{}, nil)
	build := ContainerStatus{Name: "build"}
	build.State.Terminated = &Terminated{ExitCode: 1}
	failedBuild.Status.InitContainerStatuses = append(failedBuild.Status.InitContainerStatuses, build)
	runs := pod("Running", &Terminated{}, nil)
	runs.Status.ContainerStatuses = []ContainerStatus{{Name: "test"}}
	for _, c := range []struct {
		name string
		pod  *Pod
		want string
	}{
		{"a Pending Pod", pod("Pending", nil, nil), ""},
		{"a fetch that finished", pod("Pending", &Terminated{}, nil), ""},
		{"a fetch that failed", pod("Pending", &Terminated{ExitCode: 128}, nil), "Failed"},
		{"another init container that failed", failedBuild, "Failed"},
		{"a test container that runs", runs, ""},
		{"a test container that passed", pod("Running", &Terminated{}, &Terminated{}), "Succeeded"},
		{"a test container that failed", pod("Running", &Terminated{}, &Terminated{ExitCode: 1}), "Failed"},
		{"a Succeeded Pod", pod("Succeeded", &Terminated{}, &Terminated{}), "Succeeded"},
		{"a Pod that failed before its containers ran", pod("Failed", nil, nil), "Failed"},
	} {
		if got := outcome(c.pod); got != c.want {
			t.Errorf("%s: outcome = %q, want %q", c.name, got, c.want)
		}
	}
}

// TestReportsResultBeforeThePodStops gives the check Pods whose containers
// finished while their phase is still Pending or Running, as it is for
// about a second before the kubelet stops them.
func TestReportsResultBeforeThePodStops(t *testing.T) {
	b, repo := branch()
	named(b, 1)
	passed := pod("Running", &Terminated{}, &Terminated{})
	rec := reconcileWith(t, b, repo, passed)
	if res := b.Status.Checks.Result; res.State != gitk8s.Passed {
		t.Errorf("result = %+v, want Passed", res)
	}
	if rec.RequeueAfter() != time.Second {
		t.Errorf("RequeueAfter = %v; the next reconcile deletes the Pod", rec.RequeueAfter())
	}

	b, repo = branch()
	named(b, 1)
	reconcileWith(t, b, repo, pod("Running", &Terminated{}, &Terminated{ExitCode: 1, Message: "--- FAIL: TestAdd\nFAIL\texample.com/app\t0.01s"}))
	if res := b.Status.Checks.Result; res.State != gitk8s.Failed || !strings.Contains(res.Message, "--- FAIL: TestAdd") {
		t.Errorf("result = %+v, want Failed with the test output", res)
	}

	b, repo = branch()
	named(b, 1)
	reconcileWith(t, b, repo, pod("Pending", &Terminated{ExitCode: 128, Message: "fatal: unable to access", FinishedAt: time.Now()}, nil))
	if res := b.Status.Checks.Result; res.State != gitk8s.Running || !strings.Contains(res.Message, "trying again at") {
		t.Errorf("result = %+v, want Running, waiting to fetch again", res)
	}
}

// TestKeepsAPodUntilItStops checks that the check declares a Pod after it
// records the Pod's result, until the kubelet stops the Pod, so that the
// API server deletes the Pod at once.
func TestKeepsAPodUntilItStops(t *testing.T) {
	for _, c := range []struct {
		code  int32
		phase string
	}{{0, "Succeeded"}, {1, "Failed"}} {
		b, repo := branch()
		named(b, 1)
		p := pod("Running", &Terminated{}, &Terminated{ExitCode: c.code, Message: "FAIL"})
		reconcileWith(t, b, repo, p)
		final := b.Status.Checks.Result
		if !final.Final() {
			t.Fatalf("result = %+v after the test container exited %d, want a final result", final, c.code)
		}
		if pods := kube.Owned[Pod](reconcileWith(t, b, repo, p)); len(pods) != 1 || pods[0].Name != p.Name || !b.Status.Checks.Result.Equal(final) {
			t.Errorf("owned Pods = %d and result = %+v, want Pod %s while it stops, and the same result", len(pods), b.Status.Checks.Result, p.Name)
		}
		p.Status.Phase = c.phase
		if pods := kube.Owned[Pod](reconcileWith(t, b, repo, p)); len(pods) != 0 {
			t.Errorf("owned Pods = %+v, want none once the Pod is %s", pods, c.phase)
		}
		if pods := kube.Owned[Pod](reconcileWith(t, b, repo)); len(pods) != 0 {
			t.Errorf("owned Pods = %+v, want none once the Pod is gone", pods)
		}

		p.Status.Phase = "Running"
		b.Spec.Head = strings.Repeat("1", 40)
		if pods := kube.Owned[Pod](reconcileWith(t, b, repo, p)); slices.ContainsFunc(pods, func(o *Pod) bool { return o.Name == p.Name }) {
			t.Errorf("owned Pods = %+v after the branch moved, want none for the old head", pods)
		}
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
	since := res.Notes["waiting"]
	if _, err := time.Parse(time.RFC3339, since); err != nil {
		t.Fatalf("notes.waiting = %q, want when the branch started waiting", since)
	}
	reconcileWith(t, b, repo, others...)
	if got := b.Status.Checks.Result.Notes["waiting"]; got != since {
		t.Errorf("notes.waiting = %q after another reconcile, want %q", got, since)
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

func TestCountsAPodUntilItStops(t *testing.T) {
	defer func(n int) { *maxPods = n }(*maxPods)
	*maxPods = 1
	b, repo := branch()
	named(b, 1)
	other := runningPod("default", podName("app-c-y", head, 1))
	test := ContainerStatus{Name: "test"}
	test.State.Terminated = &Terminated{}
	other.Status.ContainerStatuses = []ContainerStatus{test}
	if pods := kube.Owned[Pod](reconcileWith(t, b, repo, other)); len(pods) != 0 {
		t.Fatalf("owned Pods = %+v, want none while the kubelet stops a Pod whose tests passed", pods)
	}
	other.Status.Phase = "Succeeded"
	if pods := kube.Owned[Pod](reconcileWith(t, b, repo, other)); len(pods) != 1 {
		t.Errorf("owned Pods = %+v, want the branch's Pod once the other Pod is Succeeded", pods)
	}
}

func TestCountsOnlyTestPods(t *testing.T) {
	defer func(n int) { *maxPods = n }(*maxPods)
	*maxPods = 1
	b, repo := branch()
	named(b, 1)
	// generate labels the check's own Pods like this.
	self := &Pod{Object: kube.Meta("check-gotest-5d8f7c9b4-x2x7q", map[string]string{"app.kubernetes.io/name": "check-gotest"})}
	self.Namespace = "check-gotest"
	self.Status.Phase = "Running"
	if pods := kube.Owned[Pod](reconcileWith(t, b, repo, self)); len(pods) != 1 {
		t.Errorf("owned Pods = %+v, want a test Pod while only the check's own Pod runs", pods)
	}
}

// waitingBranch returns a branch named name that has waited since the given
// time to start its Pod.
func waitingBranch(name string, since time.Time) *Branch {
	b, _ := branch()
	b.Name = name
	b.Status.Checks.Result = &gitk8s.CheckResult{Commit: head, State: gitk8s.Running, Pod: podName(name, head, 1), Notes: map[string]string{
		"attempt": "1", "waiting": since.UTC().Format(waitingLayout),
	}}
	return b
}

// inQueue returns b's position in its parent's merge queue, where the merge
// controller kept b at its head.
func inQueue(b *Branch, position int32) *queued {
	q := &queued{Object: kube.Meta(b.Name, nil)}
	q.Namespace = b.Namespace
	q.Status.Queued.Head = b.Spec.Head
	q.Status.Queued.Position = position
	return q
}

// startedIn reconciles each branch with r, in a world that holds repo, the
// branches, pods, and extra, and returns the branches that declared a Pod
// that isn't in pods.
func startedIn(t *testing.T, r kube.Reconciler[Branch], repo *gitk8s.GitRepository, branches []*Branch, pods []*Pod, extra ...any) []string {
	t.Helper()
	var started []string
	for _, b := range branches {
		world := []any{repo}
		for _, o := range branches {
			world = append(world, o)
		}
		for _, p := range pods {
			world = append(world, p)
		}
		world = append(world, extra...)
		for _, p := range kube.Owned[Pod](reconcileIn(t, r, b, world...)) {
			if !slices.ContainsFunc(pods, func(o *Pod) bool { return o.Name == p.Name }) {
				started = append(started, b.Name)
			}
		}
	}
	return started
}

func TestStartsTheBranchThatHasWaitedLongest(t *testing.T) {
	defer func(n int) { *maxPods = n }(*maxPods)
	*maxPods = 1
	_, repo := branch()
	start := time.Now().Add(-time.Hour).UTC().Truncate(time.Microsecond)
	// The names sort differently from the order that the branches started
	// waiting, and app-c-x hasn't started waiting yet.
	newcomer, _ := branch()
	branches := []*Branch{
		waitingBranch("app-c-a", start.Add(2*time.Second)),
		waitingBranch("app-c-b", start),
		waitingBranch("app-c-c", start.Add(time.Second)),
		newcomer,
	}
	r := checks.NewReconciler[Branch](new(gotest).check(), &checks.Config{})
	var pods []*Pod
	for i, next := range []string{"app-c-b", "app-c-c", "app-c-a", "app-c-x"} {
		if i == 1 {
			t.Log("A restarted check finds the order in the branches' statuses.")
			r = checks.NewReconciler[Branch](new(gotest).check(), &checks.Config{})
		}
		if got := startedIn(t, r, repo, branches, pods); !slices.Equal(got, []string{next}) {
			t.Fatalf("started %v, want only %s", got, next)
		}
		if i == 0 && newcomer.Status.Checks.Result.Notes["waiting"] == "" {
			t.Fatalf("result = %+v, want app-c-x to record when it started waiting", newcomer.Status.Checks.Result)
		}
		p := runningPod("default", podName(next, head, 1))
		pods = append(pods, p)
		if got := startedIn(t, r, repo, branches, pods); len(got) != 0 {
			t.Fatalf("started %v while the Pod of %s runs", got, next)
		}
		p.Status.Phase = "Succeeded"
	}
}

func TestBreaksTiesByName(t *testing.T) {
	defer func(n int) { *maxPods = n }(*maxPods)
	*maxPods = 1
	_, repo := branch()
	since := time.Now().Add(-time.Hour).UTC().Truncate(time.Microsecond)
	branches := []*Branch{waitingBranch("app-c-b", since), waitingBranch("app-c-a", since)}
	r := checks.NewReconciler[Branch](new(gotest).check(), &checks.Config{})
	if got := startedIn(t, r, repo, branches, nil); !slices.Equal(got, []string{"app-c-a"}) {
		t.Errorf("started %v, want only app-c-a", got)
	}
}

func TestStartsTheFrontsOfQueuesFirst(t *testing.T) {
	defer func(n int) { *maxPods = n }(*maxPods)
	*maxPods = 1
	_, repo := branch()
	start := time.Now().Add(-time.Hour).UTC().Truncate(time.Microsecond)
	a, b := waitingBranch("app-c-a", start), waitingBranch("app-c-b", start.Add(time.Second))
	c, d := waitingBranch("app-c-c", start.Add(2*time.Second)), waitingBranch("app-c-d", start.Add(3*time.Second))
	e := waitingBranch("app-c-e", start.Add(4*time.Second))
	c.Spec.Parent, d.Spec.Parent = "release", "dev"
	// app-c-e is first in main's queue, and app-c-b is second. app-c-c is
	// first in release's queue. app-c-d is first in dev's queue, but the base
	// check has just pushed its merge of dev, and the merge controller hasn't
	// kept app-c-d in the queue at the merge yet.
	pushed := inQueue(d, 1)
	pushed.Status.Queued.Head = strings.Repeat("1", 40)
	positions := []any{inQueue(e, 1), inQueue(b, 2), inQueue(c, 1), pushed}
	branches := []*Branch{a, b, c, d, e}
	r := checks.NewReconciler[Branch](new(gotest).check(), &checks.Config{})
	var pods []*Pod
	for i, next := range []string{"app-c-c", "app-c-e", "app-c-a", "app-c-b", "app-c-d"} {
		if i == 1 {
			t.Log("A restarted check finds the order in the branches' statuses.")
			r = checks.NewReconciler[Branch](new(gotest).check(), &checks.Config{})
		}
		if got := startedIn(t, r, repo, branches, pods, positions...); !slices.Equal(got, []string{next}) {
			t.Fatalf("started %v, want only %s", got, next)
		}
		p := runningPod("default", podName(next, head, 1))
		pods = append(pods, p)
		if got := startedIn(t, r, repo, branches, pods, positions...); len(got) != 0 {
			t.Fatalf("started %v while the Pod of %s runs", got, next)
		}
		p.Status.Phase = "Succeeded"
	}
}

func TestStartsAFrontOnceTheQueueHasItsHead(t *testing.T) {
	defer func(n int) { *maxPods = n }(*maxPods)
	*maxPods = 1
	_, repo := branch()
	start := time.Now().Add(-time.Hour).UTC().Truncate(time.Microsecond)
	longest := waitingBranch("app-c-a", start)
	merged := waitingBranch("app-c-b", start.Add(time.Second))
	position := inQueue(merged, 1)
	position.Status.Queued.Head = strings.Repeat("1", 40)
	r := checks.NewReconciler[Branch](new(gotest).check(), &checks.Config{})
	if pods := kube.Owned[Pod](reconcileIn(t, r, merged, repo, longest, position)); len(pods) != 0 {
		t.Fatalf("owned Pods = %+v, want app-c-b to wait behind app-c-a while the queue has app-c-b's earlier head", pods)
	}

	t.Log("The merge controller keeps app-c-b at the front at its new head.")
	position.Status.Queued.Head = merged.Spec.Head
	if pods := kube.Owned[Pod](reconcileIn(t, r, merged, repo, longest, position)); len(pods) != 1 {
		t.Fatalf("owned Pods = %+v, want app-c-b's Pod", pods)
	}
	if pods := kube.Owned[Pod](reconcileIn(t, r, longest, repo, merged, position)); len(pods) != 0 {
		t.Errorf("owned Pods = %+v, want app-c-a to wait while app-c-b's Pod may be on its way", pods)
	}
}

func TestKeepsTheLimitWhileFrontsWait(t *testing.T) {
	defer func(n int) { *maxPods = n }(*maxPods)
	*maxPods = 2
	_, repo := branch()
	start := time.Now().Add(-time.Hour).UTC().Truncate(time.Microsecond)
	world := []any{repo}
	var branches []*Branch
	for i := range 8 {
		b := waitingBranch(fmt.Sprintf("app-c-%d", i), start.Add(time.Duration(i)*time.Second))
		branches = append(branches, b)
		world = append(world, b)
		if i >= 5 {
			b.Spec.Parent = fmt.Sprintf("parent-%d", i)
			world = append(world, inQueue(b, 1))
		}
	}
	// Every branch reconciles at once, as kube's workers do. The three that
	// have waited least are at the fronts of three queues.
	r := checks.NewReconciler[Branch](new(gotest).check(), &checks.Config{})
	copies := make([]Branch, len(branches))
	owned := make([][]*Pod, len(branches))
	var wg sync.WaitGroup
	for i, b := range branches {
		copies[i] = *b
		wg.Go(func() {
			ctx, rec := kube.Fake(t.Context(), &copies[i], world...)
			if err := r.Reconcile(ctx, &copies[i]); err != nil {
				t.Error(err)
			}
			owned[i] = kube.Owned[Pod](rec)
		})
	}
	wg.Wait()
	var started []string
	for i, b := range branches {
		if len(owned[i]) > 0 {
			started = append(started, b.Name)
		}
	}
	if want := []string{"app-c-5", "app-c-6"}; !slices.Equal(started, want) {
		t.Errorf("started %v, want %v, the two fronts that have waited longest", started, want)
	}
}

func TestKeepsTheLimitInABurst(t *testing.T) {
	defer func(n int) { *maxPods = n }(*maxPods)
	*maxPods = 3
	_, repo := branch()
	var branches []*Branch
	for i := range 10 {
		b, _ := branch()
		b.Name = fmt.Sprintf("app-c-%d", i)
		branches = append(branches, b)
	}
	r := checks.NewReconciler[Branch](new(gotest).check(), &checks.Config{})
	// burst reconciles every branch at once, as kube's workers do, in a
	// world that holds pods. It returns the Pod that each branch declared.
	burst := func(pods ...*Pod) map[string]string {
		t.Helper()
		world := []any{repo}
		for _, b := range branches {
			world = append(world, b)
		}
		for _, p := range pods {
			world = append(world, p)
		}
		copies := make([]Branch, len(branches))
		owned := make([][]*Pod, len(branches))
		var wg sync.WaitGroup
		for i, b := range branches {
			copies[i] = *b
			wg.Go(func() {
				ctx, rec := kube.Fake(t.Context(), &copies[i], world...)
				if err := r.Reconcile(ctx, &copies[i]); err != nil {
					t.Error(err)
				}
				owned[i] = kube.Owned[Pod](rec)
			})
		}
		wg.Wait()
		declared := map[string]string{}
		for i, b := range branches {
			b.Status = copies[i].Status
			if len(owned[i]) == 1 {
				declared[b.Name] = owned[i][0].Name
			}
		}
		return declared
	}

	t.Log("Three branches take places, and name their Pods before they start them.")
	if got := burst(); len(got) != 0 {
		t.Fatalf("declared Pods = %v, want none until the results name them", got)
	}
	first := burst()
	if len(first) != 3 {
		t.Fatalf("declared Pods = %v, want 3", first)
	}

	t.Log("The branches that started keep their Pods while the cache doesn't show them, and no other branch starts.")
	if got := burst(); !maps.Equal(got, first) {
		t.Fatalf("declared Pods = %v, want %v", got, first)
	}

	t.Log("The cache shows the Pods, and one has finished, so the branch that has waited longest starts.")
	var pods []*Pod
	for _, name := range slices.Sorted(maps.Values(first)) {
		pods = append(pods, runningPod("default", name))
	}
	pods[0].Status.Phase = "Succeeded"
	var waiters []*Branch
	for _, b := range branches {
		if _, ok := first[b.Name]; !ok {
			waiters = append(waiters, b)
		}
	}
	longest := slices.MinFunc(waiters, func(a, b *Branch) int {
		wa, wb := a.Status.Checks.Result.Notes["waiting"], b.Status.Checks.Result.Notes["waiting"]
		return cmp.Or(strings.Compare(wa, wb), strings.Compare(a.Name, b.Name))
	})
	got := burst(pods...)
	for name, pod := range first {
		if got[name] != pod {
			t.Errorf("%s declared %q, want its Pod %s", name, got[name], pod)
		}
		delete(got, name)
	}
	if want := map[string]string{longest.Name: podName(longest.Name, head, 1)}; !maps.Equal(got, want) {
		t.Errorf("newly declared Pods = %v, want %v", got, want)
	}
}

func TestStopsCountingAPodThatNeverAppears(t *testing.T) {
	synctest.Test(t, func(t *testing.T) {
		defer func(n int) { *maxPods = n }(*maxPods)
		*maxPods = 1
		_, repo := branch()
		first, second := waitingBranch("app-c-a", time.Now()), waitingBranch("app-c-b", time.Now().Add(time.Second))
		r := checks.NewReconciler[Branch](new(gotest).check(), &checks.Config{})
		if pods := kube.Owned[Pod](reconcileIn(t, r, first, repo, first, second)); len(pods) != 1 {
			t.Fatalf("owned Pods = %+v, want app-c-a's Pod", pods)
		}
		rec := reconcileIn(t, r, second, repo, first, second)
		if pods := kube.Owned[Pod](rec); len(pods) != 0 {
			t.Fatalf("owned Pods = %+v, want none while app-c-a's Pod may be on its way", pods)
		}
		if rec.RequeueAfter() == 0 || rec.RequeueAfter() > declaredFor {
			t.Errorf("RequeueAfter = %v, want at most %v, to start once app-c-a's Pod stops counting", rec.RequeueAfter(), declaredFor)
		}

		t.Log("The API server never creates app-c-a's Pod.")
		time.Sleep(declaredFor)
		// app-c-a goes first, while the check still holds its expired entry.
		if pods := kube.Owned[Pod](reconcileIn(t, r, first, repo, first, second)); len(pods) != 1 {
			t.Errorf("owned Pods = %+v, want app-c-a, which has waited longest, to take the free place again", pods)
		}
		if pods := kube.Owned[Pod](reconcileIn(t, r, second, repo, first, second)); len(pods) != 0 {
			t.Errorf("owned Pods = %+v, want none while app-c-a's Pod may be on its way again", pods)
		}
	})
}

func TestKeepsItsPlaceWhenThePodIsRefused(t *testing.T) {
	synctest.Test(t, func(t *testing.T) {
		defer func(n int) { *maxPods = n }(*maxPods)
		*maxPods = 1
		_, repo := branch()
		start := time.Now()
		first := waitingBranch("app-c-a", start)
		second := waitingBranch("app-c-b", start.Add(time.Second))
		third := waitingBranch("app-c-c", start.Add(2*time.Second))
		since := first.Status.Checks.Result.Notes["waiting"]
		world := func(objs ...any) []any { return append([]any{repo, first, second, third}, objs...) }
		r := checks.NewReconciler[Branch](new(gotest).check(), &checks.Config{})
		if pods := kube.Owned[Pod](reconcileIn(t, r, first, world()...)); len(pods) != 1 {
			t.Fatalf("owned Pods = %+v, want app-c-a's Pod", pods)
		}

		t.Log("The check Pod policy denies app-c-a's Pod, and kube tries again with backoff.")
		denied := errors.New(`pods "` + podName("app-c-a", head, 1) + `" is forbidden: ` +
			`ValidatingAdmissionPolicy 'git-k8s-check-pods' with binding 'git-k8s-check-pods' denied request (422 Invalid)`)
		if pods := kube.Owned[Pod](reconcileIn(t, r, first, world(denied)...)); len(pods) != 1 {
			t.Fatalf("owned Pods = %+v, want app-c-a to declare its Pod again", pods)
		}
		if pods := kube.Owned[Pod](reconcileIn(t, r, second, world()...)); len(pods) != 0 {
			t.Fatalf("owned Pods = %+v, want app-c-b to wait while app-c-a's Pod may be on its way", pods)
		}

		t.Log("After a minute, app-c-a's Pod stops counting, so app-c-b doesn't wait out the backoff.")
		time.Sleep(declaredFor)
		if pods := kube.Owned[Pod](reconcileIn(t, r, second, world()...)); len(pods) != 1 {
			t.Fatalf("owned Pods = %+v, want app-c-b's Pod", pods)
		}
		running := runningPod("default", podName("app-c-b", head, 1))
		if pods := kube.Owned[Pod](reconcileIn(t, r, first, world(running, denied)...)); len(pods) != 0 {
			t.Fatalf("owned Pods = %+v, want app-c-a to wait while app-c-b's Pod runs", pods)
		}
		if got := first.Status.Checks.Result.Notes["waiting"]; got != since {
			t.Errorf("notes.waiting = %q, want %q, when app-c-a first started waiting", got, since)
		}

		t.Log("Someone labels the namespace, and app-c-b's Pod finishes.")
		running.Status.Phase = "Succeeded"
		if got := startedIn(t, r, repo, []*Branch{third, first, second}, []*Pod{running}); !slices.Equal(got, []string{"app-c-a"}) {
			t.Errorf("started %v, want only app-c-a, which started waiting before app-c-c", got)
		}
		reconcileIn(t, r, first, world(running, runningPod("default", podName("app-c-a", head, 1)))...)
		if notes := first.Status.Checks.Result.Notes; notes["waiting"] != "" || notes["queued"] != "" {
			t.Errorf("notes = %v, want no wait recorded once app-c-a's Pod exists", notes)
		}
	})
}

func TestStopsCountingAPodThatTheCacheShowed(t *testing.T) {
	defer func(n int) { *maxPods = n }(*maxPods)
	*maxPods = 1
	b, repo := branch()
	next, _ := branch()
	next.Name = "app-c-y"
	named(b, 1)
	named(next, 1)
	for _, sees := range []*Branch{b, next} {
		r := checks.NewReconciler[Branch](new(gotest).check(), &checks.Config{})
		if pods := kube.Owned[Pod](reconcileIn(t, r, b, repo)); len(pods) != 1 {
			t.Fatalf("owned Pods = %+v, want app-c-x's Pod", pods)
		}
		reconcileIn(t, r, sees, repo, b, next, runningPod("default", podName(b.Name, head, 1)))

		t.Logf("%s saw the Pod. The Pod finishes, and kube deletes it.", sees.Name)
		if pods := kube.Owned[Pod](reconcileIn(t, r, next, repo, b)); len(pods) != 1 {
			t.Errorf("owned Pods = %+v, want app-c-y's Pod", pods)
		}
	}
}

func TestCountsAStartedBranchOnce(t *testing.T) {
	defer func(n int) { *maxPods = n }(*maxPods)
	*maxPods = 2
	_, repo := branch()
	early := time.Now().Add(-time.Hour)
	// stale is app-c-a as the cache shows it until the cache catches up with
	// the status that says app-c-a started.
	stale := waitingBranch("app-c-a", early)
	for _, c := range []struct {
		when string
		pods []any
	}{
		{"before the cache shows app-c-a's Pod", nil},
		{"once the cache shows app-c-a's Pod", []any{runningPod("default", podName("app-c-a", head, 1))}},
	} {
		r := checks.NewReconciler[Branch](new(gotest).check(), &checks.Config{})
		reconcileIn(t, r, waitingBranch("app-c-a", early), repo)
		next := waitingBranch("app-c-b", early.Add(time.Second))
		if pods := kube.Owned[Pod](reconcileIn(t, r, next, append([]any{repo, stale}, c.pods...)...)); len(pods) != 1 {
			t.Errorf("%s, owned Pods = %+v, want app-c-b's Pod", c.when, pods)
		}
	}
}

func TestIgnoresBranchesThatNoLongerWait(t *testing.T) {
	defer func(n int) { *maxPods = n }(*maxPods)
	*maxPods = 1
	_, repo := branch()
	early := time.Now().Add(-time.Hour)
	b, _ := branch()
	named(b, 1)
	rec := reconcileIn(t, checks.NewReconciler[Branch](new(gotest).check(), &checks.Config{}), b, repo, waitingBranch("app-c-a", early))
	if pods := kube.Owned[Pod](rec); len(pods) != 0 {
		t.Fatalf("owned Pods = %+v, want app-c-x to wait behind app-c-a", pods)
	}
	for _, c := range []struct {
		why    string
		change func(*Branch)
	}{
		{"moved to a new head, which waits from the start", func(b *Branch) { b.Spec.Head = strings.Repeat("1", 40) }},
		{"has no parent head", func(b *Branch) { b.Spec.ParentHead = "" }},
		{"no longer runs the check", func(b *Branch) { b.Spec.Merge = nil }},
		{"is being deleted", func(b *Branch) { b.DeletionTimestamp = &early }},
		{"belongs to a GitRepository that's gone", func(b *Branch) { b.Spec.Repository = "gone" }},
	} {
		stale := waitingBranch("app-c-a", early)
		c.change(stale)
		b, _ := branch()
		named(b, 1)
		rec := reconcileIn(t, checks.NewReconciler[Branch](new(gotest).check(), &checks.Config{}), b, repo, stale)
		if pods := kube.Owned[Pod](rec); len(pods) != 1 {
			t.Errorf("owned Pods = %+v; a branch that %s kept app-c-x waiting", pods, c.why)
		}
	}
}

func TestKeepsItsPlaceWhileItNamesThePod(t *testing.T) {
	defer func(n int) { *maxPods = n }(*maxPods)
	*maxPods = 1
	b, repo := branch()
	reconcileWith(t, b, repo)
	since := b.Status.Checks.Result.Notes["queued"]
	if _, err := time.Parse(time.RFC3339, since); err != nil {
		t.Fatalf("notes.queued = %q, want when the branch took a place", since)
	}

	t.Log("The check restarts, and another branch's Pod takes the place first.")
	reconcileWith(t, b, repo, runningPod("default", podName("app-c-y", head, 1)))
	if got := b.Status.Checks.Result.Notes["waiting"]; got != since {
		t.Errorf("notes.waiting = %q, want %q, when the branch took its place", got, since)
	}
}

func TestRetriesFailedFetch(t *testing.T) {
	b, repo := branch()
	named(b, 1)
	failed := pod("Failed", &Terminated{ExitCode: 128, Message: "fatal: unable to access", FinishedAt: time.Now()}, nil)
	rec := reconcileWith(t, b, repo, failed)
	res := b.Status.Checks.Result
	if res.State != gitk8s.Running || res.Notes["attempt"] != "1" || !strings.Contains(res.Message, "trying again at") {
		t.Fatalf("result = %+v, want Running on attempt 1, waiting to try again", res)
	}
	if d := rec.RequeueAfter(); d <= time.Second || d > fetchRetryDelay {
		t.Errorf("RequeueAfter = %v, want the rest of %v", d, fetchRetryDelay)
	}
	if pods := kube.Owned[Pod](rec); len(pods) != 1 || pods[0].Name != failed.Name {
		t.Errorf("owned Pods = %+v; the check keeps the failed Pod while it waits", pods)
	}

	t.Log("After the wait, the check names the next attempt's Pod, and then starts it.")
	failed.Status.InitContainerStatuses[0].State.Terminated.FinishedAt = time.Now().Add(-fetchRetryDelay)
	reconcileWith(t, b, repo, failed)
	res = b.Status.Checks.Result
	if second := podName("app-c-x", head, 2); res.State != gitk8s.Running || res.Notes["attempt"] != "2" || res.Pod != second {
		t.Fatalf("result = %+v, want Running on attempt 2 with Pod %s", res, second)
	}
	// The next attempt declares a new Pod, so kube deletes the failed one.
	rec = reconcileWith(t, b, repo, failed)
	if pods := kube.Owned[Pod](rec); len(pods) != 1 || pods[0].Name != podName("app-c-x", head, 2) {
		t.Errorf("owned Pods = %+v, want the attempt 2 Pod", pods)
	}

	t.Log("The wait doubles after each failure.")
	second := pod("Failed", &Terminated{ExitCode: 128, Message: "fatal: unable to access", FinishedAt: time.Now().Add(-fetchRetryDelay)}, nil)
	second.Name = podName("app-c-x", head, 2)
	rec = reconcileWith(t, b, repo, second)
	if res := b.Status.Checks.Result; res.Notes["attempt"] != "2" || rec.RequeueAfter() <= time.Second || rec.RequeueAfter() > fetchRetryDelay {
		t.Errorf("result = %+v, RequeueAfter = %v; want attempt 2 to wait %v in all", res, rec.RequeueAfter(), 2*fetchRetryDelay)
	}

	named(b, 3)
	last := pod("Pending", &Terminated{ExitCode: 128, Message: "fatal: unable to access", FinishedAt: time.Now()}, nil)
	last.Name = podName("app-c-x", head, 3)
	reconcileWith(t, b, repo, last)
	if res := b.Status.Checks.Result; res.State != gitk8s.Failed || !strings.Contains(res.Message, "in 3 attempts") || res.Pod != last.Name {
		t.Errorf("result = %+v, want Failed after 3 attempts, naming Pod %s", res, last.Name)
	}
	if pods := kube.Owned[Pod](reconcileWith(t, b, repo, last)); len(pods) != 1 || pods[0].Name != last.Name {
		t.Errorf("owned Pods = %+v, want the last attempt's Pod until the kubelet stops it", pods)
	}
}

// eachFetch runs f with the fetch container that runs fetchScript, and
// again with -go-cache, where the fetch container runs fetchSource.
func eachFetch(t *testing.T, f func(t *testing.T)) {
	t.Run("fetchScript", f)
	t.Run("fetchSource", func(t *testing.T) {
		withGoCache(t)
		f(t)
	})
}

// TestFetch runs the fetch container on this machine against a server
// that, like the mirror, serves the copy at /NAMESPACE/NAME.git and requires
// the Pod's token.
func TestFetch(t *testing.T) {
	eachFetch(t, func(t *testing.T) {
		srv := gittest.NewServer(t, "")
		w := srv.NewWork(t, "app")
		w.Write("go.mod", "module example.com/app\n")
		commit := w.Commit("first")
		w.Push("c/x")

		const token = "token-bound-to-the-pod"
		upstream, err := url.Parse(srv.URL)
		if err != nil {
			t.Fatal(err)
		}
		proxy := httputil.NewSingleHostReverseProxy(upstream)
		mirror := httptest.NewServer(http.HandlerFunc(func(rw http.ResponseWriter, r *http.Request) {
			path, ok := strings.CutPrefix(r.URL.Path, "/default/")
			switch {
			case r.Header.Get("Authorization") != "Bearer "+token:
				http.Error(rw, "send the Pod's token", http.StatusUnauthorized)
			case !ok:
				http.NotFound(rw, r)
			default:
				r.URL.Path = "/" + path
				proxy.ServeHTTP(rw, r)
			}
		}))
		t.Cleanup(mirror.Close)

		b, repo := branch()
		b.Spec.Head = commit
		p := startedAt(t, mirror.URL+"/", b, repo)

		dir, err := fetch(t, p, token)
		if err != nil {
			t.Fatal(err)
		}
		if got := gitIn(t, dir, "rev-parse", "HEAD"); got != commit {
			t.Errorf("checked out %s, want %s", got, commit)
		}
		if _, err := os.Stat(filepath.Join(dir, "repo", "go.mod")); err != nil {
			t.Errorf("the fetch container didn't check out the head: %v", err)
		}
		if config, err := os.ReadFile(filepath.Join(dir, "repo", ".git", "config")); err != nil || strings.Contains(string(config), token) {
			t.Errorf("the repository's config, which the test container reads, holds the token (%v):\n%s", err, config)
		}
		if goCache.url != "" {
			if fi, err := os.Stat(filepath.Join(dir, "go-cache", "check-gotest")); err != nil || fi.Mode().Perm()&0o111 == 0 {
				t.Errorf("fetch didn't install the GOCACHEPROG program in the go-cache volume: %v", err)
			}
		}

		if _, err := fetch(t, p, "another-token"); err == nil {
			t.Error("the fetch succeeded with a token that the mirror refuses")
		}

		w.Write("b.go", "package app\n")
		w.Commit("second")
		w.Push("c/x")
		if _, err := fetch(t, p, token); err == nil || !strings.Contains(err.Error(), "exit status 3") || !strings.Contains(err.Error(), "no longer points to") {
			t.Errorf("fetch after the branch moved = %v, want exit status 3", err)
		}
	})
}

func TestFetchRefusesUnsafeURLs(t *testing.T) {
	if _, err := exec.LookPath("git"); err != nil {
		t.Skip("git isn't installed")
	}
	marker := filepath.Join(t.TempDir(), "ran")
	bin := t.TempDir()
	if err := os.WriteFile(filepath.Join(bin, "git-remote-evil"), []byte("#!/bin/sh\ntouch "+marker+"\n"), 0o755); err != nil {
		t.Fatal(err)
	}
	t.Setenv("PATH", bin+string(os.PathListSeparator)+os.Getenv("PATH"))
	eachFetch(t, func(t *testing.T) {
		for url, want := range map[string]string{
			"--upload-pack=touch " + marker + "; false": "blocked",
			"evil::x": "not allowed",
		} {
			b, repo := branch()
			_, err := fetch(t, startedAt(t, url, b, repo), "token")
			if _, statErr := os.Stat(marker); statErr == nil {
				t.Fatalf("fetching from %q ran a command", url)
			}
			if err == nil || !strings.Contains(err.Error(), want) {
				t.Errorf("fetching from %q: err = %v, want %q", url, err, want)
			}
		}
	})
}

// fetch runs pod's fetch container on this machine with token in its token
// file, and returns the directory that holds the checkout in repo. The
// directory holds the go-cache volume too, and check-gotest's image is the
// test binary.
func fetch(t *testing.T, pod *Pod, token string) (string, error) {
	t.Helper()
	c := pod.Spec.InitContainers[0]
	dir := t.TempDir()
	tokenFile := filepath.Join(dir, "token")
	if err := os.WriteFile(tokenFile, []byte(token), 0o600); err != nil {
		t.Fatal(err)
	}
	if err := os.Mkdir(filepath.Join(dir, "go-cache"), 0o755); err != nil {
		t.Fatal(err)
	}
	local := strings.NewReplacer("/src/repo", filepath.Join(dir, "repo"), goCacheDir, filepath.Join(dir, "go-cache"))
	var cmd *exec.Cmd
	if len(c.Command) > 0 {
		cmd = exec.Command(c.Command[0], c.Command[1], local.Replace(c.Command[2]))
	} else {
		self, err := os.Executable()
		if err != nil {
			t.Fatal(err)
		}
		args := slices.Clone(c.Args)
		for i := range args {
			args[i] = local.Replace(args[i])
		}
		cmd = exec.Command(self, args...)
	}
	cmd.Env = []string{"PATH=" + os.Getenv("PATH"), "GIT_CONFIG_NOSYSTEM=1", "GIT_CONFIG_GLOBAL=" + os.DevNull}
	for _, e := range c.Env {
		switch e.Name {
		case "TOKEN_FILE":
			e.Value = tokenFile
		case "HOME":
			e.Value = dir
		}
		cmd.Env = append(cmd.Env, e.Name+"="+e.Value)
	}
	if out, err := cmd.CombinedOutput(); err != nil {
		return "", fmt.Errorf("%v: %s", err, out)
	}
	return dir, nil
}

// gitIn runs git in the checkout that fetch made in dir.
func gitIn(t *testing.T, dir string, args ...string) string {
	t.Helper()
	out, err := exec.Command("git", append([]string{"-C", filepath.Join(dir, "repo")}, args...)...).Output()
	if err != nil {
		t.Fatalf("git %s: %v", strings.Join(args, " "), err)
	}
	return strings.TrimSpace(string(out))
}

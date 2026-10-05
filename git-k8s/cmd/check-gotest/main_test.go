package main

import (
	"cmp"
	"fmt"
	"maps"
	"os"
	"os/exec"
	"path/filepath"
	"slices"
	"strings"
	"sync"
	"testing"
	"testing/synctest"
	"time"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/checks"
	"github.com/imjasonh/playground/git-k8s/internal/gittest"
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

// reconcileWith runs a new check with world holding the Pods that exist.
func reconcileWith(t *testing.T, b *Branch, repo *gitk8s.GitRepository, pods ...*Pod) *kube.Recorder {
	t.Helper()
	world := []any{repo}
	for _, p := range pods {
		world = append(world, p)
	}
	return reconcileIn(t, checks.NewReconciler[Branch](new(gotest).check(), &checks.Config{}), b, world...)
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

// fetch runs the fetch container of the branch's test Pod on this machine,
// with secrets as the values of the Secret's keys. It returns the directory
// that the container fetches into in place of /src/repo.
func fetch(t *testing.T, b *Branch, repo *gitk8s.GitRepository, secrets map[string]string) (string, error) {
	t.Helper()
	pods := kube.Owned[Pod](reconcileWith(t, b, repo))
	if len(pods) != 1 {
		t.Fatalf("owned Pods = %+v", pods)
	}
	c := pods[0].Spec.InitContainers[0]
	dir := filepath.Join(t.TempDir(), "repo")
	cmd := exec.Command(c.Command[0], c.Command[1], strings.ReplaceAll(c.Command[2], "/src/repo", dir))
	// Keep this machine's git configuration out.
	cmd.Env = []string{"PATH=" + os.Getenv("PATH"), "GIT_CONFIG_NOSYSTEM=1"}
	for _, e := range c.Env {
		v := e.Value
		if e.ValueFrom != nil {
			v = secrets[e.ValueFrom.SecretKeyRef.Key]
		}
		cmd.Env = append(cmd.Env, e.Name+"="+v)
	}
	cmd.Env = append(cmd.Env, "HOME="+t.TempDir())
	if out, err := cmd.CombinedOutput(); err != nil {
		return dir, fmt.Errorf("%w: %s", err, out)
	}
	return dir, nil
}

func TestFetchChecksOutHead(t *testing.T) {
	srv := gittest.NewServer(t, "s3cret")
	w := srv.NewWork(t, "app")
	w.Write("add.go", "package app\n")
	b, repo := branch()
	b.Spec.Head = w.Commit("Add add.go")
	w.Push("c/x")
	repo.Spec.URL = srv.Remote("app").URL
	dir, err := fetch(t, b, repo, map[string]string{"username": srv.Username, "password": srv.Password})
	if err != nil {
		t.Fatal(err)
	}
	if _, err := os.Stat(filepath.Join(dir, "add.go")); err != nil {
		t.Errorf("the fetch container didn't check out the head: %v", err)
	}
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
	for url, want := range map[string]string{
		"--upload-pack=touch " + marker + "; false": "blocked",
		"evil::x": "not allowed",
	} {
		b, repo := branch()
		repo.Spec.URL = url
		_, err := fetch(t, b, repo, nil)
		if _, statErr := os.Stat(marker); statErr == nil {
			t.Fatalf("fetching %q ran a command", url)
		}
		if err == nil || !strings.Contains(err.Error(), want) {
			t.Errorf("fetching %q: err = %v, want %q", url, err, want)
		}
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
	since := res.Outputs["waiting"]
	if _, err := time.Parse(time.RFC3339, since); err != nil {
		t.Fatalf("outputs.waiting = %q, want when the branch started waiting", since)
	}
	reconcileWith(t, b, repo, others...)
	if got := b.Status.Checks.Result.Outputs["waiting"]; got != since {
		t.Errorf("outputs.waiting = %q after another reconcile, want %q", got, since)
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

func TestCountsOnlyTestPods(t *testing.T) {
	defer func(n int) { *maxPods = n }(*maxPods)
	*maxPods = 1
	b, repo := branch()
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
	b.Status.Checks.Result = &gitk8s.CheckResult{Commit: head, State: gitk8s.Running, Outputs: map[string]string{
		"pod": podName(name, head, 1), "attempt": "1", "waiting": since.UTC().Format(waitingLayout),
	}}
	return b
}

// startedIn reconciles each branch with r, in a world that holds repo, the
// branches, and pods, and returns the branches that declared a Pod that
// isn't in pods.
func startedIn(t *testing.T, r kube.Reconciler[Branch], repo *gitk8s.GitRepository, branches []*Branch, pods []*Pod) []string {
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
		if i == 0 && newcomer.Status.Checks.Result.Outputs["waiting"] == "" {
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
		wa, wb := a.Status.Checks.Result.Outputs["waiting"], b.Status.Checks.Result.Outputs["waiting"]
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
		if pods := kube.Owned[Pod](reconcileIn(t, r, first, repo, first, second)); len(pods) != 0 {
			t.Errorf("owned Pods = %+v, want app-c-a to wait behind app-c-b once its Pod stops counting", pods)
		}
		if pods := kube.Owned[Pod](reconcileIn(t, r, second, repo, first, second)); len(pods) != 1 {
			t.Errorf("owned Pods = %+v, want app-c-b's Pod", pods)
		}
	})
}

func TestStopsCountingAPodThatTheCacheShowed(t *testing.T) {
	defer func(n int) { *maxPods = n }(*maxPods)
	*maxPods = 1
	b, repo := branch()
	next, _ := branch()
	next.Name = "app-c-y"
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
		rec := reconcileIn(t, checks.NewReconciler[Branch](new(gotest).check(), &checks.Config{}), b, repo, stale)
		if pods := kube.Owned[Pod](rec); len(pods) != 1 {
			t.Errorf("owned Pods = %+v; a branch that %s kept app-c-x waiting", pods, c.why)
		}
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

package main

import (
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
	"testing"
	"time"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/checks"
	"github.com/imjasonh/playground/git-k8s/internal/git"
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
		URL: "https://git.example.com/app.git", SecretRef: &gitk8s.SecretRef{Name: "app-creds"},
	}}
	repo.Namespace = "default"
	return b, repo
}

// named records that the check named the Pod of attempt at b's head, which
// it does before it starts the Pod.
func named(b *Branch, attempt int) {
	b.Status.Checks.Result = &gitk8s.CheckResult{Commit: b.Spec.Head, State: gitk8s.Running, Outputs: map[string]string{
		"pod": podName(b.Name, b.Spec.Head, attempt), "attempt": strconv.Itoa(attempt),
	}}
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

// started returns the Pod that the check declares once its result names
// the Pod.
func started(t *testing.T, b *Branch, repo *gitk8s.GitRepository) *Pod {
	t.Helper()
	named(b, 1)
	rec := reconcileWith(t, b, repo)
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
	if res.State != gitk8s.Running || res.Outputs["attempt"] != "1" || res.Outputs["pod"] != name {
		t.Fatalf("result = %+v, want Running on attempt 1, naming Pod %s", res, name)
	}
	if pods := kube.Owned[Pod](rec); len(pods) != 0 || rec.RequeueAfter() == 0 {
		t.Fatalf("owned Pods = %+v, RequeueAfter = %v; the check names the Pod before it starts it", pods, rec.RequeueAfter())
	}

	t.Log("Once the result names the Pod, the check starts it.")
	rec = reconcileWith(t, b, repo)
	pods := kube.Owned[Pod](rec)
	if len(pods) != 1 || pods[0].Name != name || b.Status.Checks.Result.Outputs["pod"] != name {
		t.Fatalf("owned Pods = %+v, result = %+v", pods, b.Status.Checks.Result)
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

	fetcher, tester := spec.InitContainers[0], spec.Containers[0]
	env := map[string]string{}
	for _, e := range fetcher.Env {
		env[e.Name] = e.Value
	}
	if env["URL"] != "http://git-k8s.git-k8s.svc/default/app.git" || env["GIT_ALLOW_PROTOCOL"] != git.AllowProtocol {
		t.Errorf("fetch container's environment = %v, want the copy on the mirror", env)
	}
	var token *ServiceAccountToken
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
	named(b, 1)
	failed := pod("Failed", &Terminated{ExitCode: 128, Message: "fatal: unable to access", FinishedAt: time.Now()}, nil)
	rec := reconcileWith(t, b, repo, failed)
	res := b.Status.Checks.Result
	if res.State != gitk8s.Running || res.Outputs["attempt"] != "1" || !strings.Contains(res.Message, "trying again at") {
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
	if second := podName("app-c-x", head, 2); res.State != gitk8s.Running || res.Outputs["attempt"] != "2" || res.Outputs["pod"] != second {
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
	if res := b.Status.Checks.Result; res.Outputs["attempt"] != "2" || rec.RequeueAfter() <= time.Second || rec.RequeueAfter() > fetchRetryDelay {
		t.Errorf("result = %+v, RequeueAfter = %v; want attempt 2 to wait %v in all", res, rec.RequeueAfter(), 2*fetchRetryDelay)
	}

	named(b, 3)
	last := pod("Failed", &Terminated{ExitCode: 128, Message: "fatal: unable to access", FinishedAt: time.Now()}, nil)
	last.Name = podName("app-c-x", head, 3)
	reconcileWith(t, b, repo, last)
	if res := b.Status.Checks.Result; res.State != gitk8s.Failed || !strings.Contains(res.Message, "in 3 attempts") {
		t.Errorf("result = %+v, want Failed after 3 attempts", res)
	}
}

// TestFetchScript runs the fetch container on this machine against a server
// that, like the mirror, serves the copy at /NAMESPACE/NAME.git and requires
// the Pod's token.
func TestFetchScript(t *testing.T) {
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
	defer func(u string) { *mirrorURL = u }(*mirrorURL)
	*mirrorURL = mirror.URL + "/"

	b, repo := branch()
	b.Spec.Head = commit
	p := started(t, b, repo)

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

	if _, err := fetch(t, p, "another-token"); err == nil {
		t.Error("the fetch succeeded with a token that the mirror refuses")
	}

	w.Write("b.go", "package app\n")
	w.Commit("second")
	w.Push("c/x")
	if _, err := fetch(t, p, token); err == nil || !strings.Contains(err.Error(), "exit status 3") || !strings.Contains(err.Error(), "no longer points to") {
		t.Errorf("fetch after the branch moved = %v, want exit status 3", err)
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
	defer func(u string) { *mirrorURL = u }(*mirrorURL)
	for url, want := range map[string]string{
		"--upload-pack=touch " + marker + "; false": "blocked",
		"evil::x": "not allowed",
	} {
		*mirrorURL = url
		b, repo := branch()
		_, err := fetch(t, started(t, b, repo), "token")
		if _, statErr := os.Stat(marker); statErr == nil {
			t.Fatalf("fetching from %q ran a command", url)
		}
		if err == nil || !strings.Contains(err.Error(), want) {
			t.Errorf("fetching from %q: err = %v, want %q", url, err, want)
		}
	}
}

// fetch runs pod's fetch container on this machine with token in its token
// file, and returns the directory that holds the checkout in repo.
func fetch(t *testing.T, pod *Pod, token string) (string, error) {
	t.Helper()
	c := pod.Spec.InitContainers[0]
	dir := t.TempDir()
	tokenFile := filepath.Join(dir, "token")
	if err := os.WriteFile(tokenFile, []byte(token), 0o600); err != nil {
		t.Fatal(err)
	}
	script := strings.ReplaceAll(c.Command[2], "/src/repo", filepath.Join(dir, "repo"))
	cmd := exec.Command(c.Command[0], c.Command[1], script)
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

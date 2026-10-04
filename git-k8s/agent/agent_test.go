package agent

import (
	"context"
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"net/http"
	"net/http/httptest"
	"net/url"
	"strconv"
	"strings"
	"sync"
	"testing"
	"time"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/checks"
	"github.com/imjasonh/playground/git-k8s/credentials"
	"github.com/imjasonh/playground/git-k8s/internal/git"
	"github.com/imjasonh/playground/git-k8s/internal/gittest"
	"github.com/imjasonh/playground/kube"
)

// Branch is a review check's view of a GitBranch.
type Branch struct {
	kube.Object `kube:"apiVersion=git-k8s.imjasonh.com/v1alpha1,kind=GitBranch,plural=gitbranches,scope=Namespaced"`
	Spec        gitk8s.GitBranchSpec `json:"spec"`
	Status      struct {
		Checks struct {
			Result *gitk8s.CheckResult `json:"review,omitempty"`
		} `json:"checks,omitzero"`
	} `json:"status,omitzero"`
}

func (b *Branch) Parts() (*kube.ObjectMeta, *gitk8s.GitBranchSpec, **gitk8s.CheckResult) {
	return &b.ObjectMeta, &b.Spec, &b.Status.Checks.Result
}

// fixture is a branch on a git server, a Runner for it, and a server that
// stands in for the result containers of its Pods.
type fixture struct {
	t      *testing.T
	srv    *gittest.Server
	work   *gittest.Work
	b      *Branch
	r      *Runner
	task   Task
	cfg    *checks.Config
	base   string
	result *Result

	mu   sync.Mutex
	body []byte
	uid  string
}

func newFixture(t *testing.T, password string) *fixture {
	srv := gittest.NewServer(t, password)
	w := srv.NewWork(t, "app")
	w.Write("a.txt", "one\ntwo\n")
	w.Write("old.txt", "old\n")
	main := w.Commit("main")
	w.Push("main")
	w.Branch("c/x", main)
	w.Write("a.txt", "one\nDO NOT MERGE\n")
	head := w.Commit("change")
	w.Push("c/x")

	f := &fixture{t: t, srv: srv, work: w, base: main, task: Task{Instructions: "Review the change."}}
	f.b = &Branch{Object: kube.Meta("app-c-x", nil)}
	f.b.Namespace = "default"
	f.b.Spec = gitk8s.GitBranchSpec{
		Repository: "app", Branch: "c/x", Head: head, Parent: "main", ParentHead: main,
		Merge: &gitk8s.MergePolicy{Checks: []gitk8s.CheckPolicy{{Name: "review", MayPush: true}}},
	}
	hs := httptest.NewServer(http.HandlerFunc(f.serveResult))
	t.Cleanup(hs.Close)
	u, err := url.Parse(hs.URL)
	if err != nil {
		t.Fatal(err)
	}
	port, err := strconv.Atoi(u.Port())
	if err != nil {
		t.Fatal(err)
	}
	f.r = &Runner{
		Name: "review", Image: "registry.example.com/agent-runner:test", GitImage: "registry.example.com/git:test",
		Backend: "fake", Model: "composer-2.5", Secret: "cursor-api-key", Timeout: time.Minute, port: port,
	}
	f.cfg = &checks.Config{CacheDir: t.TempDir(), Identity: git.Identity{Name: "git-k8s", Email: "git-k8s@example.com"}}
	return f
}

func (f *fixture) serveResult(w http.ResponseWriter, req *http.Request) {
	f.mu.Lock()
	body, uid := f.body, f.uid
	f.mu.Unlock()
	if req.URL.Path != "/result" || req.Header.Get("Authorization") != "Bearer "+uid {
		http.Error(w, "no", http.StatusUnauthorized)
		return
	}
	w.Write(body)
}

// serve makes the result server serve body to requests with uid, and
// returns body's digest.
func (f *fixture) serve(body []byte, uid string) string {
	f.mu.Lock()
	defer f.mu.Unlock()
	f.body, f.uid = body, uid
	sum := sha256.Sum256(body)
	return "sha256:" + hex.EncodeToString(sum[:])
}

func (f *fixture) reconcile(pods ...*Pod) *kube.Recorder {
	f.t.Helper()
	repo, secret := f.srv.Repository("app")
	world := []any{repo, secret}
	for _, p := range pods {
		world = append(world, p)
	}
	ctx, rec := kube.Fake(f.t.Context(), f.b, world...)
	check := checks.Check{Name: "review", Remote: credentials.Remote, Run: func(ctx context.Context, in *checks.Input) (checks.Verdict, error) {
		v, res := f.r.Run(ctx, in, f.task)
		f.result = res
		return v, nil
	}}
	if err := checks.NewReconciler[Branch](check, f.cfg).Reconcile(ctx, f.b); err != nil {
		f.t.Fatal(err)
	}
	return rec
}

// start reconciles, expects the check to start a Pod, and returns the Pod
// as the API server would hold it.
func (f *fixture) start() *Pod {
	f.t.Helper()
	rec := f.reconcile()
	pods := kube.Owned[Pod](rec)
	res := f.b.Status.Checks.Result
	if len(pods) != 1 || res.State != gitk8s.Running || res.Outputs["pod"] != pods[0].Name {
		f.t.Fatalf("result = %+v and owned Pods = %d, want Running with one Pod", res, len(pods))
	}
	p := pods[0]
	p.Namespace = "default"
	p.UID = "uid-" + p.Name
	return p
}

func (f *fixture) state() *gitk8s.CheckResult { return f.b.Status.Checks.Result }

func review(verdict string, files ...File) []byte {
	cost, charged := 1.25, 0.5
	b, _ := json.Marshal(Result{
		Verdict: verdict, Summary: "1 added line holds DO NOT MERGE", Reasoning: "The change adds DO NOT MERGE at a.txt:2.",
		Model: "fake:composer-2.5", Usage: Usage{InputTokens: 1200, OutputTokens: 80, CacheReadTokens: 300, CacheWriteTokens: 5},
		CostCents: &cost, ChargedCents: &charged, DurationMS: 42, Files: files,
	})
	return b
}

func terminated(t *Terminated) ContainerState { return ContainerState{Terminated: t} }

// finished sets p's status to that of a Pod whose agent reported digest and
// whose result container is serving.
func finished(p *Pod, digest string) *Pod {
	p.Status = PodStatus{
		Phase: "Running", PodIP: "127.0.0.1",
		InitContainerStatuses: []ContainerStatus{
			{Name: "prepare", State: terminated(&Terminated{Reason: "Completed"})},
			{Name: "agent", State: terminated(&Terminated{Reason: "Completed", Message: digest + "\n"})},
		},
		ContainerStatuses: []ContainerStatus{{Name: "result", State: ContainerState{Running: &struct{}{}}}},
	}
	return p
}

func TestReportsTheAgentsVerdict(t *testing.T) {
	f := newFixture(t, "")
	p := f.start()
	if res := f.state(); res.Outputs["runs"] != "1" || res.Outputs["attempt"] != "1" || res.Outputs["base"] != f.base {
		t.Fatalf("outputs = %v, want run 1, attempt 1, and the merge base", res.Outputs)
	}

	t.Log("Until the agent finishes, the check follows the Pod.")
	p.Status = PodStatus{Phase: "Pending", InitContainerStatuses: []ContainerStatus{
		{Name: "prepare", State: terminated(&Terminated{Reason: "Completed"})},
		{Name: "agent", State: ContainerState{Running: &struct{}{}}},
	}}
	f.reconcile(p)
	if res := f.state(); res.State != gitk8s.Running || !strings.Contains(res.Message, "the agent is running in Pod "+p.Name) {
		t.Fatalf("result = %+v, want Running while the agent runs", res)
	}

	digest := f.serve(review(Fail), p.UID)
	rec := f.reconcile(finished(p, digest))
	res := f.state()
	if res.State != gitk8s.Failed || res.Message != "The change adds DO NOT MERGE at a.txt:2." {
		t.Fatalf("result = %+v, want Failed with the agent's reasoning", res)
	}
	want := map[string]string{
		"summary": "1 added line holds DO NOT MERGE", "model": "fake:composer-2.5", "inputTokens": "1200", "outputTokens": "80",
		"cacheReadTokens": "300", "cacheWriteTokens": "5", "costCents": "1.25", "chargedCents": "0.5", "runs": "1", "pod": p.Name,
	}
	for k, v := range want {
		if res.Outputs[k] != v {
			t.Errorf("outputs[%s] = %q, want %q", k, res.Outputs[k], v)
		}
	}
	if f.result == nil || f.result.Usage.InputTokens != 1200 {
		t.Errorf("Run returned %+v, want the agent's result", f.result)
	}
	if rec.RequeueAfter() != time.Second {
		t.Errorf("RequeueAfter = %v; the next reconcile deletes the Pod", rec.RequeueAfter())
	}

	rec = f.reconcile(p)
	if pods := kube.Owned[Pod](rec); len(pods) != 0 || f.state().State != gitk8s.Failed {
		t.Errorf("owned Pods = %d and result = %+v, want the final result and no Pod", len(pods), f.state())
	}
}

func TestPushesTheAgentsChanges(t *testing.T) {
	f := newFixture(t, "s3cret")
	f.task.Edit = true
	head := f.b.Spec.Head
	p := f.start()
	digest := f.serve(review(Fail,
		File{Path: "a.txt", Mode: "100644", Content: []byte("one\n")},
		File{Path: "old.txt", Deleted: true},
		File{Path: "bin/tool", Mode: "100755", Content: []byte("#!/bin/sh\n")},
		File{Path: "link", Mode: "120000", Content: []byte("a.txt")},
	), p.UID)
	f.reconcile(finished(p, digest))
	res := f.state()
	fix := res.Outputs["fix"]
	if res.State != gitk8s.Fixed || fix == "" || !strings.HasPrefix(res.Message, "The change adds DO NOT MERGE at a.txt:2.; pushed ") {
		t.Fatalf("result = %+v, want Fixed with a pushed fix", res)
	}
	if got := f.work.Fetch("c/x"); got != fix {
		t.Fatalf("c/x = %s, want the fix %s", got, fix)
	}
	if got := f.work.Git("ls-tree", "-r", "--format=%(objectmode) %(path)", fix); got != "100644 a.txt\n100755 bin/tool\n120000 link" {
		t.Errorf("fix's files =\n%s", got)
	}
	if got := f.work.Show(fix, "a.txt"); got != "one" {
		t.Errorf("a.txt = %q", got)
	}
	msg := f.work.Git("log", "-1", "--format=%P%n%B", fix)
	if !strings.HasPrefix(msg, head+"\n") || !strings.Contains(msg, "1 added line holds DO NOT MERGE") || !strings.Contains(msg, git.FixerTrailer+": review") {
		t.Errorf("fix's parent and message =\n%s", msg)
	}
}

func TestDoesntPushWhatChangesNothing(t *testing.T) {
	f := newFixture(t, "")
	f.task.Edit = true
	p := f.start()
	digest := f.serve(review(Pass, File{Path: "a.txt", Mode: "100644", Content: []byte("one\nDO NOT MERGE\n")}), p.UID)
	f.reconcile(finished(p, digest))
	if res := f.state(); res.State != gitk8s.Passed || res.Outputs["fix"] != "" {
		t.Errorf("result = %+v, want Passed without a fix", res)
	}
}

func TestRejectsResultsThatDontCheckOut(t *testing.T) {
	for _, tc := range []struct {
		name   string
		edit   bool
		body   []byte
		digest string
		want   string
	}{
		{name: "digest", body: review(Pass), digest: "sha256:" + strings.Repeat("0", 64), want: "its digest doesn't match"},
		{name: "no digest", body: review(Pass), digest: "done", want: "finished without reporting its result's digest"},
		{name: "not JSON", body: []byte("pass"), want: "isn't valid: invalid character"},
		{name: "verdict", body: []byte(`{"verdict":"maybe"}`), want: `its verdict is "maybe"`},
		{name: "usage", body: []byte(`{"verdict":"pass","usage":{"inputTokens":-1}}`), want: "negative usage"},
		{name: "charge", body: []byte(`{"verdict":"pass","chargedCents":-1}`), want: "negative usage"},
		{name: "files", body: review(Pass, File{Path: "a.txt", Mode: "100644"}), want: "it changes files, which its task doesn't allow"},
		{name: "git dir", edit: true, body: review(Pass, File{Path: "sub/.GIT/config", Mode: "100644"}), want: "invalid path"},
		{name: "mode", edit: true, body: review(Pass, File{Path: "sub", Mode: "160000"}), want: `the mode "160000"`},
	} {
		t.Run(tc.name, func(t *testing.T) {
			f := newFixture(t, "")
			f.task.Edit = tc.edit
			p := f.start()
			digest := f.serve(tc.body, p.UID)
			if tc.digest != "" {
				digest = tc.digest
			}
			f.reconcile(finished(p, digest))
			if res := f.state(); res.State != gitk8s.Failed || !strings.Contains(res.Message, tc.want) || f.result != nil {
				t.Errorf("result = %+v, want Failed with %q and no result", res, tc.want)
			}
		})
	}
}

func TestKeepsTryingToFetch(t *testing.T) {
	f := newFixture(t, "")
	p := f.start()
	digest := f.serve(review(Pass), "another Pod's UID")
	rec := f.reconcile(finished(p, digest))
	if res := f.state(); res.State != gitk8s.Running || !strings.Contains(res.Message, "401 Unauthorized") || rec.RequeueAfter() != 5*time.Second {
		t.Fatalf("result = %+v and RequeueAfter = %v, want Running and a retry", res, rec.RequeueAfter())
	}
	if pods := kube.Owned[Pod](rec); len(pods) != 1 || pods[0].Name != p.Name {
		t.Fatal("the check must keep the Pod while it fetches the result")
	}
	f.serve(review(Pass), p.UID)
	f.reconcile(p)
	if res := f.state(); res.State != gitk8s.Passed || res.Outputs["runs"] != "1" {
		t.Errorf("result = %+v, want Passed from the same run", res)
	}
}

func TestReportsPodsThatFail(t *testing.T) {
	waiting := func(name, reason, message string) ContainerStatus {
		return ContainerStatus{Name: name, State: ContainerState{Waiting: &Waiting{Reason: reason, Message: message}}}
	}
	done := ContainerStatus{Name: "prepare", State: terminated(&Terminated{Reason: "Completed"})}
	for _, tc := range []struct {
		name   string
		status PodStatus
		state  string
		want   string
	}{{
		name:   "missing Secret",
		status: PodStatus{Phase: "Pending", InitContainerStatuses: []ContainerStatus{waiting("prepare", "CreateContainerConfigError", `secret "cursor-api-key" not found`)}},
		state:  gitk8s.Running,
		want:   `can't start: container prepare is waiting: CreateContainerConfigError: secret "cursor-api-key" not found`,
	}, {
		name:   "starting",
		status: PodStatus{Phase: "Pending", InitContainerStatuses: []ContainerStatus{waiting("prepare", "PodInitializing", "")}},
		state:  gitk8s.Running,
		want:   "is Pending",
	}, {
		name: "deadline while waiting",
		status: PodStatus{Phase: "Failed", Reason: "DeadlineExceeded", Message: "Pod was active on the node longer than the specified deadline",
			InitContainerStatuses: []ContainerStatus{waiting("prepare", "CreateContainerConfigError", "")}},
		state: gitk8s.Failed,
		want:  "stopped before the agent finished: Pod was active on the node longer than the specified deadline",
	}, {
		name: "deadline while running",
		status: PodStatus{Phase: "Failed", Reason: "DeadlineExceeded", Message: "Pod was active on the node longer than the specified deadline",
			InitContainerStatuses: []ContainerStatus{done, {Name: "agent", State: terminated(&Terminated{ExitCode: 137, Reason: "Error"})}}},
		state: gitk8s.Failed,
		want:  "ran out of time before the agent finished",
	}, {
		name: "result container stopped",
		status: PodStatus{Phase: "Running", PodIP: "127.0.0.1",
			InitContainerStatuses: []ContainerStatus{done, {Name: "agent", State: terminated(&Terminated{Message: "sha256:" + strings.Repeat("a", 64)})}},
			ContainerStatuses:     []ContainerStatus{{Name: "result", State: terminated(&Terminated{ExitCode: 137, Reason: "OOMKilled"})}}},
		state: gitk8s.Failed,
		want:  "stopped before the check fetched the agent's result: OOMKilled",
	}, {
		name: "result container starting",
		status: PodStatus{Phase: "Pending", PodIP: "127.0.0.1",
			InitContainerStatuses: []ContainerStatus{done, {Name: "agent", State: terminated(&Terminated{Message: "sha256:" + strings.Repeat("a", 64)})}},
			ContainerStatuses:     []ContainerStatus{waiting("result", "PodInitializing", "")}},
		state: gitk8s.Running,
		want:  "waiting for Pod review-",
	}} {
		t.Run(tc.name, func(t *testing.T) {
			f := newFixture(t, "")
			p := f.start()
			p.Status = tc.status
			f.reconcile(p)
			if res := f.state(); res.State != tc.state || !strings.Contains(res.Message, tc.want) || res.Outputs["runs"] != "1" {
				t.Errorf("result = %+v, want %s with %q", res, tc.state, tc.want)
			}
		})
	}
	t.Run("agent error message", func(t *testing.T) {
		f := newFixture(t, "")
		p := f.start()
		p.Status = PodStatus{Phase: "Failed", InitContainerStatuses: []ContainerStatus{done,
			{Name: "agent", State: terminated(&Terminated{ExitCode: 1, Message: "Invalid User API Key\n"})}}}
		f.reconcile(p)
		if res := f.state(); res.Message != "the agent failed in Pod "+p.Name+": Invalid User API Key" {
			t.Errorf("message = %q", res.Message)
		}
	})
}

func TestRetriesPreparingTheSource(t *testing.T) {
	f := newFixture(t, "")
	p := f.start()
	names := map[string]bool{p.Name: true}
	for attempt := 2; attempt <= prepareAttempts; attempt++ {
		p.Status = PodStatus{Phase: "Failed", InitContainerStatuses: []ContainerStatus{
			{Name: "prepare", State: terminated(&Terminated{ExitCode: 3, Message: "c/x no longer points to it"})},
		}}
		f.reconcile(p)
		res := f.state()
		if res.State != gitk8s.Running || res.Outputs["attempt"] != strconv.Itoa(attempt) || names[res.Outputs["pod"]] || res.Outputs["runs"] != "1" {
			t.Fatalf("result = %+v, want attempt %d in a new Pod of the same run", res, attempt)
		}
		p = f.start()
		names[p.Name] = true
	}
	p.Status.InitContainerStatuses = []ContainerStatus{{Name: "prepare", State: terminated(&Terminated{ExitCode: 128, Message: "fatal: couldn't find remote ref"})}}
	f.reconcile(p)
	if res := f.state(); res.State != gitk8s.Failed || !strings.Contains(res.Message, "couldn't prepare the source in 3 attempts: fatal: couldn't find remote ref") {
		t.Errorf("result = %+v, want Failed after 3 attempts", res)
	}
}

func TestLimitsRunsPerBranch(t *testing.T) {
	f := newFixture(t, "")
	two := int32(2)
	f.b.Spec.Merge.MaxAgentRuns = &two
	for run := 1; run <= 2; run++ {
		p := f.start()
		f.reconcile(finished(p, f.serve(review(Fail), p.UID)))
		if res := f.state(); res.State != gitk8s.Failed || res.Outputs["runs"] != strconv.Itoa(run) {
			t.Fatalf("result = %+v, want run %d to fail", res, run)
		}
		f.work.Write("a.txt", "run "+strconv.Itoa(run)+"\n")
		f.b.Spec.Head = f.work.Commit("another try")
		f.work.Push("c/x")
	}
	rec := f.reconcile()
	if res := f.state(); res.State != gitk8s.Running || !strings.Contains(res.Message, "used all 2 agent runs that maxAgentRuns allows") || len(kube.Owned[Pod](rec)) != 0 {
		t.Fatalf("result = %+v, want Running without a Pod", res)
	}

	t.Log("Raising the limit starts the run.")
	three := int32(3)
	f.b.Spec.Merge.MaxAgentRuns = &three
	f.start()
	if res := f.state(); res.Outputs["runs"] != "3" {
		t.Errorf("outputs = %v, want run 3", res.Outputs)
	}
}

func TestChangedTaskStartsANewRun(t *testing.T) {
	f := newFixture(t, "")
	first := f.start()
	f.task.Instructions = "Review the change carefully."
	second := f.start()
	if second.Name == first.Name || f.state().Outputs["runs"] != "2" {
		t.Errorf("Pods %s and %s with outputs %v, want a new Pod for run 2", first.Name, second.Name, f.state().Outputs)
	}
}

func TestPassesBranchesWithoutChanges(t *testing.T) {
	f := newFixture(t, "")
	f.b.Spec.Head = f.base
	rec := f.reconcile()
	if res := f.state(); res.State != gitk8s.Passed || res.Message != "the branch has no changes against main" || len(kube.Owned[Pod](rec)) != 0 {
		t.Errorf("result = %+v, want Passed without a Pod", res)
	}
}

func TestWaitsForAPlaceToRun(t *testing.T) {
	f := newFixture(t, "")
	f.r.MaxPods = 1
	other := &Pod{Object: kube.Meta("review-other", map[string]string{agentLabel: "review"})}
	other.Namespace = "elsewhere"
	other.Status.Phase = "Running"
	rec := f.reconcile(other)
	res := f.state()
	if res.State != gitk8s.Running || !strings.Contains(res.Message, "-max-pods is 1") || rec.RequeueAfter() != time.Minute || len(kube.Owned[Pod](rec)) != 0 || res.Outputs["runs"] != "0" {
		t.Fatalf("result = %+v and RequeueAfter = %v, want Running without a Pod or a run", res, rec.RequeueAfter())
	}
	other.Status.Phase = "Succeeded"
	if rec := f.reconcile(other); len(kube.Owned[Pod](rec)) != 1 {
		t.Error("a finished Pod doesn't take a place")
	}
}

func TestLimitsRunsPerDay(t *testing.T) {
	f := newFixture(t, "")
	f.r.MaxRunsPerDay = 1
	f.start()
	f.b.Status.Checks.Result = nil
	f.b.Name = "app-c-y"
	rec := f.reconcile()
	res := f.state()
	if res.State != gitk8s.Running || !strings.Contains(res.Message, "1 agent runs started in the last 24 hours") || len(kube.Owned[Pod](rec)) != 0 {
		t.Fatalf("result = %+v, want Running without a Pod", res)
	}
	if d := rec.RequeueAfter(); d < 23*time.Hour || d > 24*time.Hour {
		t.Errorf("RequeueAfter = %v, want about a day", d)
	}
}

func TestNeedsFlags(t *testing.T) {
	f := newFixture(t, "")
	f.r.Image = ""
	rec := f.reconcile()
	if res := f.state(); res.State != gitk8s.Running || !strings.Contains(res.Message, "set -agent-image") || len(kube.Owned[Pod](rec)) != 0 {
		t.Errorf("result = %+v, want Running without a Pod", res)
	}
}

func TestWindow(t *testing.T) {
	var w window
	t0 := time.Date(2026, 1, 2, 3, 4, 5, 0, time.UTC)
	for i, at := range []time.Duration{0, time.Hour} {
		if _, ok := w.take(t0.Add(at), 2); !ok {
			t.Fatalf("run %d didn't start", i+1)
		}
	}
	if wait, ok := w.take(t0.Add(2*time.Hour), 2); ok || wait != 22*time.Hour {
		t.Errorf("take = %v, %v; want a wait of 22h", wait, ok)
	}
	if _, ok := w.take(t0.Add(24*time.Hour+time.Second), 2); !ok {
		t.Error("the first run is more than a day old, so another can start")
	}
	if _, ok := w.take(t0, 0); !ok {
		t.Error("a limit of 0 means no limit")
	}
}

// newMergeFixture is a fixture whose task merges main into c/x, after both
// changed the second line of a.txt.
func newMergeFixture(t *testing.T) *fixture {
	f := newFixture(t, "s3cret")
	w := f.work
	w.Branch("main", f.base)
	w.Write("a.txt", "one\nTHEIRS\n")
	main := w.Commit("theirs")
	w.Push("main")
	w.Branch("c/x", f.b.Spec.Head)
	f.b.Spec.ParentHead = main
	f.task = Task{Instructions: "Resolve the conflicts.", Merge: &Merge{Commit: main, Ref: "refs/heads/main", Name: "main"}}
	return f
}

func resolution(verdict string, files ...File) []byte {
	b, _ := json.Marshal(Result{
		Verdict: verdict, Summary: "kept both lines", Reasoning: "Both sides add a line, so the merge keeps both.",
		Model: "fake:composer-2.5", Files: files,
	})
	return b
}

func TestResolvesConflicts(t *testing.T) {
	f := newMergeFixture(t)
	head, main := f.b.Spec.Head, f.task.Merge.Commit
	p := f.start()
	if res := f.state(); res.Outputs["base"] != f.base || res.Outputs["runs"] != "1" {
		t.Fatalf("outputs = %v, want run 1 from the merge base", res.Outputs)
	}
	digest := f.serve(resolution(Pass, File{Path: "a.txt", Mode: "100644", Content: []byte("one\nDO NOT MERGE\nTHEIRS\n")}), p.UID)
	f.reconcile(finished(p, digest))
	res := f.state()
	fix := res.Outputs["fix"]
	if res.State != gitk8s.Fixed || fix == "" || !strings.HasPrefix(res.Message, "the agent resolved the conflicts in a.txt; pushed ") {
		t.Fatalf("result = %+v, want Fixed with a pushed merge", res)
	}
	if got := f.work.Fetch("c/x"); got != fix {
		t.Fatalf("c/x = %s, want the merge %s", got, fix)
	}
	want := head + " " + main + "\nMerge main into c/x\n\nkept both lines\n\na.txt\n\n" + git.FixerTrailer + ": review"
	if got := f.work.Git("log", "-1", "--format=%P%n%B", fix); got != want {
		t.Errorf("merge's parents and message =\n%s\nwant\n%s", got, want)
	}
	if got := f.work.Show(fix, "a.txt"); got != "one\nDO NOT MERGE\nTHEIRS" {
		t.Errorf("a.txt = %q", got)
	}
	if got := f.work.Show(fix, "old.txt"); got != "old" {
		t.Errorf("old.txt = %q, want the file that didn't conflict", got)
	}
}

func TestUnionPathsDontReachTheAgent(t *testing.T) {
	f := newMergeFixture(t)
	w := f.work
	w.Branch("main", f.task.Merge.Commit)
	w.Write("go.sum", "y v2\n")
	main := w.Commit("theirs go.sum")
	w.Push("main")
	w.Branch("c/x", f.b.Spec.Head)
	w.Write("go.sum", "z v3\n")
	f.b.Spec.Head = w.Commit("ours go.sum")
	w.Push("c/x")
	f.b.Spec.ParentHead = main
	f.task.Merge.Commit, f.task.Merge.Union = main, []string{"go.sum"}

	p := f.start()
	digest := f.serve(resolution(Pass, File{Path: "a.txt", Mode: "100644", Content: []byte("one\nboth\n")}), p.UID)
	f.reconcile(finished(p, digest))
	res := f.state()
	if res.State != gitk8s.Fixed || !strings.HasPrefix(res.Message, "the agent resolved the conflicts in a.txt; pushed ") {
		t.Fatalf("result = %+v, want Fixed", res)
	}
	if got := f.work.Fetch("c/x"); got != res.Outputs["fix"] {
		t.Fatalf("c/x = %s, want the merge %s", got, res.Outputs["fix"])
	}
	if got := f.work.Show(res.Outputs["fix"], "go.sum"); got != "z v3\ny v2" {
		t.Errorf("go.sum = %q, want both sides' lines", got)
	}
}

func TestRefusesMergesThatTheAgentCantResolve(t *testing.T) {
	for _, tc := range []struct {
		name string
		// main makes main's side of the merge from the fixture's base, and
		// returns the commit to merge.
		main func(f *fixture) string
		want string
	}{{
		name: "no conflicts",
		main: func(f *fixture) string {
			f.work.Write("old.txt", "new\n")
			return f.work.Commit("change old.txt")
		},
		want: "merging main has no conflicts for the agent to resolve",
	}, {
		name: "deleted on one side",
		main: func(f *fixture) string {
			f.work.Git("rm", "--quiet", "a.txt")
			return f.work.Commit("delete a.txt")
		},
		want: "merging main conflicts on a.txt, which isn't a file on both sides",
	}, {
		name: "binary",
		main: func(f *fixture) string {
			f.work.Branch("c/x", f.b.Spec.Head)
			f.work.Write("a.txt", "one\ntwo\n")
			f.work.Write("bin.dat", "\x00ours\n")
			f.b.Spec.Head = f.work.Commit("ours")
			f.work.Push("c/x")
			f.work.Branch("main", f.base)
			f.work.Write("bin.dat", "\x00theirs\n")
			return f.work.Commit("theirs")
		},
		want: "merging main conflicts on bin.dat, which git can't mark with conflict markers",
	}, {
		name: "two merge bases",
		main: func(f *fixture) string {
			f.work.Write("m.txt", "m\n")
			m1 := f.work.Commit("m1")
			f.work.Git("merge", "--quiet", "--no-edit", "--no-ff", f.b.Spec.Head)
			main := f.work.Git("rev-parse", "HEAD")
			f.work.Branch("c/x", f.b.Spec.Head)
			f.work.Git("merge", "--quiet", "--no-edit", "--no-ff", m1)
			f.b.Spec.Head = f.work.Git("rev-parse", "HEAD")
			f.work.Push("c/x")
			return main
		},
		want: "the branch and main have 2 merge bases",
	}, {
		name: "unrelated",
		main: func(f *fixture) string {
			f.work.Git("checkout", "--quiet", "--orphan", "other")
			f.work.Write("a.txt", "unrelated\n")
			return f.work.Commit("unrelated")
		},
		want: "the branch shares no history with main",
	}} {
		t.Run(tc.name, func(t *testing.T) {
			f := newFixture(t, "")
			f.work.Branch("main", f.base)
			main := tc.main(f)
			f.work.Git("checkout", "--quiet", "-B", "main", main)
			f.work.Push("main")
			f.b.Spec.ParentHead = main
			f.task = Task{Instructions: "Resolve the conflicts.", Merge: &Merge{Commit: main, Ref: "refs/heads/main", Name: "main"}}
			rec := f.reconcile()
			res := f.state()
			if res.State != gitk8s.Failed || !strings.Contains(res.Message, tc.want) || res.Outputs["runs"] != "0" || len(kube.Owned[Pod](rec)) != 0 {
				t.Errorf("result = %+v, want Failed with %q and no run", res, tc.want)
			}
		})
	}
}

func TestRejectsBadResolutions(t *testing.T) {
	resolved := File{Path: "a.txt", Mode: "100644", Content: []byte("one\nDO NOT MERGE\nTHEIRS\n")}
	for _, tc := range []struct {
		name string
		body []byte
		want string
	}{
		{name: "no changes", body: resolution(Pass), want: "conflict markers remain in a.txt"},
		{name: "marker", body: resolution(Pass, File{Path: "a.txt", Mode: "100644", Content: []byte("one\n=======\nTHEIRS\n")}), want: "a.txt has more lines that start with ======= than its two sides"},
		{name: "other file", body: resolution(Pass, resolved, File{Path: "old.txt", Mode: "100644", Content: []byte("new\n")}), want: "the agent changed old.txt, which doesn't conflict"},
		{name: "deleted", body: resolution(Pass, File{Path: "a.txt", Deleted: true}), want: "the agent deleted a.txt"},
		{name: "mode", body: resolution(Pass, File{Path: "a.txt", Mode: "100755", Content: resolved.Content}), want: "the agent gave a.txt the mode 100755, which it has on neither side"},
	} {
		t.Run(tc.name, func(t *testing.T) {
			f := newMergeFixture(t)
			p := f.start()
			f.reconcile(finished(p, f.serve(tc.body, p.UID)))
			if res := f.state(); res.State != gitk8s.Failed || !strings.Contains(res.Message, "can't commit the agent's resolution: "+tc.want) || res.Outputs["fix"] != "" {
				t.Errorf("result = %+v, want Failed with %q", res, tc.want)
			}
		})
	}

	t.Run("agent fails", func(t *testing.T) {
		f := newMergeFixture(t)
		p := f.start()
		f.reconcile(finished(p, f.serve(resolution(Fail, resolved), p.UID)))
		if res := f.state(); res.State != gitk8s.Failed || res.Message != "the agent couldn't resolve the conflicts: Both sides add a line, so the merge keeps both." || res.Outputs["fix"] != "" {
			t.Errorf("result = %+v, want Failed with the agent's reasoning and no fix", res)
		}
	})
}

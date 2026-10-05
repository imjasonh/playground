package agent

import (
	"context"
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"errors"
	"maps"
	"net/http"
	"net/http/httptest"
	"net/url"
	"strconv"
	"strings"
	"sync"
	"testing"
	"time"
	"unicode/utf8"

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
	// poll is the repository's pollInterval, if it isn't gittest's.
	poll string
	// lastErr is what kube.LastError returns, if it isn't nil.
	lastErr error

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
	if f.poll != "" {
		repo.Spec.PollInterval = f.poll
	}
	world := []any{repo, secret}
	for _, p := range pods {
		world = append(world, p)
	}
	if f.lastErr != nil {
		world = append(world, f.lastErr)
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

// jobState decodes the run's state from the check's outputs.
func (f *fixture) jobState() JobState {
	f.t.Helper()
	var st JobState
	if err := st.UnmarshalText([]byte(f.state().Outputs["state"])); err != nil {
		f.t.Fatal(err)
	}
	return st
}

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
	if res := f.state(); res.Outputs["runs"] != "1" || f.jobState() != (JobState{Runs: 1, Pod: p.Name, Attempt: 1}) || res.Outputs["base"] != f.base {
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

func TestFollowsARunByItsState(t *testing.T) {
	f := newFixture(t, "")
	p := f.start()
	res := f.state()
	res.Outputs["runs"], res.Outputs["pod"] = "0", "review-0000000000000000"
	rec := f.reconcile(p)
	if pods := kube.Owned[Pod](rec); len(pods) != 1 || pods[0].Name != p.Name || f.jobState() != (JobState{Runs: 1, Pod: p.Name, Attempt: 1, UID: p.UID}) {
		t.Fatalf("state = %+v with %d owned Pods, want run 1 in the same Pod, whatever the runs and pod outputs say", f.jobState(), len(pods))
	}

	t.Log("The next head's run counts on from the state too.")
	f.reconcile(finished(p, f.serve(review(Fail), p.UID)))
	f.state().Outputs["runs"] = "0"
	f.work.Write("a.txt", "one\nnext\n")
	f.b.Spec.Head = f.work.Commit("next")
	f.work.Push("c/x")
	if f.start(); f.jobState().Runs != 2 {
		t.Errorf("state = %+v, want run 2", f.jobState())
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

func TestShortensLongReasoning(t *testing.T) {
	for _, push := range []bool{true, false} {
		f := newFixture(t, "s3cret")
		f.task.Edit = true
		f.b.Spec.Merge.Checks[0].MayPush = push
		p := f.start()
		body, _ := json.Marshal(Result{
			Verdict: Fail, Reasoning: strings.Repeat("é", 1000), Model: "fake:composer-2.5",
			Files: []File{{Path: "a.txt", Mode: "100644", Content: []byte("one\n")}},
		})
		f.reconcile(finished(p, f.serve(body, p.UID)))
		res := f.state()
		suffix := "...; the policy doesn't let this check push the fix"
		if push {
			suffix = "...; pushed " + gitk8s.Short(res.Outputs["fix"])
		}
		if len(res.Message) > 1024 || !utf8.ValidString(res.Message) || !strings.HasSuffix(res.Message, suffix) {
			t.Errorf("message = %q (%d bytes), want valid UTF-8 of at most 1,024 bytes that ends with %q", res.Message, len(res.Message), suffix)
		}
	}
}

func TestShorten(t *testing.T) {
	for _, r := range []string{"a", "é", "€", "😀"} {
		s := strings.Repeat(r, maxMessage+1)
		got := shorten(s)
		kept, ok := strings.CutSuffix(got, "...")
		if !ok || len(got) > maxMessage || len(got) <= maxMessage-utf8.UTFMax || !utf8.ValidString(got) || !strings.HasPrefix(s, kept) {
			t.Errorf("shorten(%d × %q) = %q (%d bytes)", maxMessage+1, r, got, len(got))
		}
	}
	if s := strings.Repeat("é", maxMessage/2); shorten(s) != s {
		t.Errorf("shorten changed a message of %d bytes", len(s))
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
		{name: "merge tree", body: []byte(`{"verdict":"pass","mergeTree":"` + strings.Repeat("4b", 20) + `"}`), want: "it names a merge tree, but its job merges nothing"},
		{name: "error with files", edit: true, body: []byte(`{"verdict":"fail","error":"broke","files":[{"path":"a.txt","mode":"100644"}]}`), want: "it reports an error but also changes files"},
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
		age    time.Duration
		status PodStatus
		state  string
		want   string
	}{{
		name:   "missing Secret",
		age:    stuckAfter,
		status: PodStatus{Phase: "Pending", InitContainerStatuses: []ContainerStatus{waiting("prepare", "CreateContainerConfigError", `secret "app-creds" not found`)}},
		state:  gitk8s.Failed,
		want:   `couldn't start in 5 minutes: container prepare is waiting: CreateContainerConfigError: secret "app-creds" not found`,
	}, {
		name:   "missing Secret in a new Pod",
		age:    stuckAfter - time.Minute,
		status: PodStatus{Phase: "Pending", InitContainerStatuses: []ContainerStatus{waiting("prepare", "CreateContainerConfigError", `secret "app-creds" not found`)}},
		state:  gitk8s.Running,
		want:   `can't start: container prepare is waiting: CreateContainerConfigError: secret "app-creds" not found`,
	}, {
		name:   "image that can't be pulled",
		age:    stuckAfter,
		status: PodStatus{Phase: "Pending", InitContainerStatuses: []ContainerStatus{done, waiting("agent", "ErrImagePull", "not found")}},
		state:  gitk8s.Failed,
		want:   "couldn't start in 5 minutes: container agent is waiting: ErrImagePull: not found",
	}, {
		name:   "image that can't be pulled in a new Pod",
		age:    stuckAfter - time.Minute,
		status: PodStatus{Phase: "Pending", InitContainerStatuses: []ContainerStatus{done, waiting("agent", "ErrImagePull", "not found")}},
		state:  gitk8s.Running,
		want:   "can't start: container agent is waiting: ErrImagePull: not found",
	}, {
		name:   "backing off pulling an image",
		age:    stuckAfter,
		status: PodStatus{Phase: "Pending", InitContainerStatuses: []ContainerStatus{waiting("prepare", "ImagePullBackOff", "Back-off pulling image")}},
		state:  gitk8s.Failed,
		want:   "couldn't start in 5 minutes: container prepare is waiting: ImagePullBackOff: Back-off pulling image",
	}, {
		name:   "backing off pulling an image in a new Pod",
		age:    stuckAfter - time.Minute,
		status: PodStatus{Phase: "Pending", InitContainerStatuses: []ContainerStatus{waiting("prepare", "ImagePullBackOff", "Back-off pulling image")}},
		state:  gitk8s.Running,
		want:   "can't start: container prepare is waiting: ImagePullBackOff: Back-off pulling image",
	}, {
		name:   "invalid image",
		status: PodStatus{Phase: "Pending", InitContainerStatuses: []ContainerStatus{waiting("prepare", "InvalidImageName", "")}},
		state:  gitk8s.Failed,
		want:   "can't start: container prepare is waiting: InvalidImageName",
	}, {
		name:   "container that the runtime couldn't create yet",
		status: PodStatus{Phase: "Pending", InitContainerStatuses: []ContainerStatus{waiting("prepare", "CreateContainerError", "failed to reserve container name")}},
		state:  gitk8s.Running,
		want:   "can't start: container prepare is waiting: CreateContainerError: failed to reserve container name",
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
		name: "evicted while preparing the source",
		status: PodStatus{Phase: "Failed", Reason: "Evicted", Message: `Usage of EmptyDir volume "git" exceeds the limit "2Gi". `,
			InitContainerStatuses: []ContainerStatus{{Name: "prepare", State: terminated(&Terminated{ExitCode: 137, Reason: "Error"})}, waiting("agent", "PodInitializing", "")}},
		state: gitk8s.Failed,
		want:  `was evicted: Usage of EmptyDir volume "git" exceeds the limit "2Gi".`,
	}, {
		name: "evicted while running",
		status: PodStatus{Phase: "Failed", Reason: "Evicted", Message: "Pod ephemeral local storage usage exceeds the total limit of containers 7488Mi. ",
			InitContainerStatuses: []ContainerStatus{done, {Name: "agent", State: terminated(&Terminated{ExitCode: 137, Reason: "Error"})}}},
		state: gitk8s.Failed,
		want:  "was evicted: Pod ephemeral local storage usage exceeds the total limit of containers 7488Mi.",
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
			p.CreationTimestamp = time.Now().Add(-tc.age)
			p.Status = tc.status
			rec := f.reconcile(p)
			if res := f.state(); res.State != tc.state || !strings.Contains(res.Message, tc.want) || res.Outputs["runs"] != "1" {
				t.Errorf("result = %+v, want %s with %q", res, tc.state, tc.want)
			}
			if d := rec.RequeueAfter(); tc.age == stuckAfter-time.Minute && (d <= 0 || d > time.Minute) {
				t.Errorf("RequeueAfter = %v, want a reconcile when the Pod is %v old", d, stuckAfter)
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

func TestCountsTheGraceFromWhenAContainerCanStart(t *testing.T) {
	now := time.Now()
	pull := func(name string) ContainerStatus {
		return ContainerStatus{Name: name, State: ContainerState{Waiting: &Waiting{Reason: "ErrImagePull", Message: "unexpected status code 503 Service Unavailable"}}}
	}
	prepared := func(at time.Time) ContainerStatus {
		return ContainerStatus{Name: "prepare", State: terminated(&Terminated{Reason: "Completed", FinishedAt: at})}
	}
	for _, tc := range []struct {
		name   string
		status PodStatus
		// left is how long the container has before the run fails, or 0
		// if the run fails now.
		left time.Duration
	}{{
		name:   "prepare in a Pod that waited for a node",
		status: PodStatus{Phase: "Pending", StartTime: now.Add(-30 * time.Second), InitContainerStatuses: []ContainerStatus{pull("prepare")}},
		left:   stuckAfter - 30*time.Second,
	}, {
		name:   "prepare in a Pod that started long ago",
		status: PodStatus{Phase: "Pending", StartTime: now.Add(-stuckAfter), InitContainerStatuses: []ContainerStatus{pull("prepare")}},
	}, {
		name:   "agent after prepare finished",
		status: PodStatus{Phase: "Pending", StartTime: now.Add(-9 * time.Minute), InitContainerStatuses: []ContainerStatus{prepared(now.Add(-time.Minute)), pull("agent")}},
		left:   stuckAfter - time.Minute,
	}, {
		name:   "agent long after prepare finished",
		status: PodStatus{Phase: "Pending", StartTime: now.Add(-9 * time.Minute), InitContainerStatuses: []ContainerStatus{prepared(now.Add(-stuckAfter)), pull("agent")}},
	}} {
		t.Run(tc.name, func(t *testing.T) {
			f := newFixture(t, "")
			p := f.start()
			p.CreationTimestamp = now.Add(-10 * time.Minute)
			p.Status = tc.status
			rec := f.reconcile(p)
			res, d := f.state(), rec.RequeueAfter()
			switch {
			case tc.left == 0 && (res.State != gitk8s.Failed || !strings.Contains(res.Message, "couldn't start in 5 minutes")):
				t.Errorf("result = %+v, want Failed", res)
			case tc.left > 0 && (res.State != gitk8s.Running || d > tc.left || d < tc.left-10*time.Second):
				t.Errorf("result = %+v and RequeueAfter = %v, want Running and a reconcile in %v", res, d, tc.left)
			}
		})
	}
}

func TestEndsARunWhosePodCantBeScheduled(t *testing.T) {
	f := newFixture(t, "")
	p := f.start()
	why := "0/3 nodes are available: 3 Insufficient ephemeral-storage."
	p.CreationTimestamp = time.Now().Add(-time.Minute)
	p.Status = PodStatus{Phase: "Pending", Conditions: []PodCondition{{Type: "PodScheduled", Status: "False", Reason: "Unschedulable", Message: why}}}
	rec := f.reconcile(p)
	if res := f.state(); res.State != gitk8s.Running || res.Message != "Pod "+p.Name+" can't be scheduled: "+why {
		t.Fatalf("result = %+v, want Running with the scheduler's message", res)
	}
	if d := rec.RequeueAfter(); d > stuckAfter-time.Minute || d < stuckAfter-time.Minute-10*time.Second {
		t.Errorf("RequeueAfter = %v, want a reconcile when the Pod is %v old", d, stuckAfter)
	}

	t.Log("A scheduled Pod that's still pending isn't stuck.")
	p.Status.Conditions[0].Status = "True"
	f.reconcile(p)
	if res := f.state(); res.State != gitk8s.Running || res.Message != "Pod "+p.Name+" is Pending" {
		t.Fatalf("result = %+v, want the Pod Pending", res)
	}

	t.Log("Once the Pod is stuckAfter old, the run ends, and the next reconcile doesn't declare the Pod, so kube deletes it and frees its place in -max-pods.")
	p.Status.Conditions[0].Status = "False"
	p.CreationTimestamp = time.Now().Add(-2 * time.Hour)
	f.reconcile(p)
	if res := f.state(); res.State != gitk8s.Failed || res.Message != "Pod "+p.Name+" couldn't be scheduled in 5 minutes: "+why || res.Outputs["runs"] != "1" {
		t.Fatalf("result = %+v, want Failed after 1 run", res)
	}
	if rec := f.reconcile(p); len(kube.Owned[Pod](rec)) != 0 {
		t.Error("the next reconcile must stop declaring the Pod")
	}
}

func TestReportsWhatAFailedRunUsed(t *testing.T) {
	f := newFixture(t, "")
	p := f.start()
	cost := 0.75
	body, _ := json.Marshal(Result{
		Verdict: Fail, Model: "fake:composer-2.5", Usage: Usage{InputTokens: 900, OutputTokens: 10},
		CostCents: &cost, DurationMS: 7, Error: "the agent didn't finish in 900s\x00",
	})
	f.reconcile(finished(p, f.serve(body, p.UID)))
	res := f.state()
	if res.State != gitk8s.Failed || res.Message != "the agent failed in Pod "+p.Name+": the agent didn't finish in 900s" || f.result != nil {
		t.Fatalf("result = %+v and Run returned %+v, want Failed with the error and no result", res, f.result)
	}
	state, _ := JobState{Runs: 1, Pod: p.Name, Attempt: 1, UID: p.UID}.MarshalText()
	want := map[string]string{
		"model": "fake:composer-2.5", "inputTokens": "900", "outputTokens": "10", "cacheReadTokens": "0", "cacheWriteTokens": "0",
		"costCents": "0.75", "runs": "1", "pod": p.Name, "state": string(state),
	}
	if !maps.Equal(res.Outputs, want) {
		t.Errorf("outputs = %v, want %v", res.Outputs, want)
	}
}

func TestCountsAPodThatsCreatedAgain(t *testing.T) {
	f := newFixture(t, "")
	two := int32(2)
	f.b.Spec.Merge.MaxAgentRuns = &two
	f.r.MaxRunsPerDay = 2
	p := f.start()
	f.reconcile(p)
	if st := f.jobState(); st.UID != p.UID {
		t.Fatalf("state = %+v, want the Pod's UID", st)
	}

	t.Log("kube creates a deleted Pod again, which runs the agent again.")
	rec := f.reconcile()
	if res := f.state(); res.State != gitk8s.Running || res.Message != "creating Pod "+p.Name+" again, because it was deleted" || len(kube.Owned[Pod](rec)) != 1 {
		t.Fatalf("result = %+v, want Running with the Pod declared", res)
	}
	p.UID = "uid-again"
	f.reconcile(p)
	if res := f.state(); res.State != gitk8s.Running || res.Outputs["runs"] != "2" || f.jobState().UID != p.UID {
		t.Fatalf("outputs = %v, want run 2 in the new Pod", res.Outputs)
	}
	f.reconcile(finished(p, f.serve(review(Pass), p.UID)))
	if res := f.state(); res.State != gitk8s.Passed || res.Outputs["runs"] != "2" {
		t.Errorf("result = %+v, want Passed after 2 runs", res)
	}
}

func TestWaitsForADeletedPodToGo(t *testing.T) {
	f := newFixture(t, "")
	p := f.start()
	f.reconcile(p)

	t.Log("Deleting a Pod stops its agent, which doesn't fail the run.")
	deleted := time.Now()
	p.DeletionTimestamp = &deleted
	p.Status = PodStatus{Phase: "Failed", InitContainerStatuses: []ContainerStatus{
		{Name: "prepare", State: terminated(&Terminated{Reason: "Completed"})},
		{Name: "agent", State: terminated(&Terminated{ExitCode: 143, Reason: "Error"})},
	}}
	f.reconcile(p)
	if res := f.state(); res.State != gitk8s.Running || res.Message != "Pod "+p.Name+" is being deleted, so kube creates it again once it's gone" || res.Outputs["runs"] != "1" {
		t.Fatalf("result = %+v, want Running after 1 run", res)
	}

	t.Log("Once the Pod is gone, kube creates it again, and the agent runs again.")
	if rec := f.reconcile(); len(kube.Owned[Pod](rec)) != 1 {
		t.Fatal("the check must declare the Pod again")
	}
	p.DeletionTimestamp, p.Status, p.UID = nil, PodStatus{}, "uid-again"
	f.reconcile(p)
	if res := f.state(); res.State != gitk8s.Running || res.Outputs["runs"] != "2" || f.jobState().UID != p.UID {
		t.Fatalf("result = %+v, want run 2 in the new Pod", res)
	}

	t.Log("A Pod that kube created again is another run, even if it's being deleted when the check first sees it.")
	p.DeletionTimestamp, p.UID = &deleted, "uid-third"
	f.reconcile(p)
	if res := f.state(); res.State != gitk8s.Running || res.Message != "Pod "+p.Name+" is being deleted, so kube creates it again once it's gone" ||
		res.Outputs["runs"] != "3" || f.jobState().UID != p.UID {
		t.Errorf("result = %+v, want run 3 in the Pod that's being deleted", res)
	}
}

func TestSaysWhenKubeCantCreateAPod(t *testing.T) {
	f := newFixture(t, "")
	p := f.start()
	if res := f.state(); res.Message != "started Pod "+p.Name {
		t.Fatalf("result = %+v, want the Pod started", res)
	}

	t.Log("A Pod that kube couldn't create, such as one that a LimitRange rejects, still doesn't exist on the next reconcile.")
	rec := f.reconcile()
	want := "kube can't create Pod " + p.Name + ": the program's log says why, such as a ResourceQuota or LimitRange that doesn't allow its ephemeral-storage limit of 7488Mi"
	if res := f.state(); res.State != gitk8s.Running || res.Message != want || res.Outputs["runs"] != "1" || len(kube.Owned[Pod](rec)) != 1 {
		t.Fatalf("result = %+v, want Running with the Pod declared", res)
	}

	t.Log("When kube has the last try's error, such as the check Pod policy's denial, the check reports it and declares the Pod again.")
	f.lastErr = errors.New(`applying Pod.v1 default/` + p.Name + `: pods "` + p.Name + `" is forbidden: ` +
		`ValidatingAdmissionPolicy 'git-k8s-check-pods' with binding 'git-k8s-check-pods' denied request: ` +
		`the review check can't create or change Pods in namespace default, which doesn't have the label ` +
		`git-k8s.imjasonh.com/check-pods=true (422 Invalid)`)
	rec = f.reconcile()
	want = "kube can't create Pod " + p.Name + ": " + f.lastErr.Error()
	if res := f.state(); res.State != gitk8s.Running || res.Message != want || res.Outputs["runs"] != "1" || len(kube.Owned[Pod](rec)) != 1 {
		t.Fatalf("result = %+v, want Running with kube's error and the Pod declared", res)
	}
	f.lastErr = nil
	f.reconcile(p)
	if res := f.state(); res.Message != "Pod "+p.Name+" is Pending" {
		t.Errorf("result = %+v, want the Pod Pending once it exists", res)
	}
}

func TestEndsARunWhenItsNewPodPassesALimit(t *testing.T) {
	for _, tc := range []struct {
		name          string
		maxAgentRuns  int32
		maxRunsPerDay int
		want          string
	}{
		{"maxAgentRuns", 1, 0, "the branch used all 1 agent runs that maxAgentRuns allows"},
		{"-max-runs-per-day", 10, 1, "1 agent runs started in the last 24 hours, the -max-runs-per-day limit"},
	} {
		t.Run(tc.name, func(t *testing.T) {
			f := newFixture(t, "")
			f.b.Spec.Merge.MaxAgentRuns = &tc.maxAgentRuns
			f.r.MaxRunsPerDay = tc.maxRunsPerDay
			p := f.start()
			f.reconcile(p)
			p.UID = "uid-again"
			f.reconcile(p)
			if res := f.state(); res.State != gitk8s.Failed || res.Message != "Pod "+p.Name+" was deleted and created again, but "+tc.want || res.Outputs["runs"] != "1" {
				t.Errorf("result = %+v, want Failed after 1 run", res)
			}
			if rec := f.reconcile(p); len(kube.Owned[Pod](rec)) != 0 {
				t.Error("the next reconcile must stop declaring the Pod")
			}
		})
	}
}

func TestWontCreateADeletedPodAgainPastALimit(t *testing.T) {
	for _, tc := range []struct {
		name          string
		maxAgentRuns  int32
		maxRunsPerDay int
		want          string
	}{
		{"maxAgentRuns", 1, 0, "the branch used all 1 agent runs that maxAgentRuns allows"},
		{"-max-runs-per-day", 10, 1, "1 agent runs started in the last 24 hours, the -max-runs-per-day limit"},
	} {
		t.Run(tc.name, func(t *testing.T) {
			f := newFixture(t, "")
			f.b.Spec.Merge.MaxAgentRuns = &tc.maxAgentRuns
			f.r.MaxRunsPerDay = tc.maxRunsPerDay
			p := f.start()
			f.reconcile(p)
			rec := f.reconcile()
			if res := f.state(); res.State != gitk8s.Failed || res.Message != "Pod "+p.Name+" was deleted, but "+tc.want || res.Outputs["runs"] != "1" || len(kube.Owned[Pod](rec)) != 0 {
				t.Errorf("result = %+v with %d owned Pods, want Failed without the Pod", res, len(kube.Owned[Pod](rec)))
			}
		})
	}
}

func TestRetriesPreparingTheSource(t *testing.T) {
	f := newFixture(t, "")
	p := f.start()
	names := map[string]bool{p.Name: true}
	for attempt := 2; attempt <= prepareAttempts; attempt++ {
		p.Status = PodStatus{Phase: "Failed", InitContainerStatuses: []ContainerStatus{
			{Name: "prepare", State: terminated(&Terminated{ExitCode: 128, Message: "fatal: unable to access the repository"})},
		}}
		rec := f.reconcile(p)
		res := f.state()
		pods := kube.Owned[Pod](rec)
		if res.State != gitk8s.Running || f.jobState().Attempt != attempt || names[res.Outputs["pod"]] || res.Outputs["runs"] != "1" ||
			len(pods) != 2 || pods[1].Name != res.Outputs["pod"] {
			t.Fatalf("result = %+v with %d owned Pods, want attempt %d in a new Pod of the same run, declared at once", res, len(pods), attempt)
		}
		p = pods[1]
		p.Namespace, p.UID = "default", "uid-"+p.Name
		names[p.Name] = true
	}
	p.Status.InitContainerStatuses = []ContainerStatus{{Name: "prepare", State: terminated(&Terminated{ExitCode: 128, Message: "fatal: couldn't find remote ref"})}}
	f.reconcile(p)
	if res := f.state(); res.State != gitk8s.Failed || !strings.Contains(res.Message, "couldn't prepare the source in 3 attempts: fatal: couldn't find remote ref") {
		t.Errorf("result = %+v, want Failed after 3 attempts", res)
	}
}

func TestWaitsForTheNewHeadWhenTheBranchMoved(t *testing.T) {
	f := newFixture(t, "")
	two := int32(2)
	f.b.Spec.Merge.MaxAgentRuns = &two
	f.r.MaxRunsPerDay = 2
	first := f.start()
	f.reconcile(finished(first, f.serve(review(Fail), first.UID)))
	f.work.Write("a.txt", "one\nretry\n")
	f.b.Spec.Head = f.work.Commit("retry")
	f.work.Push("c/x")
	p := f.start()

	t.Log("The agent doesn't run on a branch that moved, so the run doesn't count, once.")
	moved := "c/x no longer points to " + f.b.Spec.Head
	p.Status = PodStatus{Phase: "Failed", InitContainerStatuses: []ContainerStatus{
		{Name: "prepare", State: terminated(&Terminated{ExitCode: movedStatus, Message: moved, FinishedAt: time.Now()})},
	}}
	for range 2 {
		rec := f.reconcile(p)
		if res := f.state(); res.State != gitk8s.Running || res.Message != "waiting up to a minute for a run on the new commits: "+moved || res.Outputs["pod"] != p.Name ||
			f.jobState() != (JobState{Runs: 1, Pod: p.Name, Attempt: 1, UID: p.UID, Refunded: p.UID}) {
			t.Fatalf("result = %+v, want Running in the same Pod with the run given back", res)
		}
		if pods := kube.Owned[Pod](rec); len(pods) != 1 || pods[0].Name != p.Name || rec.RequeueAfter() < 59*time.Second || rec.RequeueAfter() > time.Minute {
			t.Fatalf("owned Pods = %d and RequeueAfter = %v, want the same Pod and a retry in about a minute", len(pods), rec.RequeueAfter())
		}
	}

	t.Log("The new head starts a new run, which the limits still allow.")
	f.work.Write("a.txt", "one\nmoved\n")
	f.b.Spec.Head = f.work.Commit("move")
	f.work.Push("c/x")
	if q := f.start(); q.Name == p.Name || f.state().Outputs["runs"] != "2" {
		t.Errorf("outputs = %v, want run 2 in a new Pod", f.state().Outputs)
	}
}

func TestPreparesTheSourceAgainWhenTheHeadStaysTheSame(t *testing.T) {
	f := newFixture(t, "")
	f.r.MaxRunsPerDay = 1
	p := f.start()
	moved := "c/x no longer points to " + f.b.Spec.Head
	for attempt := 1; ; attempt++ {
		t.Logf("Attempt %d finds that the branch moved, and then the branch moves back.", attempt)
		exited := &Terminated{ExitCode: movedStatus, Message: moved, FinishedAt: time.Now()}
		p.Status = PodStatus{Phase: "Failed", InitContainerStatuses: []ContainerStatus{{Name: "prepare", State: terminated(exited)}}}
		rec := f.reconcile(p)
		if res := f.state(); res.State != gitk8s.Running || res.Message != "waiting up to a minute for a run on the new commits: "+moved ||
			res.Outputs["runs"] != "0" || len(f.r.day.starts) != 0 || rec.RequeueAfter() < 59*time.Second || rec.RequeueAfter() > time.Minute {
			t.Fatalf("result = %+v with %d runs in the last day and RequeueAfter = %v, want the run given back and a retry in about a minute", res, len(f.r.day.starts), rec.RequeueAfter())
		}

		exited.FinishedAt = time.Now().Add(-movedWait)
		rec = f.reconcile(p)
		res := f.state()
		if attempt == prepareAttempts {
			if res.State != gitk8s.Failed || res.Message != "couldn't prepare the source in 3 attempts: "+moved || res.Outputs["runs"] != "0" || len(f.r.day.starts) != 0 {
				t.Errorf("result = %+v with %d runs in the last day, want Failed without a run", res, len(f.r.day.starts))
			}
			return
		}
		pods := kube.Owned[Pod](rec)
		if len(pods) != 2 || pods[1].Name != res.Outputs["pod"] {
			t.Fatalf("owned Pods = %d and outputs = %v, want the old Pod and the new one", len(pods), res.Outputs)
		}
		next := pods[1]
		want := "preparing the source again in Pod " + next.Name + ", because the run is still for the same commits after Pod " + p.Name + " found that " + moved
		if st := f.jobState(); res.State != gitk8s.Running || res.Message != want || st.Runs != 1 || st.Attempt != attempt+1 || st.UID != "" || len(f.r.day.starts) != 1 {
			t.Fatalf("result = %+v with %d runs in the last day, want attempt %d as a new run", res, len(f.r.day.starts), attempt+1)
		}
		p = next
		p.Namespace, p.UID = "default", "uid-"+p.Name
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

func TestRestartsARunWhenAFlagChanges(t *testing.T) {
	f := newFixture(t, "")
	one := int32(1)
	f.b.Spec.Merge.MaxAgentRuns = &one
	f.r.MaxRunsPerDay = 2
	p := f.start()
	f.reconcile(p)

	t.Log("A deploy with another -model starts the run again in a new Pod, though the branch used all of its runs.")
	f.r.Model = "composer-3"
	rec := f.reconcile(p)
	pods := kube.Owned[Pod](rec)
	if res := f.state(); len(pods) != 1 || pods[0].Name == p.Name || res.State != gitk8s.Running || res.Message != "started Pod "+pods[0].Name ||
		res.Outputs["pod"] != pods[0].Name || res.Outputs["runs"] != "1" || f.jobState().UID != "" {
		t.Fatalf("result = %+v with %d owned Pods, want run 1 in a new Pod", res, len(pods))
	}
	q := pods[0]
	q.Namespace, q.UID = "default", "uid-"+q.Name

	t.Log("Another restart waits for a place in -max-runs-per-day without a Pod.")
	f.r.Model = "composer-4"
	rec = f.reconcile(q)
	if res := f.state(); res.State != gitk8s.Running || res.Message != "waiting to start the agent again: 2 agent runs started in the last 24 hours, the -max-runs-per-day limit" ||
		res.Outputs["pod"] != q.Name || res.Outputs["runs"] != "1" || len(kube.Owned[Pod](rec)) != 0 {
		t.Fatalf("result = %+v, want Running without a Pod", res)
	}
	if d := rec.RequeueAfter(); d < 23*time.Hour || d > 24*time.Hour {
		t.Errorf("RequeueAfter = %v, want about a day", d)
	}

	t.Log("With the flag back, the run finishes in the restarted Pod.")
	f.r.Model = "composer-3"
	f.reconcile(finished(q, f.serve(review(Pass), q.UID)))
	if res := f.state(); res.State != gitk8s.Passed || res.Outputs["runs"] != "1" {
		t.Errorf("result = %+v, want Passed after 1 run", res)
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

	t.Log("A -source-size that isn't a size starts no Pod either.")
	f = newFixture(t, "")
	f.r.SourceSize = "2GB"
	rec = f.reconcile()
	if res := f.state(); res.State != gitk8s.Running || !strings.Contains(res.Message, `-source-size is "2GB", but it must be a size such as 2Gi`) || len(kube.Owned[Pod](rec)) != 0 {
		t.Errorf("result = %+v, want Running without a Pod", res)
	}

	t.Log("Nor does a -storage-request that isn't a size or that's more than the Pod's limit.")
	for request, want := range map[string]string{
		"1GB": `-storage-request is "1GB", but it must be a size such as 1Gi`,
		"8Gi": "-storage-request is 8Gi, but it can't be more than 7488Mi, each agent Pod's ephemeral-storage limit",
	} {
		f = newFixture(t, "")
		f.r.StorageRequest = request
		rec = f.reconcile()
		if res := f.state(); res.State != gitk8s.Running || !strings.Contains(res.Message, want) || len(kube.Owned[Pod](rec)) != 0 {
			t.Errorf("-storage-request %s: result = %+v, want Running without a Pod", request, res)
		}
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
	if !w.full(t0.Add(2*time.Hour), 2) || w.full(t0.Add(2*time.Hour), 3) || w.full(t0, 0) {
		t.Error("full must report a limit that 2 runs reach, without recording a run")
	}
	if _, ok := w.take(t0.Add(24*time.Hour+time.Second), 2); !ok {
		t.Error("the first run is more than a day old, so another can start")
	}
	n := len(w.starts)
	if _, ok := w.take(t0, 0); !ok || len(w.starts) != n {
		t.Error("a limit of 0 means no limit, so take records nothing")
	}

	t.Log("giveBack forgets the latest run, once for each Pod, and forgets the Pod after a day.")
	if !w.giveBack(t0.Add(25*time.Hour), "uid-1") || len(w.starts) != n-1 || !w.starts[len(w.starts)-1].Equal(t0.Add(time.Hour)) {
		t.Fatalf("giveBack didn't forget the latest run: runs started at %v, want %d ending at %v", w.starts, n-1, t0.Add(time.Hour))
	}
	if w.giveBack(t0.Add(26*time.Hour), "uid-1") || len(w.starts) != n-1 {
		t.Errorf("giveBack forgot another run for the same Pod: %d runs, want %d", len(w.starts), n-1)
	}
	if !w.giveBack(t0.Add(49*time.Hour), "uid-2") || len(w.given) != 1 {
		t.Errorf("giveBack holds %d Pods, want only the one from the last day", len(w.given))
	}

	t.Log("note keeps the runs that each Pod's state last counted, by namespace, and forgets a Pod that no call noted in a day.")
	w.note(t0, "default", &JobState{Runs: 2, Pod: "review-a"})
	w.note(t0, "other", &JobState{Runs: 3, Pod: "review-a"})
	w.note(t0.Add(time.Hour), "other", &JobState{Runs: 1, Pod: "review-a"})
	w.note(t0.Add(time.Hour), "default", &JobState{Runs: 4})
	a, _ := w.runs("default", "review-a")
	b, _ := w.runs("other", "review-a")
	if _, ok := w.runs("default", "review-b"); a != 2 || b != 1 || ok {
		t.Errorf("runs = %d and %d, want 2 and 1 for Pods with the same name in two namespaces, and none for a Pod that no call noted", a, b)
	}
	w.note(t0.Add(24*time.Hour), "default", &JobState{})
	_, okA := w.runs("default", "review-a")
	b, okB := w.runs("other", "review-a")
	if okA || !okB || b != 1 || len(w.counted) != 1 {
		t.Errorf("note holds %d Pods, want only the one noted in the last day", len(w.counted))
	}
}

// movedPod sets p's status to that of a Pod that found, at finished, that
// the branch no longer points to head.
func movedPod(p *Pod, head string, finished time.Time) *Pod {
	p.Status = PodStatus{Phase: "Failed", InitContainerStatuses: []ContainerStatus{
		{Name: "prepare", State: terminated(&Terminated{ExitCode: movedStatus, Message: "c/x no longer points to " + head, FinishedAt: finished})},
	}}
	return p
}

// newHead pushes a commit that sets a.txt to content, and makes it the
// branch's head.
func (f *fixture) newHead(content string) {
	f.work.Write("a.txt", content)
	f.b.Spec.Head = f.work.Commit("another head")
	f.work.Push("c/x")
}

func TestCountsRunsOnceWhenTheBranchMovesBack(t *testing.T) {
	for _, tc := range []struct {
		name     string
		deleting bool
	}{{"old Pod", false}, {"old Pod being deleted", true}} {
		t.Run(tc.name, func(t *testing.T) {
			f := newFixture(t, "")
			f.r.MaxRunsPerDay = 10
			head := f.b.Spec.Head
			p := f.start()
			f.reconcile(movedPod(p, head, time.Now()))
			f.newHead("one\nnext\n")
			q := f.start()
			f.reconcile(finished(q, f.serve(review(Fail), q.UID)))

			t.Log("The branch moves back while the first head's Pod still exists, so the check follows that Pod, whose run it gave back.")
			f.b.Spec.Head = head
			old := movedPod(p, head, time.Now().Add(-2*movedWait))
			if !tc.deleting {
				rec := f.reconcile(old)
				if pods := kube.Owned[Pod](rec); len(pods) != 2 || f.jobState().Attempt != 2 || f.jobState().Pod != pods[1].Name {
					t.Fatalf("state = %+v with %d owned Pods, want attempt 2 in a new Pod", f.jobState(), len(pods))
				}
			} else {
				now := time.Now()
				old.DeletionTimestamp = &now
				f.reconcile(old)
				if res := f.state(); res.Message != "Pod "+p.Name+" is being deleted, so kube creates it again once it's gone" || f.jobState().Runs != 1 {
					t.Fatalf("result = %+v with state %+v, want the old Pod after 1 run", res, f.jobState())
				}
				f.reconcile()
				again := *old
				again.DeletionTimestamp, again.UID, again.Status = nil, "uid-again", PodStatus{Phase: "Pending"}
				f.reconcile(&again)
			}
			if st := f.jobState(); st.Runs != 2 || len(f.r.day.starts) != 2 {
				t.Errorf("runs = %d with %d runs in the last day, want 2 and 2: the second head's and the next one on the first head", st.Runs, len(f.r.day.starts))
			}
		})
	}
}

func TestFollowsTheOldPodWhenTheBranchMovesBack(t *testing.T) {
	f := newFixture(t, "")
	f.r.MaxRunsPerDay = 10
	head := f.b.Spec.Head
	p := f.start()
	p.Status = PodStatus{Phase: "Pending", InitContainerStatuses: []ContainerStatus{
		{Name: "prepare", State: terminated(&Terminated{Reason: "Completed"})},
		{Name: "agent", State: ContainerState{Running: &struct{}{}}},
	}}
	f.reconcile(p)
	f.newHead("one\nnext\n")
	f.reconcile(f.start())

	t.Log("The branch moves back while kube deletes the first head's Pod, whose run already counted.")
	f.b.Spec.Head = head
	now := time.Now()
	p.DeletionTimestamp = &now
	f.reconcile(p)
	if st := f.jobState(); st.Pod != p.Name || st.Runs != 2 || len(f.r.day.starts) != 2 {
		t.Fatalf("state = %+v with %d runs in the last day, want the old Pod after 2 runs", st, len(f.r.day.starts))
	}

	t.Log("Once the Pod is gone, kube creates it again, and its agent is the third run.")
	f.reconcile()
	again := *p
	again.DeletionTimestamp, again.UID, again.Status = nil, "uid-again", PodStatus{Phase: "Pending"}
	f.reconcile(&again)
	if st := f.jobState(); st.Runs != 3 || len(f.r.day.starts) != 3 {
		t.Errorf("state = %+v with %d runs in the last day, want 3 runs", st, len(f.r.day.starts))
	}
}

func TestWaitsForTwoPollsWhenTheBranchMoved(t *testing.T) {
	for _, tc := range []struct {
		poll, say string
		wait      time.Duration
	}{
		{"10s", "a minute", time.Minute},
		{"45s", "2 minutes", 90 * time.Second},
		{"5m", "10 minutes", 10 * time.Minute},
	} {
		t.Run(tc.poll, func(t *testing.T) {
			f := newFixture(t, "")
			f.poll = tc.poll
			head := f.b.Spec.Head
			p := f.start()
			rec := f.reconcile(movedPod(p, head, time.Now().Add(-tc.wait/2)))
			want := "waiting up to " + tc.say + " for a run on the new commits: c/x no longer points to " + head
			if res := f.state(); res.State != gitk8s.Running || res.Message != want || len(kube.Owned[Pod](rec)) != 1 {
				t.Fatalf("result = %+v, want Running in the same Pod", res)
			}
			if d := rec.RequeueAfter(); d <= tc.wait/2-time.Second || d > tc.wait/2 {
				t.Errorf("RequeueAfter = %v, want about %v", d, tc.wait/2)
			}

			t.Log("A branch that moved and moved back between two polls has the same head after the wait, so the check fetches it again.")
			rec = f.reconcile(movedPod(p, head, time.Now().Add(-tc.wait)))
			if pods := kube.Owned[Pod](rec); len(pods) != 2 || f.jobState().Attempt != 2 || f.jobState().Pod != pods[1].Name {
				t.Errorf("state = %+v with %d owned Pods, want attempt 2 in a new Pod", f.jobState(), len(pods))
			}
		})
	}
}

func TestPreparesTheSourceAgainOnADeployDuringTheWait(t *testing.T) {
	f := newFixture(t, "")
	f.r.MaxRunsPerDay = 10
	p := f.start()
	f.reconcile(movedPod(p, f.b.Spec.Head, time.Now()))

	t.Log("The Pod's agent didn't run, so a deploy ends the wait, and the check prepares the source again in a new Pod, which counts as a run.")
	f.r.Model = "composer-3"
	rec := f.reconcile(p)
	pods := kube.Owned[Pod](rec)
	if st := f.jobState(); len(pods) != 1 || pods[0].Name == p.Name || st.Pod != pods[0].Name || st.Attempt != 2 || st.Runs != 1 || len(f.r.day.starts) != 1 {
		t.Errorf("state = %+v with %d owned Pods and %d runs in the last day, want attempt 2 as run 1 in a new Pod", st, len(pods), len(f.r.day.starts))
	}
}

func TestLimitsRunsPerBranchWithABrokenState(t *testing.T) {
	for _, tc := range []struct {
		name, state string
		runs, pods  int
	}{
		{"negative runs", `{"runs":-5}`, 1, 1},
		{"state that doesn't decode", `{"runs":9,"pod":"rev`, 9, 0},
		{"no state", "", 9, 0},
	} {
		t.Run(tc.name, func(t *testing.T) {
			f := newFixture(t, "")
			one := int32(1)
			f.b.Spec.Merge.MaxAgentRuns = &one
			p := f.start()
			f.reconcile(finished(p, f.serve(review(Fail), p.UID)))
			res := f.state()
			res.Outputs["state"], res.Outputs["runs"] = tc.state, "9"
			if tc.state == "" {
				delete(res.Outputs, "state")
			}
			f.newHead("one\nnext\n")
			rec := f.reconcile()
			if pods := kube.Owned[Pod](rec); f.state().State != gitk8s.Running || f.jobState().Runs != tc.runs || len(pods) != tc.pods {
				t.Errorf("result = %+v with %d owned Pods, want Running after %d runs with %d Pods", f.state(), len(pods), tc.runs, tc.pods)
			}
		})
	}
	t.Run("negative runs in a run in progress", func(t *testing.T) {
		f := newFixture(t, "")
		p := f.start()
		state, _ := JobState{Runs: -5, Pod: p.Name, Attempt: 1}.MarshalText()
		f.state().Outputs["state"] = string(state)
		f.reconcile(p)
		if st := f.jobState(); st.Pod != p.Name || st.Runs != 0 {
			t.Errorf("state = %+v, want the run in Pod %s after 0 runs", st, p.Name)
		}
	})
}

func TestCountsARunOnceWhenAReconcileReadsAnOldResult(t *testing.T) {
	for _, tc := range []struct {
		name string
		runs int
	}{{"first run", 0}, {"run after another head's", 1}} {
		t.Run(tc.name, func(t *testing.T) {
			f := newFixture(t, "")
			f.r.MaxRunsPerDay = 10
			if tc.runs > 0 {
				p := f.start()
				f.reconcile(finished(p, f.serve(review(Fail), p.UID)))
				f.newHead("one\nnext\n")
			}
			old := f.state()
			p := f.start()

			t.Log("Creating the Pod can run the next reconcile before the result that the last one wrote reaches the cache, so that reconcile follows the Pod, whose run counted once.")
			f.b.Status.Checks.Result = old
			f.reconcile(p)
			if st := f.jobState(); st.Pod != p.Name || st.Runs != tc.runs+1 || len(f.r.day.starts) != tc.runs+1 {
				t.Errorf("state = %+v with %d runs in the last day, want Pod %s after %d runs", st, len(f.r.day.starts), p.Name, tc.runs+1)
			}
		})
	}
}

func TestCountsAGivenBackRunOnceWhenTheBranchMovesBack(t *testing.T) {
	f := newFixture(t, "")
	f.r.MaxRunsPerDay = 10
	head := f.b.Spec.Head
	p := f.start()
	f.reconcile(movedPod(p, head, time.Now()))
	f.b.Spec.Head = f.base
	f.reconcile()
	if res := f.state(); res.State != gitk8s.Passed || f.jobState().Runs != 0 {
		t.Fatalf("result = %+v, want Passed after 0 runs on a head without changes", res)
	}

	t.Log("The branch moves back while the first head's Pod still exists, and that Pod's run was given back, so the source is prepared again as run 1.")
	f.b.Spec.Head = head
	rec := f.reconcile(movedPod(p, head, time.Now().Add(-2*movedWait)))
	if st, pods := f.jobState(), kube.Owned[Pod](rec); st.Runs != 1 || st.Attempt != 2 || len(pods) != 2 || st.Pod != pods[1].Name || len(f.r.day.starts) != 1 {
		t.Errorf("state = %+v with %d owned Pods and %d runs in the last day, want attempt 2 as run 1 in a new Pod", st, len(pods), len(f.r.day.starts))
	}
}

func TestCountsAPodAgainAfterARestart(t *testing.T) {
	t.Run("Pod without its state", func(t *testing.T) {
		f := newFixture(t, "")
		f.r.MaxRunsPerDay = 10
		old := f.state()
		p := f.start()

		t.Log("kube creates a Pod before it writes the state that counts the Pod's run, so a program that stops in between leaves a Pod that no state counts.")
		f.b.Status.Checks.Result = old
		f.r.day = window{}
		f.reconcile(p)
		if st := f.jobState(); st.Pod != p.Name || st.Runs != 1 || len(f.r.day.starts) != 1 {
			t.Errorf("state = %+v with %d runs in the last day, want Pod %s after 1 run", st, len(f.r.day.starts), p.Name)
		}
	})
	t.Run("moved Pod whose run was given back", func(t *testing.T) {
		f := newFixture(t, "")
		f.r.MaxRunsPerDay = 10
		head := f.b.Spec.Head
		p := f.start()
		f.reconcile(movedPod(p, head, time.Now()))
		f.newHead("one\nnext\n")
		f.start()

		t.Log("After a restart, the branch moves back while the first head's Pod still exists. That Pod's run counts again and is given back again, so the second head's run still counts.")
		f.r.day = window{}
		f.b.Spec.Head = head
		f.reconcile(movedPod(p, head, time.Now().Add(-2*movedWait)))
		if st := f.jobState(); st.Runs != 2 || st.Attempt != 2 {
			t.Errorf("state = %+v, want attempt 2 as run 2", st)
		}
	})
}

package agent

import (
	"encoding/json"
	"math"
	"reflect"
	"slices"
	"strings"
	"testing"

	"github.com/imjasonh/playground/kube"
)

// runJob reconciles a controller that runs job for the fixture's branch,
// with pods in the cluster.
func (f *fixture) runJob(job *Job, st *JobState, pods ...*Pod) (JobStatus, *kube.Recorder) {
	f.t.Helper()
	world := make([]any, len(pods))
	for i, p := range pods {
		world[i] = p
	}
	ctx, rec := kube.Fake(f.t.Context(), f.b, world...)
	return f.r.RunJob(ctx, job, st), rec
}

func TestRunsAJob(t *testing.T) {
	f := newFixture(t, "s3cret")
	repo, _ := f.srv.Repository("app")
	main := f.base
	job := &Job{
		Name: "app-c-x", Namespace: "default", URL: repo.Spec.URL, Credentials: repo.Spec.SecretRef,
		Checkout: Checkout{Branch: "c/x", Head: f.b.Spec.Head, Parent: "main", Base: main},
		Task:     Task{Instructions: "Fix the change.", Edit: true},
		Tools:    []string{"read", "edit"},
		Image:    "registry.example.com/agent-runner:fix",
		MaxRuns:  1,
	}
	st := &JobState{}
	s, rec := f.runJob(job, st)
	pods := kube.Owned[Pod](rec)
	if s.Done || len(pods) != 1 || *st != (JobState{Runs: 1, Pod: pods[0].Name, Attempt: 1}) || s.Message != "started Pod "+pods[0].Name {
		t.Fatalf("RunJob = %+v with state %+v and %d Pods, want a started Pod", s, st, len(pods))
	}
	p := pods[0]
	for _, c := range slices.Concat(p.Spec.InitContainers[1:], p.Spec.Containers) {
		if c.Image != job.Image {
			t.Errorf("container %s runs %s, want the job's image", c.Name, c.Image)
		}
	}
	env := map[string]string{}
	var secrets []string
	for _, e := range p.Spec.InitContainers[0].Env {
		if e.ValueFrom != nil {
			secrets = append(secrets, e.ValueFrom.SecretKeyRef.Name+"/"+e.ValueFrom.SecretKeyRef.Key)
		}
		env[e.Name] = e.Value
	}
	if env["URL"] != repo.Spec.URL || env["HEAD"] != job.Checkout.Head || env["BASE"] != main {
		t.Errorf("prepare's environment = %v, want the job's commits", env)
	}
	if want := []string{"app-creds/username", "app-creds/password", "cursor-api-key/api-key"}; !slices.Equal(secrets, want) {
		t.Errorf("prepare reads Secrets %v, want %v", secrets, want)
	}
	var task podTask
	for _, e := range p.Spec.InitContainers[1].Env {
		if e.Name == "AGENT_TASK" {
			if err := json.Unmarshal([]byte(e.Value), &task); err != nil {
				t.Fatal(err)
			}
		}
	}
	if !slices.Equal(task.Tools, job.Tools) || !task.Edit || task.Instructions != job.Task.Instructions || task.Head != job.Checkout.Head || task.Base != main {
		t.Errorf("AGENT_TASK = %+v, want the job's task, tools, and commits", task)
	}

	t.Log("RunJob follows the Pod until it serves the agent's result.")
	p.Namespace = "default"
	p.UID = "uid-" + p.Name
	digest := f.serve(review(Pass, File{Path: "a.txt", Mode: "100644", Content: []byte("merged\n")}), p.UID)
	s, rec = f.runJob(job, st, finished(p, digest))
	if !s.Done || s.Result == nil || len(s.Result.Files) != 1 || s.Message != "The change adds DO NOT MERGE at a.txt:2." || rec.RequeueAfter() != 0 {
		t.Fatalf("RunJob = %+v and RequeueAfter = %v, want the agent's result, with the requeue left to the caller", s, rec.RequeueAfter())
	}

	t.Log("A job for another head starts a new run, unless the job used all of its runs.")
	job.Checkout.Head = main
	s, rec = f.runJob(job, st)
	if s.Done || len(kube.Owned[Pod](rec)) != 0 || s.Message != "not starting the agent: the job used all 1 of its runs" || *st != (JobState{Runs: 1}) {
		t.Errorf("RunJob = %+v with state %+v, want no new run", s, st)
	}

	t.Log("A job that isn't valid fails without a Pod.")
	job.Tools = []string{"shell"}
	s, rec = f.runJob(job, &JobState{})
	if !s.Done || s.Result != nil || len(kube.Owned[Pod](rec)) != 0 || !strings.HasPrefix(s.Message, `can't run the agent: agents can't have the "shell" tool`) {
		t.Errorf("RunJob = %+v, want a failure without a Pod", s)
	}
}

// reviewJob is a job that reviews the fixture's branch.
func (f *fixture) reviewJob() *Job {
	repo, _ := f.srv.Repository("app")
	return &Job{
		Name: "app-c-x", Namespace: "default", URL: repo.Spec.URL,
		Checkout: Checkout{Branch: "c/x", Head: f.b.Spec.Head, Parent: "main", Base: f.base},
		Task:     Task{Instructions: "Review the change."},
	}
}

// startJob runs job, expects it to start a Pod, and returns the Pod as the
// API server would hold it.
func (f *fixture) startJob(job *Job, st *JobState) *Pod {
	f.t.Helper()
	_, rec := f.runJob(job, st)
	pods := kube.Owned[Pod](rec)
	if len(pods) != 1 {
		f.t.Fatalf("owned Pods = %d, want 1", len(pods))
	}
	p := pods[0]
	p.Namespace = "default"
	p.UID = "uid-" + p.Name
	return p
}

func TestCountsAJobsPodThatsCreatedAgain(t *testing.T) {
	f := newFixture(t, "")
	job := f.reviewJob()
	job.MaxRuns = 2
	st := &JobState{}
	p := f.startJob(job, st)
	for i, uid := range []string{"uid-1", "uid-2"} {
		p.UID = uid
		s, _ := f.runJob(job, st, p)
		if want := (JobState{Runs: i + 1, Pod: p.Name, Attempt: 1, UID: uid}); s.Done || *st != want {
			t.Fatalf("RunJob = %+v with state %+v, want %+v", s, st, want)
		}
	}
	gone := *st
	if s, rec := f.runJob(job, &gone); !s.Done || s.Result != nil || len(kube.Owned[Pod](rec)) != 0 || s.Message != "Pod "+p.Name+" was deleted, but the job used all 2 of its runs" {
		t.Errorf("RunJob = %+v, want the run to end at the job's limit without the Pod", s)
	}
	p.UID = "uid-3"
	if s, _ := f.runJob(job, st, p); !s.Done || s.Result != nil || s.Message != "Pod "+p.Name+" was deleted and created again, but the job used all 2 of its runs" {
		t.Errorf("RunJob = %+v, want the run to end at the job's limit", s)
	}
}

func TestRestartsAJobsRunWhenAFlagChanges(t *testing.T) {
	f := newFixture(t, "")
	job := f.reviewJob()
	job.MaxRuns = 1
	st := &JobState{}
	p := f.startJob(job, st)
	f.runJob(job, st, p)

	t.Log("Another -agent-image starts the run again in a new Pod, which isn't another run.")
	f.r.Image = "registry.example.com/agent-runner:new"
	s, rec := f.runJob(job, st, p)
	pods := kube.Owned[Pod](rec)
	if s.Done || len(pods) != 1 || pods[0].Name == p.Name || *st != (JobState{Runs: 1, Pod: pods[0].Name, Attempt: 1}) || s.Message != "started Pod "+pods[0].Name {
		t.Fatalf("RunJob = %+v with state %+v and %d Pods, want run 1 in a new Pod", s, st, len(pods))
	}
	q := pods[0]
	q.Namespace, q.UID = "default", "uid-"+q.Name

	t.Log("Neither MaxRuns nor empty Tools changes the job.")
	job.MaxRuns, job.Tools = 2, []string{}
	s, rec = f.runJob(job, st, q)
	if pods := kube.Owned[Pod](rec); s.Done || len(pods) != 1 || pods[0].Name != q.Name || st.Runs != 1 {
		t.Fatalf("RunJob = %+v with state %+v, want the same run in the same Pod", s, st)
	}

	t.Log("Another image in the job is another job, so it starts a new run.")
	job.Image = "registry.example.com/agent-runner:fix"
	s, rec = f.runJob(job, st, q)
	if pods := kube.Owned[Pod](rec); s.Done || len(pods) != 1 || pods[0].Name == q.Name || st.Runs != 2 {
		t.Errorf("RunJob = %+v with state %+v, want run 2 in a new Pod", s, st)
	}
}

func TestGivesBackAJobsRunOncePerPodWhenTheBranchMoved(t *testing.T) {
	f := newFixture(t, "")
	job := f.reviewJob()
	st := &JobState{Runs: 1}
	p := f.startJob(job, st)
	p.Status = PodStatus{Phase: "Failed", InitContainerStatuses: []ContainerStatus{
		{Name: "prepare", State: terminated(&Terminated{ExitCode: movedStatus, Message: "c/x no longer points to " + job.Checkout.Head})},
	}}
	for _, uid := range []string{p.UID, p.UID, "uid-again"} {
		p.UID = uid
		if s, _ := f.runJob(job, st, p); s.Done || *st != (JobState{Runs: 1, Pod: p.Name, Attempt: 1, UID: uid, Refunded: uid}) {
			t.Fatalf("RunJob = %+v with state %+v, want the run of Pod UID %s given back once", s, st, uid)
		}
	}
}

func TestKeepsAFinishedJobDone(t *testing.T) {
	f := newFixture(t, "")
	job := f.reviewJob()
	st := &JobState{}
	first := f.startJob(job, st)
	first.Status = PodStatus{Phase: "Failed", InitContainerStatuses: []ContainerStatus{
		{Name: "prepare", State: terminated(&Terminated{ExitCode: 128, Message: "fatal: unable to access the repository"})},
	}}
	_, rec := f.runJob(job, st, first)
	pods := kube.Owned[Pod](rec)
	p := pods[len(pods)-1]
	p.Namespace, p.UID = "default", "uid-"+p.Name
	s, _ := f.runJob(job, st, finished(p, f.serve(review(Pass), p.UID)))
	done := JobState{Runs: 1, Pod: p.Name, Attempt: 2, UID: p.UID, Done: true}
	if !s.Done || s.Result == nil || *st != done {
		t.Fatalf("RunJob = %+v with state %+v, want the agent's result and %+v", s, st, done)
	}

	t.Log("Later calls declare no Pod, so neither a deleted Pod nor a deploy runs the agent again.")
	for _, tc := range []struct {
		model string
		pods  []*Pod
	}{
		{f.r.Model, []*Pod{p}},
		{f.r.Model, nil},
		{"composer-3", nil},
	} {
		f.r.Model = tc.model
		s, rec := f.runJob(job, st, tc.pods...)
		if !s.Done || s.Result != nil || s.Failed != nil || s.Message != "the run in Pod "+p.Name+" already finished" || len(kube.Owned[Pod](rec)) != 0 || *st != done {
			t.Fatalf("RunJob = %+v with state %+v, want the run done without its Pod", s, st)
		}
	}

	t.Log("A job for another head starts a new run.")
	job.Checkout.Head = f.base
	s, rec = f.runJob(job, st)
	if pods := kube.Owned[Pod](rec); s.Done || len(pods) != 1 || *st != (JobState{Runs: 2, Pod: pods[0].Name, Attempt: 1}) {
		t.Fatalf("RunJob = %+v with state %+v, want run 2", s, st)
	}

	t.Log("A job that isn't valid ends its run at once, without a Pod to wait for.")
	job.Tools = []string{"shell"}
	s, rec = f.runJob(job, st)
	if !s.Done || len(kube.Owned[Pod](rec)) != 0 || rec.RequeueAfter() != 0 || *st != (JobState{Runs: 2, Done: true}) {
		t.Errorf("RunJob = %+v with state %+v and RequeueAfter = %v, want the run done without a Pod", s, st, rec.RequeueAfter())
	}
}

func TestReportsAJobsResultAgainWithoutDone(t *testing.T) {
	f := newFixture(t, "")
	job := f.reviewJob()
	st := &JobState{}
	p := f.startJob(job, st)
	f.runJob(job, st, p)
	p = finished(p, f.serve(review(Pass), p.UID))
	done := JobState{Runs: 1, Pod: p.Name, Attempt: 1, UID: p.UID, Done: true}

	t.Log("A caller that stores the state without Done, such as when acting on the result failed, gets the result again.")
	for range 2 {
		kept := *st
		kept.Done = false
		s, rec := f.runJob(job, &kept, p)
		if !s.Done || s.Result == nil || len(kube.Owned[Pod](rec)) != 1 || rec.RequeueAfter() != 0 || kept != done {
			t.Fatalf("RunJob = %+v with state %+v and RequeueAfter = %v, want the agent's result again and %+v", s, kept, rec.RequeueAfter(), done)
		}
		*st = kept
	}

	t.Log("Once the caller stores Done, the next call declares no Pod, so kube deletes it.")
	if s, rec := f.runJob(job, st, p); !s.Done || s.Result != nil || len(kube.Owned[Pod](rec)) != 0 || *st != done {
		t.Errorf("RunJob = %+v with state %+v, want the run done without its Pod", s, st)
	}
}

func TestReportsWhatAFailedJobUsed(t *testing.T) {
	f := newFixture(t, "")
	job := f.reviewJob()
	st := &JobState{}
	p := f.startJob(job, st)
	body, _ := json.Marshal(Result{Verdict: Fail, Model: "fake:composer-2.5", Usage: Usage{InputTokens: 9}, Error: "the agent's run ended with status error: rate limited"})
	s, rec := f.runJob(job, st, finished(p, f.serve(body, p.UID)))
	if !s.Done || s.Result != nil || s.Failed == nil || s.Failed.Usage.InputTokens != 9 || rec.RequeueAfter() != 0 ||
		s.Message != "the agent failed in Pod "+p.Name+": the agent's run ended with status error: rate limited" {
		t.Errorf("RunJob = %+v, want a failed run with what the agent used", s)
	}
}

func TestEncodesTheWholeJobState(t *testing.T) {
	var st JobState
	v := reflect.ValueOf(&st).Elem()
	for i := range v.NumField() {
		field, fv := v.Type().Field(i), v.Field(i)
		switch {
		case !field.IsExported():
			t.Fatalf("JobState.%s isn't exported, so MarshalText can't encode it", field.Name)
		case fv.Kind() == reflect.Int:
			fv.SetInt(int64(-1 - i))
		case fv.Kind() == reflect.String:
			fv.SetString("value of " + field.Name)
		case fv.Kind() == reflect.Bool:
			fv.SetBool(true)
		default:
			t.Fatalf("give JobState.%s, a %s, a value in this test", field.Name, fv.Kind())
		}
	}
	text, err := st.MarshalText()
	if err != nil {
		t.Fatal(err)
	}
	var got JobState
	if err := got.UnmarshalText(text); err != nil || got != st {
		t.Errorf("UnmarshalText(%s) = %+v, %v; want %+v", text, got, err, st)
	}

	t.Log("Empty text is the zero state, and other text that isn't a state is an error.")
	if err := got.UnmarshalText(nil); err != nil || got != (JobState{}) {
		t.Errorf("UnmarshalText(nil) = %+v, %v; want the zero state", got, err)
	}
	if err := got.UnmarshalText([]byte("1")); err == nil {
		t.Error("UnmarshalText(1) succeeded")
	}

	t.Log("The largest state, with the longest Pod name that a check's name allows, fits in a 1,024-byte output value.")
	uid := "0b5f4b5e-5c1c-4b8e-9a7e-0123456789ab"
	big := JobState{Runs: math.MinInt, Pod: strings.Repeat("a", 40) + "-0123456789abcdef", Attempt: math.MaxInt, UID: uid, Refunded: uid, Done: true}
	if text, _ := big.MarshalText(); len(text) > 1024 {
		t.Errorf("MarshalText = %d bytes, want at most 1,024", len(text))
	}
}

func TestValidatesJobs(t *testing.T) {
	sha := strings.Repeat("a", 40)
	job := func(change func(*Job)) *Job {
		j := &Job{
			Name: "app-c-x", Namespace: "default", URL: "https://git.example.com/app.git",
			Checkout: Checkout{Branch: "c/x", Head: sha},
			Task:     Task{Instructions: "Fix it.", Edit: true},
		}
		change(j)
		return j
	}
	for _, change := range []func(*Job){
		func(*Job) {},
		func(j *Job) {
			j.Checkout.Head = strings.Repeat("c", 64)
			j.Checkout.Base = sha
			j.Tools = []string{"read", "delete"}
		},
	} {
		if err := job(change).validate(); err != nil {
			t.Errorf("validate = %v, want a valid job", err)
		}
	}
	for _, tc := range []struct {
		name   string
		change func(*Job)
		want   string
	}{
		{"no name", func(j *Job) { j.Name = "" }, "needs a name, a namespace, a repository URL, and a branch"},
		{"no branch", func(j *Job) { j.Checkout.Branch = "" }, "needs a name, a namespace, a repository URL, and a branch"},
		{"short head", func(j *Job) { j.Checkout.Head = "aaaaaaa" }, "must be commit SHAs"},
		{"option head", func(j *Job) { j.Checkout.Head = "--" + sha[2:] }, "must be commit SHAs"},
		{"uppercase base", func(j *Job) { j.Checkout.Base = strings.ToUpper(strings.Repeat("b", 40)) }, "must be commit SHAs"},
		{"no instructions", func(j *Job) { j.Task.Instructions = " \n" }, "needs instructions"},
		{"edit tool", func(j *Job) { j.Task.Edit, j.Tools = false, []string{"read", "edit"} }, "the edit tool needs a task that edits files"},
		{"shell", func(j *Job) { j.Tools = []string{"read", "shell"} }, `agents can't have the "shell" tool, only read, grep, glob, ls, edit, delete`},
	} {
		if err := job(tc.change).validate(); err == nil || !strings.Contains(err.Error(), tc.want) {
			t.Errorf("%s: validate = %v, want %q", tc.name, err, tc.want)
		}
	}
}

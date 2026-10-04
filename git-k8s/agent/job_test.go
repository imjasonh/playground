package agent

import (
	"encoding/json"
	"errors"
	"fmt"
	"maps"
	"os"
	"os/exec"
	"slices"
	"strings"
	"testing"
	"time"

	"github.com/imjasonh/playground/git-k8s/internal/gittest"
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
		Checkout: Checkout{Branch: "c/x", Head: f.b.Spec.Head, Parent: "main", Base: main, Merge: &Ref{Branch: "main", Commit: main}},
		Task:     Task{Instructions: "Merge main into c/x.", Edit: true},
		Tools:    []string{"read", "edit"},
		Image:    "registry.example.com/agent-runner:merge",
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
	if env["URL"] != repo.Spec.URL || env["HEAD"] != job.Checkout.Head || env["BASE"] != main || env["MERGE_BRANCH"] != "main" || env["MERGE_HEAD"] != main {
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
	if !slices.Equal(task.Tools, job.Tools) || !task.Edit || task.Instructions != job.Task.Instructions || task.MergeBranch != "main" || task.MergeHead != main ||
		task.ConflictsFile != "/input/conflicts" || task.MergeLogFile != "/input/merge-log.txt" {
		t.Errorf("AGENT_TASK = %+v, want the job's task, tools, and merge", task)
	}

	t.Log("RunJob follows the Pod until it serves the agent's result.")
	p.Namespace = "default"
	p.UID = "uid-" + p.Name
	digest := f.serve(review(Pass, File{Path: "a.txt", Mode: "100644", Content: []byte("merged\n")}), p.UID)
	s, rec = f.runJob(job, st, finished(p, digest))
	if !s.Done || s.Result == nil || len(s.Result.Files) != 1 || s.Message != "The change adds DO NOT MERGE at a.txt:2." || rec.RequeueAfter() != time.Second {
		t.Fatalf("RunJob = %+v and RequeueAfter = %v, want the agent's result and a reconcile that deletes the Pod", s, rec.RequeueAfter())
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
			j.Checkout.Merge = &Ref{Branch: "main", Commit: sha}
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
		{"merge without base", func(j *Job) { j.Checkout.Merge = &Ref{Branch: "main", Commit: sha} }, "needs a branch, its commit's SHA, and the merge base"},
		{"merge without branch", func(j *Job) { j.Checkout.Base, j.Checkout.Merge = sha, &Ref{Commit: sha} }, "needs a branch, its commit's SHA, and the merge base"},
		{"no instructions", func(j *Job) { j.Task.Instructions = " \n" }, "needs instructions"},
		{"edit tool", func(j *Job) { j.Task.Edit, j.Tools = false, []string{"read", "edit"} }, "the edit tool needs a task that edits files"},
		{"shell", func(j *Job) { j.Tools = []string{"read", "shell"} }, `agents can't have the "shell" tool, only read, grep, glob, ls, edit, delete`},
	} {
		if err := job(tc.change).validate(); err == nil || !strings.Contains(err.Error(), tc.want) {
			t.Errorf("%s: validate = %v, want %q", tc.name, err, tc.want)
		}
	}
}

func TestPrepareScriptMerges(t *testing.T) {
	srv := gittest.NewServer(t, "s3cret")
	w := srv.NewWork(t, "app")
	w.Write("f.txt", "one\ntwo\nthree\n")
	w.Write("k.txt", "keep\n")
	w.Write(".cursorignore", "secret/\n")
	base := w.Commit("base")
	w.Push("main")
	w.Branch("c/x", base)
	w.Write("f.txt", "one\nours\nthree\n")
	w.Git("rm", "-q", "k.txt")
	head := w.Commit("ours")
	w.Push("c/x")
	w.Branch("main", base)
	w.Write("f.txt", "one\ntheirs\nthree\n")
	w.Write("k.txt", "changed\n")
	w.Write("h.txt", "new\n")
	merged := w.Commit("theirs")
	w.Push("main")
	repo, secret := srv.Repository("app")
	data := maps.Clone(secret.Data)
	data["api-key"] = []byte("key-123")

	r := &Runner{Name: "merge", Image: "agent", GitImage: "git", Backend: "fake", Model: "m", Secret: "cursor-api-key", Timeout: time.Minute}
	job := &Job{
		Name: "app-c-x", Namespace: "default", URL: repo.Spec.URL, Credentials: repo.Spec.SecretRef,
		Checkout: Checkout{Branch: "c/x", Head: head, Parent: "main", Base: base, Merge: &Ref{Branch: "main", Commit: merged}},
		Task:     Task{Instructions: "Merge main.", Edit: true},
	}
	dir, out, err := runPrepare(t, r.jobPod(job, 1).Spec.InitContainers[0], data)
	if err != nil {
		t.Fatalf("prepare: %v\n%s", err, out)
	}
	read := func(path string) string {
		t.Helper()
		b, err := os.ReadFile(dir + path)
		if err != nil {
			t.Fatal(err)
		}
		return string(b)
	}
	if got, want := read("/src/f.txt"), fmt.Sprintf("one\n<<<<<<< %s\nours\n||||||| %s\ntwo\n=======\ntheirs\n>>>>>>> %s\nthree\n", head, base, merged); got != want {
		t.Errorf("f.txt =\n%s\nwant\n%s", got, want)
	}
	if got := read("/src/k.txt"); got != "changed\n" {
		t.Errorf("k.txt = %q, want main's change to the file that c/x deleted", got)
	}
	if got := read("/src/h.txt"); got != "new\n" {
		t.Errorf("h.txt = %q, want the file that main added", got)
	}
	if _, err := os.Stat(dir + "/src/.cursorignore"); !os.IsNotExist(err) {
		t.Errorf("the work tree has .cursorignore: %v", err)
	}
	if tree, paths, _ := strings.Cut(read("/input/conflicts"), "\x00"); !isCommit(tree) || paths != "f.txt\x00k.txt\x00" {
		t.Errorf("conflicts = %q and %q, want the merge's tree and f.txt and k.txt", tree, paths)
	}
	if files := read("/input/files"); strings.Count(files, "\x00") != 3 || !strings.Contains(files, "\tk.txt\x00") || !strings.Contains(files, "\th.txt\x00") {
		t.Errorf("files = %q, want the merge's 3 files", files)
	}
	if got := read("/input/changes"); got != "M\x00f.txt\x00D\x00k.txt\x00" {
		t.Errorf("changes = %q, want c/x's change", got)
	}
	if log := strings.Fields(read("/input/merge-log.txt")); len(log) != 2 || !strings.HasPrefix(merged, log[0]) || log[1] != "theirs" {
		t.Errorf("merge-log.txt = %q, want main's commit since the merge base", log)
	}

	t.Log("A merged branch that moved fails with status 3.")
	job.Checkout.Merge.Commit = base
	_, out, err = runPrepare(t, r.jobPod(job, 1).Spec.InitContainers[0], data)
	var exit *exec.ExitError
	if !errors.As(err, &exit) || exit.ExitCode() != movedStatus || !strings.Contains(out, "main no longer points to "+base) {
		t.Errorf("prepare = %v\n%s; want status 3", err, out)
	}
}

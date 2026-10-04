package agent

import (
	"cmp"
	"context"
	"encoding/hex"
	"errors"
	"fmt"
	"slices"
	"strings"
	"time"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/kube"
)

// Job is one agent run on commits of a repository, for a check or a
// controller. Runner.Run builds one from a check's branch.
type Job struct {
	// Name, with the Runner's Name, names the job's Pods. Use the name of
	// the object that the job is for, such as a GitBranch.
	Name string
	// Namespace holds the job's Pods and the Secrets that they read.
	Namespace string
	// URL is the repository that the Pods fetch from.
	URL string
	// Credentials names the Secret that holds the repository's username
	// and password, or is nil if the repository needs none.
	Credentials *gitk8s.SecretRef
	Checkout    Checkout
	Task        Task
	// Tools are the agent's tools: any of read, grep, glob, and ls, and
	// edit and delete if Task.Edit is set. Empty means all that Task
	// allows. None of them runs commands, because the agent's container
	// holds the API key and reaches Cursor's API.
	Tools []string
	// Image runs the runner, if it isn't the Runner's Image.
	Image string
	// MaxRuns is the most runs that RunJob starts for one JobState, or 0
	// for no limit.
	MaxRuns int
}

// Checkout is the commits that a job's agent works on.
type Checkout struct {
	// Branch points to Head. If the Pod finds it elsewhere, the run waits
	// for a Job with the new head.
	Branch string
	Head   string
	// Parent names the branch that Branch lands on.
	Parent string
	// Base is the merge base of Head and Parent's head, or of Head and
	// Merge's commit, or empty if they share no history. The agent reads
	// the change from Base to Head.
	Base string
	// Merge, if set, is a branch of the same repository to merge into
	// Head, and Base can't be empty. The agent's files are then the tree
	// that git merge-tree --write-tree --merge-base=Base writes with
	// merge.conflictStyle=diff3, instead of Head's, so the files that
	// conflict hold conflict markers. A Result's Files change that tree.
	Merge *Ref
}

// Ref is a branch and the commit that it points to.
type Ref struct {
	Branch string
	Commit string
}

// JobState is what RunJob needs to follow a job's run from one call to the
// next. Keep it with the object that the job is for, such as in a check's
// outputs, and pass it to each call.
type JobState struct {
	// Runs counts the runs that RunJob started.
	Runs int
	// Pod names the run's Pod, and Attempt counts its attempts at
	// preparing the source.
	Pod     string
	Attempt int
}

// JobStatus is how a job's run stands.
type JobStatus struct {
	// Done is true once the run finished. Then stop calling RunJob for the
	// run, and kube deletes its Pod.
	Done bool
	// Message says how the run is going, or why it failed.
	Message string
	// Result is the agent's result, when the run finished with one.
	Result *Result
}

// RunJob starts or follows job's run, and reports how it stands. It
// declares the run's Pod with kube.Own, so call it on each reconcile until
// the run is done. A JobState whose Pod was for other commits, another
// task, or other flags starts a new run.
func (r *Runner) RunJob(ctx context.Context, job *Job, st *JobState) JobStatus {
	s := r.runJob(ctx, job, st)
	if s.Done {
		// The caller stops declaring the Pod once the run is done, so kube
		// deletes it on the next reconcile.
		kube.RequeueAfter(ctx, time.Second)
	}
	return s
}

func (r *Runner) runJob(ctx context.Context, job *Job, st *JobState) JobStatus {
	if err := r.validate(); err != nil {
		return JobStatus{Message: fmt.Sprintf("can't start agents: %v", err)}
	}
	x := &run{r: r, job: job, st: st}
	if err := job.validate(); err != nil {
		return x.fail("can't run the agent: %v", err)
	}
	if st.Pod != "" {
		if p := r.jobPod(job, max(st.Attempt, 1)); p.Name == st.Pod {
			st.Attempt = max(st.Attempt, 1)
			return x.follow(ctx, p)
		}
	}
	*st = JobState{Runs: st.Runs}
	if job.MaxRuns > 0 && st.Runs >= job.MaxRuns {
		return JobStatus{Message: fmt.Sprintf("not starting the agent: the job used all %d of its runs", job.MaxRuns)}
	}
	p := r.jobPod(job, 1)
	if n := r.unfinishedPods(ctx, job.Namespace, p.Name); r.MaxPods > 0 && n >= r.MaxPods {
		// Listing the Pods runs this again when one of them finishes.
		kube.RequeueAfter(ctx, time.Minute)
		return JobStatus{Message: fmt.Sprintf("waiting to start a Pod: %d agent Pods are running, and -max-pods is %d", n, r.MaxPods)}
	}
	if wait, ok := r.day.take(time.Now(), r.MaxRunsPerDay); !ok {
		kube.RequeueAfter(ctx, wait)
		return JobStatus{Message: fmt.Sprintf("waiting to start the agent: %d agent runs started in the last 24 hours, the -max-runs-per-day limit", r.MaxRunsPerDay)}
	}
	*st = JobState{Runs: st.Runs + 1, Pod: p.Name, Attempt: 1}
	return x.follow(ctx, p)
}

// readTools read and search files, and editTools change them, so only a
// task that edits gets them.
var (
	readTools = []string{"read", "grep", "glob", "ls"}
	editTools = []string{"edit", "delete"}
)

func (j *Job) validate() error {
	c := j.Checkout
	switch {
	case j.Name == "" || j.Namespace == "" || j.URL == "" || c.Branch == "":
		return errors.New("the job needs a name, a namespace, a repository URL, and a branch")
	case !isCommit(c.Head) || c.Base != "" && !isCommit(c.Base):
		return errors.New("the job's head and merge base must be commit SHAs")
	case c.Merge != nil && (c.Merge.Branch == "" || !isCommit(c.Merge.Commit) || c.Base == ""):
		return errors.New("a merge needs a branch, its commit's SHA, and the merge base")
	case strings.TrimSpace(j.Task.Instructions) == "":
		return errors.New("the job needs instructions")
	}
	for _, tool := range j.Tools {
		switch {
		case slices.Contains(editTools, tool) && !j.Task.Edit:
			return fmt.Errorf("the %s tool needs a task that edits files", tool)
		case !slices.Contains(readTools, tool) && !slices.Contains(editTools, tool):
			return fmt.Errorf("agents can't have the %.40q tool, only %s", tool, strings.Join(slices.Concat(readTools, editTools), ", "))
		}
	}
	return nil
}

// isCommit reports whether s is a full commit SHA, which git can't read as
// an option.
func isCommit(s string) bool {
	_, err := hex.DecodeString(s)
	return (len(s) == 40 || len(s) == 64) && err == nil && s == strings.ToLower(s)
}

// follow declares desired, the run's Pod, and reports how the run stands.
func (x *run) follow(ctx context.Context, desired *Pod) JobStatus {
	st := x.st
	pod := kube.Own(ctx, desired)
	if pod == nil {
		return x.status("started Pod %s", st.Pod)
	}
	s := &pod.Status
	if t := state(s.InitContainerStatuses, "prepare").Terminated; t != nil && t.ExitCode != 0 {
		msg := exitMessage(t)
		switch {
		case t.ExitCode == movedStatus:
			return x.status("waiting for a run on the new commits: %s", msg)
		case st.Attempt < prepareAttempts:
			st.Attempt++
			st.Pod = x.r.jobPod(x.job, st.Attempt).Name
			kube.RequeueAfter(ctx, time.Second)
			return x.status("preparing the source failed, so trying again: %s", msg)
		}
		return x.fail("couldn't prepare the source in %d attempts: %s", prepareAttempts, msg)
	}
	agent := state(s.InitContainerStatuses, "agent")
	t := agent.Terminated
	switch {
	case t != nil && t.ExitCode != 0 && s.Reason == "DeadlineExceeded":
		return x.fail("Pod %s ran out of time before the agent finished: %s", st.Pod, s.Message)
	case t != nil && t.ExitCode != 0:
		return x.fail("the agent failed in Pod %s: %s", st.Pod, exitMessage(t))
	case t == nil && s.Phase == "Failed":
		return x.fail("Pod %s stopped before the agent finished: %s", st.Pod, cmp.Or(s.Message, s.Reason, "no reason given"))
	}
	if t == nil {
		msg, reason := blocked(s)
		switch {
		case slices.Contains(stuck, reason):
			return x.fail("Pod %s can't start: %s", st.Pod, msg)
		case reason != "":
			return x.status("Pod %s can't start: %s", st.Pod, msg)
		}
		if agent.Running != nil {
			return x.status("the agent is running in Pod %s", st.Pod)
		}
		return x.status("Pod %s is %s", st.Pod, cmp.Or(s.Phase, "Pending"))
	}
	digest := strings.TrimSpace(t.Message)
	if !isDigest(digest) {
		return x.fail("the agent in Pod %s finished without reporting its result's digest", st.Pod)
	}
	server := state(s.ContainerStatuses, "result")
	if server.Terminated != nil || s.Phase == "Failed" || s.Phase == "Succeeded" {
		why := cmp.Or(s.Message, s.Reason, "no reason given")
		if t := server.Terminated; t != nil {
			why = exitMessage(t)
		}
		return x.fail("Pod %s stopped before the check fetched the agent's result: %s", st.Pod, why)
	}
	if server.Running == nil || s.PodIP == "" {
		return x.status("waiting for Pod %s to serve the agent's result", st.Pod)
	}
	body, err := x.r.fetch(ctx, s.PodIP, pod.UID)
	if errors.Is(err, errTooBig) {
		return x.fail("the agent's result from Pod %s isn't valid: %v", st.Pod, err)
	}
	if err != nil {
		kube.RequeueAfter(ctx, 5*time.Second)
		return x.status("fetching the agent's result from Pod %s: %v", st.Pod, err)
	}
	res, err := parseResult(body, digest, x.job.Task.Edit)
	if err != nil {
		return x.fail("the agent's result from Pod %s isn't valid: %v", st.Pod, err)
	}
	return JobStatus{Done: true, Message: cmp.Or(res.Reasoning, res.Summary), Result: res}
}

func (x *run) status(format string, args ...any) JobStatus {
	return JobStatus{Message: fmt.Sprintf(format, args...)}
}

// fail finishes the run without a result.
func (x *run) fail(format string, args ...any) JobStatus {
	return JobStatus{Done: true, Message: fmt.Sprintf(format, args...)}
}

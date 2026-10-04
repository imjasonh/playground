package agent

import (
	"cmp"
	"context"
	"encoding/hex"
	"encoding/json"
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
	// Branch points to Head. If the Pod finds it elsewhere, the agent
	// doesn't run, and the run waits for a Job with the new head without
	// counting toward the run limits.
	Branch string
	Head   string
	// Parent names the branch that Branch lands on.
	Parent string
	// Base is the merge base of Head and Parent's head, or empty if they
	// share no history. The agent reads the change from Base to Head.
	Base string
}

// JobState is what RunJob needs to follow a job's run from one call to the
// next. RunJob changes it on each call, so store all of it after each
// call, such as in one of a check's outputs with MarshalText, and pass it
// to the next call.
type JobState struct {
	// Runs counts the runs that RunJob started and didn't give back.
	Runs int `json:"runs,omitempty"`
	// Pod names the run's Pod, and Attempt counts its attempts at
	// preparing the source.
	Pod     string `json:"pod,omitempty"`
	Attempt int    `json:"attempt,omitempty"`
	// UID is the UID of the run's Pod when RunJob last saw it, so RunJob
	// can tell when kube created the Pod again.
	UID string `json:"uid,omitempty"`
	// Refunded is the UID of the run's Pod that found that the branch
	// moved. Its agent didn't run, so RunJob gave back the run, once.
	Refunded string `json:"refunded,omitempty"`
	// Done is true once RunJob reported that the run finished. Later calls
	// for the same job report the run as done again, without its result,
	// and don't declare its Pod. To get the result again from the next
	// call, such as when acting on it failed, store the state with Done
	// set to false.
	Done bool `json:"done,omitempty"`
}

// MarshalText encodes all of the state as one value, which UnmarshalText
// decodes.
func (s JobState) MarshalText() ([]byte, error) { return json.Marshal(jobState(s)) }

// UnmarshalText decodes a state that MarshalText encoded, or the zero
// state from empty text, such as an output that a check hasn't written.
func (s *JobState) UnmarshalText(text []byte) error {
	v := jobState{}
	if len(text) > 0 {
		if err := json.Unmarshal(text, &v); err != nil {
			return fmt.Errorf("decoding an agent's job state: %w", err)
		}
	}
	*s = JobState(v)
	return nil
}

// jobState is JobState without its methods, so json encodes its fields.
type jobState JobState

// JobStatus is how a job's run stands.
type JobStatus struct {
	// Done is true once the run finished. Later calls with the stored state
	// report the run as done until the job changes.
	Done bool
	// Message says how the run is going, or why it failed.
	Message string
	// Result is the agent's result, when the run finished with one.
	Result *Result
	// Failed is the runner's report on a run that failed after the agent
	// started, with the Error and what the agent used, or nil.
	Failed *Result
	// Moved is true when the run waits because a branch moved before the
	// Pod fetched it.
	Moved bool
}

// RunJob starts or follows job's run, and reports how it stands. It
// declares the run's Pod with kube.Own, so call it on each reconcile, with
// the state that the last call left, until the run is done. Then calls
// with the stored state don't declare the Pod, so kube deletes it in the
// next reconcile. RunJob doesn't ask for that reconcile, so call
// kube.RequeueAfter to delete the Pod soon. A JobState whose Pod was for
// another job, such as one with other commits or another task, starts a
// new run. One whose Pod has another spec, such as after a deploy with
// other flags, starts an unfinished run again in a new Pod, which doesn't
// count as another run. If the run's Pod is deleted before the run
// finishes, kube creates it again, which runs the agent again, so RunJob
// counts another run.
func (r *Runner) RunJob(ctx context.Context, job *Job, st *JobState) JobStatus {
	if st.Done && sameJob(r.jobPod(job, max(st.Attempt, 1)).Name, st.Pod) {
		return JobStatus{Done: true, Message: fmt.Sprintf("the run in Pod %s already finished", st.Pod)}
	}
	s := r.runJob(ctx, job, st)
	if s.Done {
		st.Done = true
	}
	return s
}

func (r *Runner) runJob(ctx context.Context, job *Job, st *JobState) JobStatus {
	return (&run{r: r, job: job, st: st}).startOrFollow(ctx)
}

// startOrFollow starts or follows the run, as RunJob does.
func (x *run) startOrFollow(ctx context.Context) JobStatus {
	r, job, st := x.r, x.job, x.st
	if err := r.validate(); err != nil {
		return JobStatus{Message: fmt.Sprintf("can't start agents: %v", err)}
	}
	if err := job.validate(); err != nil {
		// RunJob marks st done, so it can't keep naming another job's Pod.
		*st = JobState{Runs: st.Runs}
		return x.fail("can't run the agent: %v", err)
	}
	if st.Pod != "" {
		p := r.jobPod(job, max(st.Attempt, 1))
		switch {
		case p.Name == st.Pod:
			st.Attempt = max(st.Attempt, 1)
			return x.follow(ctx, p)
		case sameJob(p.Name, st.Pod):
			return x.restart(ctx, p)
		}
	}
	*st = JobState{Runs: st.Runs}
	if why := x.usedAll(); why != "" {
		return JobStatus{Message: "not starting the agent: " + why}
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
	x.started = true
	return x.follow(ctx, p)
}

// restart starts the run again in p, a Pod for the same job and attempt
// with another spec, such as after a deploy with other flags. The agent
// starts over, so the restart takes a place in -max-runs-per-day, but it
// doesn't count toward the job's runs, so a deploy can't stop a run whose
// job has none left.
func (x *run) restart(ctx context.Context, p *Pod) JobStatus {
	if st := x.st; st.Refunded != "" && st.Refunded == st.UID {
		// A new Pod would find that the branch moved, too.
		c := x.job.Checkout
		s := x.status("waiting for a run on the new commits: %s no longer points to %s", c.Branch, c.Head)
		s.Moved = true
		return s
	}
	if wait, ok := x.r.day.take(time.Now(), x.r.MaxRunsPerDay); !ok {
		kube.RequeueAfter(ctx, wait)
		return x.status("waiting to start the agent again: %d agent runs started in the last 24 hours, the -max-runs-per-day limit", x.r.MaxRunsPerDay)
	}
	x.st.Pod, x.st.UID = p.Name, ""
	x.started = true
	return x.follow(ctx, p)
}

// usedAll says why the run can't start another Pod, if it used all the runs
// that it may start. A check's run counts against maxAgentRuns instead of
// the job's MaxRuns.
func (x *run) usedAll() string {
	if x.in != nil {
		if limit := x.in.Spec.Merge.MaxRuns(); x.st.Runs >= limit {
			return fmt.Sprintf("the branch used all %d agent runs that maxAgentRuns allows", limit)
		}
		return ""
	}
	if limit := x.job.MaxRuns; limit > 0 && x.st.Runs >= limit {
		return fmt.Sprintf("the job used all %d of its runs", limit)
	}
	return ""
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
	// kube creates a deleted Pod again, which runs the agent again, so the
	// run declares a Pod that's gone only if it can count another run.
	if st.UID != "" && kube.Get[podPhase](ctx, x.job.Namespace, st.Pod) == nil {
		if why := x.usedAll(); why != "" {
			return x.fail("Pod %s was deleted, but %s", st.Pod, why)
		}
		if x.r.day.full(time.Now(), x.r.MaxRunsPerDay) {
			return x.fail("Pod %s was deleted, but %d agent runs started in the last 24 hours, the -max-runs-per-day limit", st.Pod, x.r.MaxRunsPerDay)
		}
	}
	pod := kube.Own(ctx, desired)
	if pod == nil {
		if st.UID != "" {
			return x.status("creating Pod %s again, because it was deleted", st.Pod)
		}
		// kube creates a Pod right after the reconcile that declares it, so
		// a Pod that an earlier reconcile declared and that doesn't exist
		// means that creating it failed. Get runs this again once the Pod
		// exists.
		if !x.started && kube.Get[podPhase](ctx, x.job.Namespace, st.Pod) == nil {
			return x.status("kube can't create Pod %s: the program's log says why, such as a ResourceQuota or LimitRange that doesn't allow its ephemeral-storage limit of %s", st.Pod, formatSize(x.r.podDisk()))
		}
		return x.status("started Pod %s", st.Pod)
	}
	if pod.UID != st.UID {
		if st.UID != "" {
			if why := x.usedAll(); why != "" {
				return x.fail("Pod %s was deleted and created again, but %s", st.Pod, why)
			}
			if _, ok := x.r.day.take(time.Now(), x.r.MaxRunsPerDay); !ok {
				return x.fail("Pod %s was deleted and created again, but %d agent runs started in the last 24 hours, the -max-runs-per-day limit", st.Pod, x.r.MaxRunsPerDay)
			}
			st.Runs++
		}
		st.UID = pod.UID
	}
	if pod.Deleting() {
		// Deleting a Pod stops its containers, so their exit codes say
		// nothing about the agent.
		return x.status("Pod %s is being deleted, so kube creates it again once it's gone", st.Pod)
	}
	s := &pod.Status
	if s.Phase == "Failed" && s.Reason == "Evicted" {
		return x.fail("Pod %s was evicted: %s", st.Pod, cmp.Or(strings.TrimSpace(s.Message), "no reason given"))
	}
	if t := state(s.InitContainerStatuses, "prepare").Terminated; t != nil && t.ExitCode != 0 {
		msg := exitMessage(t)
		switch {
		case t.ExitCode == movedStatus:
			if st.Refunded != pod.UID {
				st.Refunded = pod.UID
				if x.r.day.giveBack(time.Now(), pod.UID) {
					st.Runs--
				}
			}
			s := x.status("waiting for a run on the new commits: %s", msg)
			s.Moved = true
			return s
		case st.Attempt < prepareAttempts:
			st.Attempt++
			next := x.r.jobPod(x.job, st.Attempt)
			st.Pod, st.UID = next.Name, ""
			// A later reconcile takes a missing Pod to mean that kube
			// couldn't create it, so declare the Pod in this one.
			kube.Own(ctx, next)
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
		msg, reason, since := blocked(s)
		if since.IsZero() {
			since = pod.CreationTimestamp
		}
		wait := stuckAfter - time.Since(since)
		switch {
		case reason == "InvalidImageName":
			return x.fail("Pod %s can't start: %s", st.Pod, msg)
		case slices.Contains(stuck, reason) && wait <= 0:
			return x.fail("Pod %s couldn't start in %d minutes: %s", st.Pod, int(stuckAfter/time.Minute), msg)
		case slices.Contains(stuck, reason):
			kube.RequeueAfter(ctx, wait)
			return x.status("Pod %s can't start: %s", st.Pod, msg)
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
	if res.Error != "" {
		return JobStatus{Done: true, Message: fmt.Sprintf("the agent failed in Pod %s: %s", st.Pod, res.Error), Failed: res}
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

// Package agent runs an AI agent on a branch in a sandboxed Pod, for checks
// that review or change code.
//
// A check calls Runner.Run on each reconcile, and Run declares a Pod for
// each run with kube.Own:
//
//   - The prepare init container fetches the branch with the repository's
//     credentials. It writes the head's files, the change from the merge
//     base, and the commit log to volumes, and copies the Cursor API key
//     from a Secret to a memory volume.
//   - The agent init container runs the runner in runner/, which reads and
//     deletes the key, runs the agent on the files, and writes the agent's
//     result to a volume and the result's SHA-256 digest as its termination
//     message.
//   - The result container serves the result over HTTP to requests that
//     carry the Pod's UID.
//
// Run reads the digest and the UID from the API server, fetches the result
// from the Pod's IP, and checks it against the digest. So the agent's
// containers get no Kubernetes or git credentials, and a result can hold the
// files that the agent changed, which don't fit in a termination message.
// Run turns those files into a fix commit, which the checks framework pushes
// when the check's policy and the branch's maxAutomatedCommits allow.
//
// A controller that isn't a check calls Runner.RunJob with a Job, which
// names the repository, the commits to check out, the task, and the agent's
// tools. Run builds a Job from the check's branch.
package agent

import (
	"cmp"
	"context"
	"errors"
	"flag"
	"fmt"
	"slices"
	"strconv"
	"strings"
	"sync"
	"time"
	"unicode/utf8"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/checks"
	"github.com/imjasonh/playground/git-k8s/internal/git"
	"github.com/imjasonh/playground/kube"
)

// Verdicts that an agent gives.
const (
	Pass = "pass"
	Fail = "fail"
)

// prepareAttempts is how many Pods a run starts when preparing the source
// fails.
const prepareAttempts = 3

// Runner runs agents in Pods for one check. Set Name to the check's name,
// and the other fields with AddFlags.
type Runner struct {
	Name string
	// Image runs the runner in runner/, which runner/Dockerfile builds.
	Image string
	// GitImage fetches the source. It needs git and sh.
	GitImage string
	// Backend is cursor, which runs the agent in the Pod with the Cursor
	// SDK, or fake, which needs no API key, for tests.
	Backend string
	Model   string
	// Secret names the Secret, in each branch's namespace, whose api-key
	// key holds the Cursor API key.
	Secret       string
	RuntimeClass string
	// Timeout is the longest that an agent can run.
	Timeout time.Duration
	// MaxPods is the most of this check's Pods that run at once, or 0 for
	// no limit.
	MaxPods int
	// MaxRunsPerDay is the most runs that the Runner starts in any 24
	// hours, or 0 for no limit.
	MaxRunsPerDay int
	// SourceSize is the most disk space, such as 2Gi, that each of an agent
	// Pod's repository, files, and input can use. Empty means 2Gi.
	SourceSize string

	port int
	day  window
}

// AddFlags registers flags that set the Runner's fields other than Name.
func (r *Runner) AddFlags(fs *flag.FlagSet) {
	fs.StringVar(&r.Image, "agent-image", "", "image that runs the agent, built from agent/runner/Dockerfile (required)")
	fs.StringVar(&r.GitImage, "git-image", "cgr.dev/chainguard/git:latest", "image that fetches the source; it needs git and sh")
	fs.StringVar(&r.Backend, "backend", "cursor", "where the agent runs: cursor, with the Cursor SDK in the Pod, or fake, for tests")
	fs.StringVar(&r.Model, "model", "composer-2.5", "model that the agent uses")
	fs.StringVar(&r.Secret, "api-key-secret", "cursor-api-key", "Secret, in each branch's namespace, whose api-key key holds the Cursor API key")
	fs.StringVar(&r.RuntimeClass, "runtime-class", "", "RuntimeClass for agent Pods, such as gvisor")
	fs.DurationVar(&r.Timeout, "timeout", 15*time.Minute, "longest that an agent can run")
	fs.IntVar(&r.MaxPods, "max-pods", 10, "most agent Pods to run at once, in all namespaces; 0 means no limit")
	fs.IntVar(&r.MaxRunsPerDay, "max-runs-per-day", 100, "most agent runs to start in any 24 hours; 0 means no limit")
	fs.StringVar(&r.SourceSize, "source-size", defaultSourceSize, "most disk space that each of an agent Pod's repository, files, and input can use")
}

func (r *Runner) validate() error {
	switch {
	case r.Image == "":
		return errors.New("set -agent-image to the image that agent/runner/Dockerfile builds")
	case r.Backend != "cursor" && r.Backend != "fake":
		return fmt.Errorf("-backend is %q, but it must be cursor or fake", r.Backend)
	case r.Model == "" || r.GitImage == "" || r.Secret == "" || r.Timeout < time.Second:
		return errors.New("-model, -git-image, -api-key-secret, and -timeout need values")
	case r.sourceBytes() == 0:
		return fmt.Errorf("-source-size is %q, but it must be a size such as 2Gi", r.SourceSize)
	}
	return nil
}

// Task is what an agent does on a branch.
type Task struct {
	// Instructions say what to do. The runner adds the branch, the change,
	// and the answer's format.
	Instructions string
	// Edit lets the agent change files. The files that it changes become a
	// fix commit.
	Edit bool
}

// Run starts or follows the agent's run on the branch's head, and returns
// the verdict for the check to report: Running until the run finishes, and
// then the agent's verdict, with a fix commit when the agent changed files.
// It also returns the agent's result once the run finishes.
//
// Run doesn't return errors, because a check that returns one reports Error
// without outputs, and the outputs count the branch's runs for
// maxAgentRuns. A check that calls Run needs Check.Remote.
func (r *Runner) Run(ctx context.Context, in *checks.Input, task Task) (checks.Verdict, *Result) {
	st := &JobState{}
	prev := in.Previous
	if prev != nil {
		st.Runs, _ = strconv.Atoi(prev.Outputs["runs"])
	}
	x := &run{r: r, in: in, job: r.checkJob(in, task, ""), st: st}
	if err := r.validate(); err != nil {
		return x.running("can't start agents: %v", err), nil
	}
	head := in.Spec.Head
	if prev != nil && prev.State == gitk8s.Running && prev.Commit == head && prev.Outputs["pod"] != "" {
		st.Pod = prev.Outputs["pod"]
		st.Attempt, _ = strconv.Atoi(prev.Outputs["attempt"])
		st.UID = prev.Outputs["podUID"]
		x.job.Checkout.Base = prev.Outputs["base"]
	}
	// A Pod's name covers its spec, so a changed flag or policy starts a
	// new run instead of changing a Pod that can't change.
	if st.Pod == "" || r.jobPod(x.job, max(st.Attempt, 1)).Name != st.Pod {
		*st = JobState{Runs: st.Runs}
		if why := x.usedAll(); why != "" {
			return x.running("not starting the agent: %s", why), nil
		}
		base, err := in.MergeBase(ctx)
		if err != nil {
			kube.RequeueAfter(ctx, 30*time.Second)
			return x.running("finding the merge base: %v", err), nil
		}
		if base == head {
			v := checks.Pass("the branch has no changes against %s", in.Spec.Parent)
			v.Outputs = x.outputs()
			return v, nil
		}
		x.job.Checkout.Base = base
	}
	s := x.startOrFollow(ctx)
	switch {
	case !s.Done:
		return x.running("%s", s.Message), nil
	case s.Result == nil:
		v := checks.Fail("%s", s.Message)
		if s.Failed != nil {
			v.Outputs = usageOutputs(s.Failed)
		}
		return x.done(ctx, v), nil
	}
	return x.verdict(ctx, s.Result)
}

// checkJob is the job for a check's run on the branch's change from base.
func (r *Runner) checkJob(in *checks.Input, task Task, base string) *Job {
	return &Job{
		Name:        in.Meta.Name,
		Namespace:   in.Meta.Namespace,
		URL:         in.Repository.Spec.URL,
		Credentials: in.Repository.Spec.SecretRef,
		Checkout:    Checkout{Branch: in.Spec.Branch, Head: in.Spec.Head, Parent: in.Spec.Parent, Base: base},
		Task:        task,
	}
}

// unfinishedPods counts the Runner's Pods in all namespaces that haven't
// finished, or returns 0 if the Pod named name in namespace ns already
// exists, because that Pod needs no new place.
func (r *Runner) unfinishedPods(ctx context.Context, ns, name string) int {
	if r.MaxPods <= 0 || kube.Get[podPhase](ctx, ns, name) != nil {
		return 0
	}
	n := 0
	for _, p := range kube.List[podPhase](ctx, kube.MatchingLabels(map[string]string{agentLabel: r.Name})) {
		if p.Status.Phase != "Succeeded" && p.Status.Phase != "Failed" {
			n++
		}
	}
	return n
}

// run is one reconcile's view of one run. in is nil for a job that isn't a
// check's.
type run struct {
	r   *Runner
	in  *checks.Input
	job *Job
	st  *JobState
}

// outputs hold what the next reconcile needs to follow the run.
func (x *run) outputs() map[string]string {
	o := map[string]string{"runs": strconv.Itoa(x.st.Runs)}
	if x.st.Pod != "" {
		o["pod"] = x.st.Pod
		o["attempt"] = strconv.Itoa(x.st.Attempt)
		if x.st.UID != "" {
			o["podUID"] = x.st.UID
		}
		if base := x.job.Checkout.Base; base != "" {
			o["base"] = base
		}
	}
	return o
}

func (x *run) running(format string, args ...any) checks.Verdict {
	return checks.Verdict{State: gitk8s.Running, Message: shorten(fmt.Sprintf(format, args...)), Outputs: x.outputs()}
}

// done finishes the run with v.
func (x *run) done(ctx context.Context, v checks.Verdict) checks.Verdict {
	// The next reconcile finds the result final and declares no Pod, so
	// kube deletes it.
	kube.RequeueAfter(ctx, time.Second)
	v.Message = shorten(v.Message)
	if v.Outputs == nil {
		v.Outputs = map[string]string{}
	}
	v.Outputs["runs"] = strconv.Itoa(x.st.Runs)
	v.Outputs["pod"] = x.st.Pod
	return v
}

// maxMessage leaves room in the checks framework's 1,024-byte messages for
// what it appends about a fix.
const maxMessage = 896

// shorten cuts s to at most maxMessage bytes, on a rune boundary.
func shorten(s string) string {
	if len(s) <= maxMessage {
		return s
	}
	i := maxMessage - len("...")
	for i > 0 && !utf8.RuneStart(s[i]) {
		i--
	}
	return s[:i] + "..."
}

// verdict turns a valid result into the check's verdict.
func (x *run) verdict(ctx context.Context, res *Result) (checks.Verdict, *Result) {
	v := checks.Verdict{State: gitk8s.Passed, Message: cmp.Or(res.Reasoning, res.Summary)}
	if res.Verdict == Fail {
		v.State = gitk8s.Failed
	}
	if len(res.Files) > 0 {
		repo, err := x.in.Repo(ctx)
		if err != nil {
			kube.RequeueAfter(ctx, 30*time.Second)
			return x.running("fetching the branch to commit the agent's changes: %v", err), nil
		}
		fix, err := x.commit(ctx, repo, res)
		if err != nil {
			return x.done(ctx, checks.Fail("can't commit the agent's changes: %v", err)), res
		}
		v.Fix = fix
	}
	v.Outputs = usageOutputs(res)
	v.Outputs["summary"] = res.Summary
	return x.done(ctx, v), res
}

// usageOutputs say what a run used.
func usageOutputs(res *Result) map[string]string {
	o := map[string]string{
		"model":            res.Model,
		"inputTokens":      strconv.FormatInt(res.Usage.InputTokens, 10),
		"outputTokens":     strconv.FormatInt(res.Usage.OutputTokens, 10),
		"cacheReadTokens":  strconv.FormatInt(res.Usage.CacheReadTokens, 10),
		"cacheWriteTokens": strconv.FormatInt(res.Usage.CacheWriteTokens, 10),
	}
	if res.CostCents != nil {
		o["costCents"] = strconv.FormatFloat(*res.CostCents, 'f', -1, 64)
	}
	if res.ChargedCents != nil {
		o["chargedCents"] = strconv.FormatFloat(*res.ChargedCents, 'f', -1, 64)
	}
	return o
}

// commit makes a commit on the branch's head with the agent's changes, or
// returns "" if they change nothing.
func (x *run) commit(ctx context.Context, repo *git.Repo, res *Result) (string, error) {
	head := x.in.Spec.Head
	c, err := repo.Commit(ctx, head)
	if err != nil {
		return "", err
	}
	tree, err := ApplyFiles(ctx, repo, c.Tree, res.Files)
	if err != nil || tree == c.Tree {
		return "", err
	}
	paths := make([]string, len(res.Files))
	for i, f := range res.Files {
		paths[i] = f.Path
	}
	msg := fmt.Sprintf("Apply changes from the %s agent\n\n%s\n\n%s\n\n%s: %s\n", x.r.Name, res.Summary, strings.Join(paths, "\n"), git.FixerTrailer, x.r.Name)
	return repo.CommitTree(ctx, tree, []string{head}, msg, x.in.Identity, c.Time)
}

func state(statuses []ContainerStatus, name string) ContainerState {
	for _, s := range statuses {
		if s.Name == name {
			return s.State
		}
	}
	return ContainerState{}
}

func exitMessage(t *Terminated) string {
	return cmp.Or(strings.TrimSpace(t.Message), t.Reason, fmt.Sprintf("exit code %d", t.ExitCode))
}

// starting are the reasons that a container waits while it starts normally.
var starting = []string{"", "PodInitializing", "ContainerCreating"}

// stuck are the reasons that a container waits until someone fixes a
// Secret or an image. A run ends on them instead of holding a -max-pods
// slot until the Pod's deadline. Other reasons, such as
// CreateContainerError, often pass by themselves.
var stuck = []string{"CreateContainerConfigError", "ErrImagePull", "ImagePullBackOff", "InvalidImageName"}

// blocked reports why a container can't start, such as a missing Secret or
// an image that can't be pulled, and the reason that it waits.
func blocked(st *PodStatus) (msg, reason string) {
	for _, s := range slices.Concat(st.InitContainerStatuses, st.ContainerStatuses) {
		if w := s.State.Waiting; w != nil && !slices.Contains(starting, w.Reason) {
			return fmt.Sprintf("container %s is waiting: %s", s.Name, strings.TrimSpace(w.Reason+": "+w.Message)), w.Reason
		}
	}
	return "", ""
}

// window counts the runs that started in the last 24 hours. It's in
// memory, so it starts over when the program restarts.
type window struct {
	mu     sync.Mutex
	starts []time.Time
}

// take records a run that starts at now, unless limit runs started in the
// 24 hours before. Then it returns how long until one of those is older
// than 24 hours. A limit of 0 means no limit.
func (w *window) take(now time.Time, limit int) (time.Duration, bool) {
	if limit <= 0 {
		return 0, true
	}
	w.mu.Lock()
	defer w.mu.Unlock()
	cutoff := now.Add(-24 * time.Hour)
	i := 0
	for i < len(w.starts) && !w.starts[i].After(cutoff) {
		i++
	}
	w.starts = w.starts[i:]
	if len(w.starts) >= limit {
		return w.starts[len(w.starts)-limit].Sub(cutoff), false
	}
	w.starts = append(w.starts, now)
	return 0, true
}

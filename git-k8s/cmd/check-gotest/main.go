// Command check-gotest runs a branch's Go tests in a sandboxed Pod.
//
// For each branch head, the gotest check declares a Pod with kube.Own. An
// init container fetches the head from the repository's copy on the mirror,
// with a token for the mirror that's bound to the Pod, and the test
// container runs go test ./... as a non-root user, with no service account
// token, no privileges, and a read-only root file system. Only that init
// container sees the token for the mirror. The mirror lets the token fetch
// only the branch's repository, and only while the check's running result
// names the Pod and the Pod that has the token's UID carries kube's
// controller label for this check and is Pending, as a Pod is until its
// init containers finish. A NetworkPolicy that the core program owns lets
// the Pods with that label reach only the mirror, the cluster's DNS
// servers, and what the core program's -goproxy and -go-cache-namespace
// allow, so this program needs no permission to change NetworkPolicies. The
// check reports the Pod's result once the test container exits or an init
// container fails, with the end of the test output when the tests fail.
// With -go-cache, test Pods download modules from a go-cache server and
// share build outputs through it; see addGoCache.
//
// kube deletes a Pod when the check stops declaring it: once the check has
// recorded the Pod's result and the kubelet has stopped the Pod, or when the
// branch moves to a new head. Owner references delete the Pods with their
// GitBranch.
package main

import (
	"cmp"
	"context"
	"crypto/sha256"
	"encoding/hex"
	"flag"
	"fmt"
	"io"
	"maps"
	"os"
	"os/exec"
	"slices"
	"strconv"
	"strings"
	"sync"
	"time"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/checks"
	"github.com/imjasonh/playground/git-k8s/internal/git"
	"github.com/imjasonh/playground/git-k8s/internal/images"
	"github.com/imjasonh/playground/kube"
	"github.com/imjasonh/playground/kube/k8s"
)

// Branch is this check's view of a GitBranch.
type Branch struct {
	kube.Object `kube:"apiVersion=git-k8s.imjasonh.com/v1alpha1,kind=GitBranch,plural=gitbranches,scope=Namespaced"`
	Spec        gitk8s.GitBranchSpec `json:"spec"`
	Status      struct {
		Checks struct {
			Result *gitk8s.CheckResult `json:"gotest,omitempty"`
		} `json:"checks,omitzero"`
	} `json:"status,omitzero"`
}

func (b *Branch) Parts() (*kube.ObjectMeta, *gitk8s.GitBranchSpec, **gitk8s.CheckResult) {
	return &b.ObjectMeta, &b.Spec, &b.Status.Checks.Result
}

// queued is a GitBranch's position in its parent's merge queue, which the
// merge controller writes. It declares only the position and the head that
// the merge controller last kept in the queue, so the check sees nothing
// else in the status, including other checks' results, and changes to the
// rest of the status don't run the check again. generate grants list and
// watch on GitBranches for it, which the check already has for Branch.
type queued struct {
	kube.Object `kube:"apiVersion=git-k8s.imjasonh.com/v1alpha1,kind=GitBranch,plural=gitbranches,scope=Namespaced"`
	Status      struct {
		Queued struct {
			Head     string `json:"head"`
			Position int32  `json:"position,omitempty"`
		} `json:"queued,omitzero"`
	} `json:"status,omitzero"`
}

// front reports whether branch k is at the front of its parent's merge
// queue at head. When the base check pushes its merge of the parent to the
// front, the branch counts again once the merge controller keeps it in the
// queue at the merge, moments later.
func front(ctx context.Context, k kube.Key, head string) bool {
	q := kube.Get[queued](ctx, k.Namespace, k.Name)
	return q != nil && q.Status.Queued.Position == 1 && q.Status.Queued.Head == head
}

// turn is a waiting branch's place in line for a test Pod. Only the front
// of a merge queue lands, so a front that waits for a Pod holds up every
// branch behind it, and fronts go first. The rest of each queue waits in
// line with the branches that aren't queued, because the base check merges
// the parent into each of those branches when it reaches the front, which
// runs the tests again, and their positions change at every landing. When
// the fronts of -max-pods or more queues wait at once, they can take every
// place, and the other branches wait until the queues drain, which they do
// because a branch whose tests haven't passed can't join a queue. Fronts,
// and then the other branches, go in the order that they started waiting,
// then by key. Positions and waiting times are in the GitBranch status, so
// a restarted check keeps the order.
type turn struct {
	front  bool
	since  time.Time
	branch kube.Key
}

// before reports whether t comes before u.
func (t turn) before(u turn) bool {
	switch {
	case t.front != u.front:
		return t.front
	case !t.since.Equal(u.since):
		return t.since.Before(u.since)
	}
	return t.branch.String() < u.branch.String()
}

var (
	goImage      = flag.String("go-image", images.Go, "image that runs go test")
	gitImage     = flag.String("git-image", images.Git, "image that fetches the source without -go-cache; it needs git and sh")
	runtimeClass = flag.String("runtime-class", "", "RuntimeClass for test Pods, such as gvisor")
	timeout      = flag.Duration("timeout", 10*time.Minute, "longest a test Pod can run")
	goProxy      = flag.String("goproxy", "off", "GOPROXY for go test; off keeps tests from downloading modules, and other values need the same -goproxy on the core program")
	maxPods      = flag.Int("max-pods", 10, "most test Pods to run at once, in all namespaces; 0 means no limit")
	mirrorURL    = flag.String("mirror", gitk8s.MirrorURL, "base URL of the git-k8s mirror, which test Pods fetch from")
)

// testPodLabels are the labels on every test Pod. generate gives the
// check's own Pods the same app.kubernetes.io/name, so the component label
// is what keeps the check from counting them.
var testPodLabels = map[string]string{"app.kubernetes.io/name": "check-gotest", "app.kubernetes.io/component": "test"}

// mirrorTokenDir holds the fetch container's token for the mirror.
const mirrorTokenDir = "/var/run/secrets/git-k8s"

// podPhase is what the check counts running test Pods by. Declaring only
// the phase means that other changes to Pods don't run the check again. A
// Pod counts until its phase is Succeeded or Failed, once the kubelet has
// stopped it, even though run reports its result before then.
type podPhase struct {
	kube.Object `kube:"apiVersion=v1,kind=Pod,plural=pods,scope=Namespaced"`
	Status      struct {
		Phase string `json:"phase,omitempty"`
	} `json:"status"`
}

// fetchAttempts is how many Pods the check starts for one head when
// fetching the source fails.
const fetchAttempts = 3

// fetchRetryDelay is how long the check waits after the first failed fetch
// before it starts the next Pod. The wait doubles after each failure, so
// that the attempts outlast a restart of the mirror.
const fetchRetryDelay = 30 * time.Second

// declaredFor is how long the check counts a Pod that it declared but its
// cache doesn't show. A Pod that the API server never created stops taking
// a place after that.
const declaredFor = time.Minute

// waitingLayout formats outputs.waiting and outputs.queued as a Kubernetes
// MicroTime, which sorts as a string.
const waitingLayout = "2006-01-02T15:04:05.000000Z07:00"

// gotest is the gotest check. It runs at most -max-pods test Pods at once.
// When a place frees up, the fronts of merge queues get it first, then the
// branch that has waited longest; see turn.
type gotest struct {
	mu sync.Mutex
	// declared holds when this process first declared each test Pod that
	// its cache didn't show yet. Counting them keeps workers that reconcile
	// at the same moment from all taking the last place.
	declared map[kube.Key]time.Time
}

func (g *gotest) check() checks.Check {
	return checks.Check{Name: gitk8s.GoTestCheck, FilesOnly: true, Stale: stopping, Run: g.run}
}

// stopping reports whether the Pod that a final result names hasn't
// stopped yet. run keeps declaring the Pod until it has, because the API
// server deletes a Pod whose phase is Succeeded or Failed at once, but
// waits for the kubelet to stop one that's still running.
func stopping(ctx context.Context, meta *kube.ObjectMeta, _ *gitk8s.GitBranchSpec, previous *gitk8s.CheckResult) bool {
	name := previous.Outputs["pod"]
	if name == "" {
		return false
	}
	p := kube.Get[podPhase](ctx, meta.Namespace, name)
	return p != nil && p.Status.Phase != "Succeeded" && p.Status.Phase != "Failed"
}

func (g *gotest) run(ctx context.Context, in *checks.Input) (checks.Verdict, error) {
	if p := in.Previous; p.Final() && p.Commit == in.Spec.Head {
		// stopping found that the Pod that the result names hasn't stopped,
		// so keep declaring the Pod, and keep the result.
		if pod, err := testPod(in, p.Outputs["pod"]); err == nil {
			kube.Own(ctx, pod)
		}
		return checks.Verdict{State: p.State, Message: p.Message, Outputs: p.Outputs}, nil
	}
	attempt, named := 1, ""
	if p := in.Previous; p != nil && p.Commit == in.Spec.Head && p.State == gitk8s.Running {
		if n, err := strconv.Atoi(p.Outputs["attempt"]); err == nil && n > 0 {
			attempt = n
		}
		named = p.Outputs["pod"]
	}
	name := podName(in.Meta.Name, in.Spec.Head, attempt)
	outputs := map[string]string{"pod": name, "attempt": strconv.Itoa(attempt)}
	running := func(format string, args ...any) checks.Verdict {
		return checks.Verdict{State: gitk8s.Running, Message: fmt.Sprintf(format, args...), Outputs: outputs}
	}
	// take counts the Pod from the moment that it lets the branch start it,
	// so build the Pod first, and one that can't be built takes no place.
	p, err := testPod(in, name)
	if err != nil {
		return checks.Verdict{}, err
	}
	since := time.Now().UTC().Truncate(time.Microsecond)
	if pod, t, ok := waiting(in.Previous, in.Spec.Head, "waiting", "queued"); ok && pod == name {
		since = t
	}
	if !g.take(ctx, in.Meta.Key(), in.Spec.Head, kube.Key{Namespace: in.Meta.Namespace, Name: name}, since) {
		outputs["waiting"] = since.Format(waitingLayout)
		// Listing the Pods runs this again when one of them finishes. The
		// requeue covers declared Pods that never appear.
		kube.RequeueAfter(ctx, time.Minute)
		return running("waiting to start a Pod: -max-pods is %d, and the fronts of merge queues start first, then branches that have waited longer", *maxPods), nil
	}
	if named != name {
		// The mirror lets a test Pod fetch only once a running result names
		// it, so the check records the name before it starts the Pod, and
		// outputs.queued keeps the branch's place in line meanwhile.
		outputs["queued"] = since.Format(waitingLayout)
		kube.RequeueAfter(ctx, time.Second)
		return running("starting Pod %s", name), nil
	}
	pod := kube.Own(ctx, p)
	if pod == nil {
		// outputs.queued keeps the branch's place in line until the Pod
		// exists. Other branches count only outputs.waiting, so a Pod that
		// the API server refuses stops holding a place after declaredFor.
		outputs["queued"] = since.Format(waitingLayout)
		// kube creates the Pod after run returns, and retries with backoff
		// when it can't, for example because an admission policy denies it.
		if err := kube.LastError(ctx); err != nil {
			return running("starting Pod %s; the last try failed: %v", name, err), nil
		}
		return running("starting Pod %s", name), nil
	}
	switch outcome(pod) {
	case "Succeeded":
		// Once the kubelet stops the Pod, a reconcile finds this result
		// final and declares no Pod, so kube deletes it.
		kube.RequeueAfter(ctx, time.Second)
		v := checks.Pass("go test passed in Pod %s", name)
		v.Outputs = map[string]string{"pod": name}
		return v, nil
	case "Failed":
		msg, finished, code := terminated(pod.Status.InitContainerStatuses, "fetch")
		// A new Pod can't install the GOCACHEPROG program either.
		failed := code != 0 && code != installStatus
		delay := fetchRetryDelay << (attempt - 1)
		if wait := delay - time.Since(finished); failed && attempt < fetchAttempts && wait > 0 {
			// The failed Pod stays declared while the check waits, because
			// its finish time says when to try again.
			kube.RequeueAfter(ctx, wait)
			return running("fetching the source failed, so trying again at %s UTC: %s", finished.Add(delay).UTC().Format(time.TimeOnly), msg), nil
		}
		kube.RequeueAfter(ctx, time.Second)
		if failed {
			if attempt < fetchAttempts {
				outputs["attempt"] = strconv.Itoa(attempt + 1)
				outputs["pod"] = podName(in.Meta.Name, in.Spec.Head, attempt+1)
				return running("fetching the source failed, so trying again: %s", msg), nil
			}
			v := checks.Fail("couldn't fetch the source in %d attempts: %s", fetchAttempts, msg)
			v.Outputs = map[string]string{"pod": name}
			return v, nil
		}
		msg, _, _ = terminated(pod.Status.ContainerStatuses, "test")
		if m, failed := goCacheFailure(pod); failed {
			msg = m
		}
		out := tail(cmp.Or(msg, pod.Status.Message, pod.Status.Reason), 900)
		v := checks.Fail("go test failed in Pod %s: %s", name, out)
		if strings.Contains(out, "lookup disabled by GOPROXY=off") {
			v = checks.Fail("go test couldn't download modules in Pod %s, because -goproxy is off; vendor the dependencies, or set -goproxy: %s", name, out)
		}
		v.Outputs = map[string]string{"pod": name}
		return v, nil
	}
	return running("Pod %s is %s", name, cmp.Or(pod.Status.Phase, "Pending")), nil
}

// take reports whether branch b can run its test Pod pod at head. It can if
// the Pod exists or b declared it moments ago, or if a place is free for it
// after the waiting branches whose turns come first, where b started
// waiting at since. take counts a Pod that it lets b start until the cache
// shows the Pod.
func (g *gotest) take(ctx context.Context, b kube.Key, head string, pod kube.Key, since time.Time) bool {
	if *maxPods <= 0 {
		return true
	}
	g.mu.Lock()
	defer g.mu.Unlock()
	if g.declared == nil {
		g.declared = map[kube.Key]time.Time{}
	}
	if kube.Get[podPhase](ctx, pod.Namespace, pod.Name) != nil {
		delete(g.declared, pod)
		return true
	}
	now := time.Now()
	if t, ok := g.declared[pod]; ok && now.Sub(t) < declaredFor {
		return true
	}
	seen := map[kube.Key]bool{}
	free := *maxPods
	for _, p := range kube.List[podPhase](ctx, kube.MatchingLabels(testPodLabels)) {
		seen[p.Key()] = true
		if p.Status.Phase != "Succeeded" && p.Status.Phase != "Failed" {
			free--
		}
	}
	for k, t := range g.declared {
		if seen[k] || now.Sub(t) >= declaredFor {
			delete(g.declared, k)
		}
	}
	free -= len(g.declared)
	if free <= 0 {
		// Turns don't matter without a free place, and reading positions in
		// the queues would run this again each time that one changes. A Pod
		// that finishes runs this again.
		return false
	}
	// Reading the positions runs this again when one changes, so a branch
	// that reaches the front can take a free place before branches that
	// have waited longer take it.
	mine := turn{front: front(ctx, b, head), since: since, branch: b}
	for _, o := range kube.List[Branch](ctx) {
		k, t, ok := waitingFor(ctx, o)
		if _, declared := g.declared[k]; !ok || declared || seen[k] || o.Key() == b {
			continue
		}
		if (turn{front: front(ctx, o.Key(), o.Spec.Head), since: t, branch: o.Key()}).before(mine) {
			free--
		}
	}
	// After a failed read, ctx is canceled and kube creates no Pod, so take
	// mustn't count one.
	if free <= 0 || ctx.Err() != nil {
		return false
	}
	g.declared[pod] = now
	return true
}

// waiting returns the Pod that a result says its branch is waiting to start
// at head, and when the branch started waiting, from the first of keys that
// the result's outputs hold.
func waiting(res *gitk8s.CheckResult, head string, keys ...string) (string, time.Time, bool) {
	if res == nil || res.Commit != head || res.State != gitk8s.Running {
		return "", time.Time{}, false
	}
	for _, k := range keys {
		if t, err := time.Parse(time.RFC3339, res.Outputs[k]); err == nil {
			return res.Outputs["pod"], t, true
		}
	}
	return "", time.Time{}, false
}

// waitingFor returns the Pod that b is waiting to start and when it started
// waiting. It skips branches that the check no longer runs on, including
// branches whose GitRepository is gone, because nothing updates their
// results, and a stale result holds up every branch behind it.
func waitingFor(ctx context.Context, b *Branch) (kube.Key, time.Time, bool) {
	s := &b.Spec
	if b.Deleting() || s.Parent == "" || s.Merge.Check(gitk8s.GoTestCheck) == nil || s.Head == "" || s.ParentHead == "" {
		return kube.Key{}, time.Time{}, false
	}
	pod, since, ok := waiting(b.Status.Checks.Result, s.Head, "waiting")
	if !ok || kube.Get[gitk8s.Repository](ctx, b.Namespace, s.Repository) == nil {
		return kube.Key{}, time.Time{}, false
	}
	return kube.Key{Namespace: b.Namespace, Name: pod}, since, true
}

// podName names the Pod for one attempt at one head of a branch. The check
// Pod policy in config/policy.yaml denies a new Pod unless its name is
// gotest-ID, where ID has no hyphens.
func podName(branch, head string, attempt int) string {
	sum := sha256.Sum256([]byte(fmt.Sprintf("%s\x00%s\x00%d", branch, head, attempt)))
	return "gotest-" + hex.EncodeToString(sum[:8])
}

// outcome returns the phase that the Pod ends in, Succeeded or Failed, as
// soon as its containers show it, or "" until then. With restartPolicy
// Never, an init container that fails fails the Pod, and the test
// container's exit code decides the rest. The kubelet reports a
// container's exit about a second before it sets the Pod's phase, which it
// does only once it has stopped the Pod's sandbox.
func outcome(pod *Pod) string {
	if p := pod.Status.Phase; p == "Succeeded" || p == "Failed" {
		return p
	}
	for _, s := range pod.Status.InitContainerStatuses {
		if t := s.State.Terminated; t != nil && t.ExitCode != 0 {
			return "Failed"
		}
	}
	for _, s := range pod.Status.ContainerStatuses {
		if t := s.State.Terminated; s.Name == "test" && t != nil {
			if t.ExitCode != 0 {
				return "Failed"
			}
			return "Succeeded"
		}
	}
	return ""
}

// terminated returns the message, finish time, and exit code of the named
// container if it exited with an error. The exit code is 0 otherwise.
func terminated(statuses []ContainerStatus, name string) (string, time.Time, int32) {
	for _, s := range statuses {
		if t := s.State.Terminated; s.Name == name && t != nil && t.ExitCode != 0 {
			return cmp.Or(t.Message, t.Reason, fmt.Sprintf("exit code %d", t.ExitCode)), t.FinishedAt, t.ExitCode
		}
	}
	return "", time.Time{}, 0
}

// tail keeps the end of s, where go test prints its summary.
func tail(s string, n int) string {
	if len(s) <= n {
		return s
	}
	return "..." + s[len(s)-n:]
}

// fetchScript runs in the fetch container without -go-cache. It checks out
// the branch at HEAD, or exits with status 3 if the branch moved, which the
// next head's Pod takes care of. The repository goes in a directory that
// the container creates, because git refuses to use one that another user
// owns, such as the root of an emptyDir volume. The token goes in git's
// environment, not in the repository's config, which the test container
// can read. The git image has no cat, so the shell reads the token, which
// has no newline.
const fetchScript = `set -eu
token=
IFS= read -r token < "$TOKEN_FILE" || [ -n "$token" ]
export GIT_CONFIG_COUNT=1 GIT_CONFIG_KEY_0=http.extraHeader GIT_CONFIG_VALUE_0="Authorization: Bearer $token"
git init -q /src/repo
cd /src/repo
git fetch -q --depth=1 --end-of-options "$URL" "refs/heads/$BRANCH"
if [ "$(git rev-parse FETCH_HEAD)" != "$HEAD" ]; then
  echo "$BRANCH no longer points to $HEAD" >&2
  exit 3
fi
git checkout -q --detach FETCH_HEAD
`

// installStatus is the exit status of a fetch container that couldn't
// install the GOCACHEPROG program. Neither git nor fetchScript exits with
// it.
const installStatus = 4

// fetchSource is the fetch container's command with -go-cache. It runs in
// check-gotest's own image, which must have git but may have no shell, and
// does what fetchScript does in -dir, including exiting with status 3 if
// the branch moved. Before it fetches, -install copies this binary to a
// path for build and the test container to run as GOCACHEPROG. That spares
// the Pod an init container, which the kubelet starts about a second after
// the one before it exits.
func fetchSource(args []string, stderr io.Writer) int {
	flags := flag.NewFlagSet("fetch", flag.ContinueOnError)
	flags.SetOutput(stderr)
	dir := flags.String("dir", "", "directory to check out the head in, which must not exist")
	install := flags.String("install", "", "copy this binary to `path` before fetching")
	if err := flags.Parse(args); err != nil {
		return 2
	}
	if *install != "" {
		if err := installSelf(*install); err != nil {
			fmt.Fprintln(stderr, "can't install the GOCACHEPROG program:", err)
			return installStatus
		}
	}
	fail := func(err error) int {
		fmt.Fprintln(stderr, err)
		return 1
	}
	token, err := os.ReadFile(os.Getenv("TOKEN_FILE"))
	if err != nil {
		return fail(err)
	}
	env := append(os.Environ(), "GIT_CONFIG_COUNT=1", "GIT_CONFIG_KEY_0=http.extraHeader",
		"GIT_CONFIG_VALUE_0=Authorization: Bearer "+strings.TrimSpace(string(token)))
	git := func(args ...string) (string, error) {
		cmd := exec.Command("git", append([]string{"-C", *dir}, args...)...)
		cmd.Env = env
		cmd.Stderr = stderr
		out, err := cmd.Output()
		if err != nil {
			return "", fmt.Errorf("git %s: %w", args[0], err)
		}
		return strings.TrimSpace(string(out)), nil
	}
	if err := os.Mkdir(*dir, 0o755); err != nil {
		return fail(err)
	}
	if _, err := git("init", "-q"); err != nil {
		return fail(err)
	}
	branch, head := os.Getenv("BRANCH"), os.Getenv("HEAD")
	if _, err := git("fetch", "-q", "--depth=1", "--end-of-options", os.Getenv("URL"), "refs/heads/"+branch); err != nil {
		return fail(err)
	}
	fetched, err := git("rev-parse", "FETCH_HEAD")
	if err != nil {
		return fail(err)
	}
	if fetched != head {
		fmt.Fprintf(stderr, "%s no longer points to %s\n", branch, head)
		return 3
	}
	if _, err := git("checkout", "-q", "--detach", "FETCH_HEAD"); err != nil {
		return fail(err)
	}
	return 0
}

func testPod(in *checks.Input, name string) (*Pod, error) {
	yes, no := true, false
	user := int64(65532)
	deadline := int64(timeout.Seconds())
	// The kubelet sends a deleted Pod's containers SIGTERM and kills them
	// when the grace period ends. It raises a shorter grace period to 2
	// seconds. A container's first process ignores SIGTERM unless it handles
	// the signal, as the shell that runs fetchScript doesn't, and the Pod
	// counts toward -max-pods until its containers stop.
	grace := int64(2)
	expiry := int64(tokenSeconds)
	restricted := &SecurityContext{
		AllowPrivilegeEscalation: &no,
		ReadOnlyRootFilesystem:   &yes,
		Capabilities:             &Capabilities{Drop: []string{"ALL"}},
	}
	mounts := []VolumeMount{{Name: "src", MountPath: "/src"}, {Name: "tmp", MountPath: "/tmp"}}
	fetchEnv := []EnvVar{
		{Name: "URL", Value: strings.TrimSuffix(*mirrorURL, "/") + gitk8s.MirrorPath(in.Repository.Namespace, in.Repository.Name)},
		{Name: "BRANCH", Value: in.Spec.Branch},
		{Name: "HEAD", Value: in.Spec.Head},
		{Name: "TOKEN_FILE", Value: mirrorTokenDir + "/token"},
		{Name: "HOME", Value: "/tmp"},
		{Name: "GIT_TERMINAL_PROMPT", Value: "0"},
		{Name: "GIT_ALLOW_PROTOCOL", Value: git.AllowProtocol},
	}
	p := &Pod{Object: kube.Meta(name, maps.Clone(testPodLabels))}
	p.Spec = PodSpec{
		RestartPolicy:                 "Never",
		AutomountServiceAccountToken:  &no,
		ActiveDeadlineSeconds:         &deadline,
		TerminationGracePeriodSeconds: &grace,
		RuntimeClassName:              *runtimeClass,
		SecurityContext: &PodSecurityContext{
			RunAsNonRoot:   &yes,
			RunAsUser:      &user,
			RunAsGroup:     &user,
			FSGroup:        &user,
			SeccompProfile: &SeccompProfile{Type: "RuntimeDefault"},
		},
		Volumes: []Volume{
			{Name: "src", EmptyDir: &EmptyDir{}},
			{Name: "tmp", EmptyDir: &EmptyDir{}},
			{Name: "mirror-token", Projected: &Projected{Sources: []VolumeProjection{{
				ServiceAccountToken: &ServiceAccountTokenProjection{Audience: gitk8s.MirrorAudience, ExpirationSeconds: &expiry, Path: "token"},
			}}}},
		},
		InitContainers: []Container{{
			Name:                     "fetch",
			Image:                    *gitImage,
			ImagePullPolicy:          images.PullPolicy(*gitImage),
			Command:                  []string{"sh", "-c", fetchScript},
			Env:                      fetchEnv,
			VolumeMounts:             append(slices.Clip(mounts), VolumeMount{Name: "mirror-token", MountPath: mirrorTokenDir, ReadOnly: true}),
			SecurityContext:          restricted,
			TerminationMessagePolicy: "FallbackToLogsOnError",
		}},
		Containers: []Container{{
			Name:            "test",
			Image:           *goImage,
			ImagePullPolicy: images.PullPolicy(*goImage),
			Command:         []string{"go", "test", "./..."},
			WorkingDir:      "/src/repo",
			Env: []EnvVar{
				{Name: "HOME", Value: "/tmp"},
				{Name: "GOCACHE", Value: "/tmp/go-build"},
				{Name: "GOPATH", Value: "/tmp/go"},
				{Name: "GOTOOLCHAIN", Value: "local"},
				{Name: "GOPROXY", Value: *goProxy},
				{Name: "CGO_ENABLED", Value: "0"},
			},
			VolumeMounts:             mounts,
			SecurityContext:          restricted,
			TerminationMessagePolicy: "FallbackToLogsOnError",
			Resources: &Resources{
				Requests: map[string]k8s.Quantity{"cpu": "100m", "memory": "256Mi"},
				Limits:   map[string]k8s.Quantity{"memory": "2Gi"},
			},
		}},
	}
	if err := addGoCache(p, in); err != nil {
		return nil, err
	}
	return p, nil
}

func main() {
	if len(os.Args) > 1 {
		switch os.Args[1] {
		case "cacheprog":
			os.Exit(cacheprog(os.Args[2:], os.Stdin, os.Stdout, os.Stderr))
		case "fetch":
			os.Exit(fetchSource(os.Args[2:], os.Stderr))
		}
	}
	checks.Main[Branch](new(gotest).check())
}

// Command check-gotest runs a branch's Go tests in a sandboxed Pod.
//
// For each branch head, the gotest check declares a Pod with kube.Own. An
// init container fetches the head from the repository, and the test
// container runs go test ./... as a non-root user, with no service account
// token, no privileges, and a read-only root file system. Only the init
// container sees the repository's credentials. The check reports the Pod's
// result, with the end of the test output when the tests fail.
//
// kube deletes a Pod when the check stops declaring it, which happens after
// the check records the Pod's result and when the branch moves to a new
// head. Owner references delete the Pods with their GitBranch.
package main

import (
	"cmp"
	"context"
	"crypto/sha256"
	"encoding/hex"
	"flag"
	"fmt"
	"maps"
	"strconv"
	"strings"
	"time"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/checks"
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

var (
	goImage      = flag.String("go-image", "cgr.dev/chainguard/go:latest", "image that runs go test")
	gitImage     = flag.String("git-image", "cgr.dev/chainguard/git:latest", "image that fetches the source; it needs git and sh")
	runtimeClass = flag.String("runtime-class", "", "RuntimeClass for test Pods, such as gvisor")
	timeout      = flag.Duration("timeout", 10*time.Minute, "longest a test Pod can run")
	goProxy      = flag.String("goproxy", "off", "GOPROXY for go test; off keeps tests from downloading modules")
	maxPods      = flag.Int("max-pods", 10, "most test Pods to run at once, in all namespaces; 0 means no limit")
)

// testPodLabels are the labels on every test Pod.
var testPodLabels = map[string]string{"app.kubernetes.io/name": "check-gotest"}

// podPhase is what the check counts running test Pods by. Declaring only
// the phase means that other changes to Pods don't run the check again.
type podPhase struct {
	kube.Object `kube:"apiVersion=v1,kind=Pod,plural=pods,scope=Namespaced"`
	Status      struct {
		Phase string `json:"phase,omitempty"`
	} `json:"status"`
}

// fetchAttempts is how many Pods the check starts for one head when
// fetching the source fails.
const fetchAttempts = 3

var check = checks.Check{Name: "gotest", Run: run}

func run(ctx context.Context, in *checks.Input) (checks.Verdict, error) {
	attempt := 1
	if p := in.Previous; p != nil && p.Commit == in.Spec.Head && p.State == gitk8s.Running {
		if n, err := strconv.Atoi(p.Outputs["attempt"]); err == nil && n > 0 {
			attempt = n
		}
	}
	name := podName(in.Meta.Name, in.Spec.Head, attempt)
	outputs := map[string]string{"pod": name, "attempt": strconv.Itoa(attempt)}
	running := func(format string, args ...any) checks.Verdict {
		return checks.Verdict{State: gitk8s.Running, Message: fmt.Sprintf(format, args...), Outputs: outputs}
	}
	if n := unfinishedPods(ctx, in.Meta.Namespace, name); *maxPods > 0 && n >= *maxPods {
		// Listing the Pods runs this again when one of them finishes.
		kube.RequeueAfter(ctx, time.Minute)
		return running("waiting to start a Pod: %d test Pods are running, and -max-pods is %d", n, *maxPods), nil
	}
	pod := kube.Own(ctx, testPod(in, name))
	if pod == nil {
		// kube creates the Pod after run returns, and retries with backoff
		// when it can't, for example because an admission policy denies it.
		if err := kube.LastError(ctx); err != nil {
			return running("starting Pod %s; the last try failed: %v", name, err), nil
		}
		return running("starting Pod %s", name), nil
	}
	switch pod.Status.Phase {
	case "Succeeded":
		// The next reconcile finds this result final and declares no Pod,
		// so kube deletes it.
		kube.RequeueAfter(ctx, time.Second)
		v := checks.Pass("go test passed in Pod %s", name)
		v.Outputs = map[string]string{"pod": name}
		return v, nil
	case "Failed":
		kube.RequeueAfter(ctx, time.Second)
		if msg, failed := terminated(pod.Status.InitContainerStatuses, "fetch"); failed {
			if attempt < fetchAttempts {
				outputs["attempt"] = strconv.Itoa(attempt + 1)
				return running("fetching the source failed, so trying again: %s", msg), nil
			}
			return checks.Fail("couldn't fetch the source in %d attempts: %s", fetchAttempts, msg), nil
		}
		msg, _ := terminated(pod.Status.ContainerStatuses, "test")
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

// unfinishedPods counts the test Pods in all namespaces that haven't
// finished, or returns 0 if the Pod named name in namespace ns already
// exists, because that Pod needs no new place.
func unfinishedPods(ctx context.Context, ns, name string) int {
	if *maxPods <= 0 || kube.Get[podPhase](ctx, ns, name) != nil {
		return 0
	}
	n := 0
	for _, p := range kube.List[podPhase](ctx, kube.MatchingLabels(testPodLabels)) {
		if p.Status.Phase != "Succeeded" && p.Status.Phase != "Failed" {
			n++
		}
	}
	return n
}

// podName names the Pod for one attempt at one head of a branch. The check
// Pod policy in config/policy.yaml denies a new Pod unless its name is
// gotest-ID, where ID has no hyphens.
func podName(branch, head string, attempt int) string {
	sum := sha256.Sum256([]byte(fmt.Sprintf("%s\x00%s\x00%d", branch, head, attempt)))
	return "gotest-" + hex.EncodeToString(sum[:8])
}

// terminated returns the message of the named container if it exited with
// an error.
func terminated(statuses []ContainerStatus, name string) (string, bool) {
	for _, s := range statuses {
		if t := s.State.Terminated; s.Name == name && t != nil && t.ExitCode != 0 {
			return cmp.Or(t.Message, t.Reason, fmt.Sprintf("exit code %d", t.ExitCode)), true
		}
	}
	return "", false
}

// tail keeps the end of s, where go test prints its summary.
func tail(s string, n int) string {
	if len(s) <= n {
		return s
	}
	return "..." + s[len(s)-n:]
}

// fetchScript runs in the init container. It checks out the branch at HEAD,
// or exits with status 3 if the branch moved, which the next head's Pod
// takes care of. The repository goes in a directory that the container
// creates, because git refuses to use one that another user owns, such as
// the root of an emptyDir volume.
const fetchScript = `set -eu
git init -q /src/repo
cd /src/repo
if [ -n "${GIT_PASSWORD:-}" ]; then
  git config credential.helper '!f() { echo "username=${GIT_USERNAME:-git}"; echo "password=${GIT_PASSWORD}"; }; f'
fi
git fetch -q --depth=1 "$URL" "refs/heads/$BRANCH"
if [ "$(git rev-parse FETCH_HEAD)" != "$HEAD" ]; then
  echo "$BRANCH no longer points to $HEAD" >&2
  exit 3
fi
git checkout -q --detach FETCH_HEAD
`

func testPod(in *checks.Input, name string) *Pod {
	yes, no := true, false
	user := int64(65532)
	deadline := int64(timeout.Seconds())
	restricted := &SecurityContext{
		AllowPrivilegeEscalation: &no,
		ReadOnlyRootFilesystem:   &yes,
		Capabilities:             &Capabilities{Drop: []string{"ALL"}},
	}
	mounts := []VolumeMount{{Name: "src", MountPath: "/src"}, {Name: "tmp", MountPath: "/tmp"}}
	fetchEnv := []EnvVar{
		{Name: "URL", Value: in.Repository.Spec.URL},
		{Name: "BRANCH", Value: in.Spec.Branch},
		{Name: "HEAD", Value: in.Spec.Head},
		{Name: "HOME", Value: "/tmp"},
		{Name: "GIT_TERMINAL_PROMPT", Value: "0"},
	}
	if ref := in.Repository.Spec.SecretRef; ref != nil {
		fetchEnv = append(fetchEnv,
			EnvVar{Name: "GIT_USERNAME", ValueFrom: &EnvVarSource{SecretKeyRef: &SecretKeySelector{Name: ref.Name, Key: "username", Optional: &yes}}},
			EnvVar{Name: "GIT_PASSWORD", ValueFrom: &EnvVarSource{SecretKeyRef: &SecretKeySelector{Name: ref.Name, Key: "password"}}},
		)
	}
	p := &Pod{Object: kube.Meta(name, maps.Clone(testPodLabels))}
	p.Spec = PodSpec{
		RestartPolicy:                "Never",
		AutomountServiceAccountToken: &no,
		ActiveDeadlineSeconds:        &deadline,
		RuntimeClassName:             *runtimeClass,
		SecurityContext: &PodSecurityContext{
			RunAsNonRoot:   &yes,
			RunAsUser:      &user,
			RunAsGroup:     &user,
			FSGroup:        &user,
			SeccompProfile: &SeccompProfile{Type: "RuntimeDefault"},
		},
		Volumes: []Volume{{Name: "src", EmptyDir: &EmptyDir{}}, {Name: "tmp", EmptyDir: &EmptyDir{}}},
		InitContainers: []Container{{
			Name:                     "fetch",
			Image:                    *gitImage,
			ImagePullPolicy:          "IfNotPresent",
			Command:                  []string{"sh", "-c", fetchScript},
			Env:                      fetchEnv,
			VolumeMounts:             mounts,
			SecurityContext:          restricted,
			TerminationMessagePolicy: "FallbackToLogsOnError",
		}},
		Containers: []Container{{
			Name:            "test",
			Image:           *goImage,
			ImagePullPolicy: "IfNotPresent",
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
	return p
}

func main() { checks.Main[Branch](check) }

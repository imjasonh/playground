// Command check-gotest runs a branch's Go tests in a sandboxed Pod.
//
// For each branch head, the gotest check declares a Pod with kube.Own. An
// init container fetches the head from the repository's copy on the mirror,
// with a token that's bound to the Pod, and the test container runs go test
// ./... as a non-root user, with no service account token, no privileges,
// and a read-only root file system. Only the init container sees the token,
// and the mirror lets it fetch only the branch's repository, only while a
// running result names the Pod. A NetworkPolicy lets the Pod reach only the
// mirror and DNS. The check reports the Pod's result, with the end of the
// test output when the tests fail.
//
// kube deletes a Pod and its NetworkPolicy when the check stops declaring
// them, which happens after the check records the Pod's result and when the
// branch moves to a new head. Owner references delete them with their
// GitBranch.
package main

import (
	"cmp"
	"context"
	"crypto/sha256"
	"encoding/hex"
	"flag"
	"fmt"
	"maps"
	"slices"
	"strconv"
	"strings"
	"time"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/checks"
	"github.com/imjasonh/playground/git-k8s/internal/git"
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
	mirrorURL    = flag.String("mirror", gitk8s.MirrorURL, "base URL of the git-k8s mirror, which test Pods fetch from")
	mirrorNS     = flag.String("mirror-namespace", "git-k8s", "namespace of the git-k8s core program, which serves the mirror")
)

// testPodLabels are the labels on every test Pod.
var testPodLabels = map[string]string{"app.kubernetes.io/name": "check-gotest"}

// podLabel holds a test Pod's name, so that the Pod's NetworkPolicy selects
// only that Pod.
const podLabel = gitk8s.Group + "/test-pod"

// mirrorPort is the port of the core program's Pods that serves the mirror.
// A NetworkPolicy matches the port of the Pod that a Service sends a
// connection to, not the Service's port.
const mirrorPort = 8081

// tokenDir holds the init container's token for the mirror.
const tokenDir = "/var/run/secrets/git-k8s"

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

// fetchRetryDelay is how long the check waits after the first failed fetch
// before it starts the next Pod. The wait doubles after each failure, so
// that the attempts outlast a restart of the mirror.
const fetchRetryDelay = 30 * time.Second

var check = checks.Check{Name: "gotest", Run: run}

func run(ctx context.Context, in *checks.Input) (checks.Verdict, error) {
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
	if n := unfinishedPods(ctx, in.Meta.Namespace, name); *maxPods > 0 && n >= *maxPods {
		// Listing the Pods runs this again when one of them finishes.
		kube.RequeueAfter(ctx, time.Minute)
		return running("waiting to start a Pod: %d test Pods are running, and -max-pods is %d", n, *maxPods), nil
	}
	if named != name {
		// The mirror lets a test Pod fetch only once a running result names
		// it, so the check records the name before it starts the Pod.
		kube.RequeueAfter(ctx, time.Second)
		return running("starting Pod %s", name), nil
	}
	// kube applies these in order, so the policy exists before the Pod.
	kube.Own(ctx, testPolicy(name))
	pod := kube.Own(ctx, testPod(in, name))
	if pod == nil {
		return running("started Pod %s", name), nil
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
		msg, finished, failed := terminated(pod.Status.InitContainerStatuses, "fetch")
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
			return checks.Fail("couldn't fetch the source in %d attempts: %s", fetchAttempts, msg), nil
		}
		msg, _, _ = terminated(pod.Status.ContainerStatuses, "test")
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

// podName names the Pod for one attempt at one head of a branch.
func podName(branch, head string, attempt int) string {
	sum := sha256.Sum256([]byte(fmt.Sprintf("%s\x00%s\x00%d", branch, head, attempt)))
	return "gotest-" + hex.EncodeToString(sum[:8])
}

// terminated returns the message and finish time of the named container if
// it exited with an error.
func terminated(statuses []ContainerStatus, name string) (string, time.Time, bool) {
	for _, s := range statuses {
		if t := s.State.Terminated; s.Name == name && t != nil && t.ExitCode != 0 {
			return cmp.Or(t.Message, t.Reason, fmt.Sprintf("exit code %d", t.ExitCode)), t.FinishedAt, true
		}
	}
	return "", time.Time{}, false
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
// the root of an emptyDir volume. The token goes in git's environment, not
// in the repository's config, which the test container can read. The git
// image has no cat, so the shell reads the token, which has no newline.
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

// testPolicy declares the NetworkPolicy of the test Pod named name. It lets
// the Pod reach only the mirror and DNS, and with -goproxy, ports 80 and
// 443 anywhere, and lets nothing reach the Pod.
func testPolicy(name string) *NetworkPolicy {
	p := &NetworkPolicy{Object: kube.Meta(name, maps.Clone(testPodLabels))}
	p.Spec = NetworkPolicySpec{
		PodSelector: LabelSelector{MatchLabels: map[string]string{podLabel: name}},
		PolicyTypes: []string{"Ingress", "Egress"},
		Egress: []NetworkPolicyRule{{
			To: []NetworkPolicyPeer{{
				NamespaceSelector: &LabelSelector{MatchLabels: map[string]string{"kubernetes.io/metadata.name": *mirrorNS}},
				PodSelector:       &LabelSelector{MatchLabels: map[string]string{"app.kubernetes.io/name": "git-k8s"}},
			}},
			Ports: []NetworkPolicyPort{{Protocol: "TCP", Port: mirrorPort}},
		}, {
			Ports: []NetworkPolicyPort{{Protocol: "UDP", Port: 53}, {Protocol: "TCP", Port: 53}},
		}},
	}
	if *goProxy != "off" {
		p.Spec.Egress = append(p.Spec.Egress, NetworkPolicyRule{
			Ports: []NetworkPolicyPort{{Protocol: "TCP", Port: 80}, {Protocol: "TCP", Port: 443}},
		})
	}
	return p
}

func testPod(in *checks.Input, name string) *Pod {
	yes, no := true, false
	user := int64(65532)
	deadline := int64(timeout.Seconds())
	tokenSeconds := int64(600)
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
		{Name: "TOKEN_FILE", Value: tokenDir + "/token"},
		{Name: "HOME", Value: "/tmp"},
		{Name: "GIT_TERMINAL_PROMPT", Value: "0"},
		{Name: "GIT_ALLOW_PROTOCOL", Value: git.AllowProtocol},
	}
	labels := maps.Clone(testPodLabels)
	labels[podLabel] = name
	p := &Pod{Object: kube.Meta(name, labels)}
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
		Volumes: []Volume{
			{Name: "src", EmptyDir: &EmptyDir{}},
			{Name: "tmp", EmptyDir: &EmptyDir{}},
			{Name: "mirror-token", Projected: &Projected{Sources: []VolumeProjection{{
				ServiceAccountToken: &ServiceAccountToken{Audience: gitk8s.MirrorAudience, ExpirationSeconds: &tokenSeconds, Path: "token"},
			}}}},
		},
		InitContainers: []Container{{
			Name:                     "fetch",
			Image:                    *gitImage,
			ImagePullPolicy:          "IfNotPresent",
			Command:                  []string{"sh", "-c", fetchScript},
			Env:                      fetchEnv,
			VolumeMounts:             append(slices.Clip(mounts), VolumeMount{Name: "mirror-token", MountPath: tokenDir, ReadOnly: true}),
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

package agent

import (
	"cmp"
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"math"
	"strconv"
	"time"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/checks"
	"github.com/imjasonh/playground/kube"
	"github.com/imjasonh/playground/kube/k8s"
)

// agentLabel, on each agent Pod, names the check that runs it.
const agentLabel = gitk8s.Group + "/agent"

// Where the agent Pod's volumes hold the source, the agent's input, the API
// key, and the result.
const (
	workTree   = "/src"
	inputDir   = "/input"
	keyFile    = "/key/api-key"
	resultFile = "/result/result.json"
)

// podSlack is how much longer than the agent's timeout a Pod can run. It
// covers pulling images, preparing the source, and waiting for the check
// to fetch the result.
const podSlack = 30 * time.Minute

func (r *Runner) resultPort() int { return cmp.Or(r.port, 8080) }

// podTask is the task that runner/src/task.ts reads from AGENT_TASK.
type podTask struct {
	Backend        string `json:"backend"`
	Model          string `json:"model"`
	Instructions   string `json:"instructions"`
	Edit           bool   `json:"edit"`
	TimeoutSeconds int64  `json:"timeoutSeconds"`
	Branch         string `json:"branch"`
	Parent         string `json:"parent"`
	Head           string `json:"head"`
	Base           string `json:"base"`
	WorkTree       string `json:"workTree"`
	DiffFile       string `json:"diffFile"`
	LogFile        string `json:"logFile"`
	FilesFile      string `json:"filesFile"`
	KeyFile        string `json:"keyFile"`
	ResultFile     string `json:"resultFile"`
	TerminationLog string `json:"terminationLog"`
}

// prepareScript runs in the prepare container. It fetches the branch at
// HEAD, or exits with status 3 if the branch moved, and writes the head's
// files, its index, the change from BASE, the commit log, and the API key
// for the agent container. The git image has no commands but git and sh,
// so the script uses only those and the shell's builtins, and git init's
// templates make .git/info. The repository goes in a directory that git
// init creates, because git refuses to use one that another user owns,
// such as the root of an emptyDir volume. The attributes file makes the
// files match their blobs, so the runner can tell which ones the agent
// changed.
const prepareScript = `set -eu
git init -q "$REPO"
cd "$REPO"
if [ -n "${GIT_PASSWORD:-}" ]; then
  git config credential.helper '!f() { echo "username=${GIT_USERNAME:-git}"; echo "password=${GIT_PASSWORD}"; }; f'
fi
git fetch -q --depth=50 --end-of-options "$URL" "refs/heads/$BRANCH"
if [ "$(git rev-parse FETCH_HEAD)" != "$HEAD" ]; then
  echo "$BRANCH no longer points to $HEAD" >&2
  exit 3
fi
if [ -n "${BASE:-}" ] && ! git cat-file -e "$BASE^{commit}" 2>/dev/null; then
  git fetch -q --unshallow --end-of-options "$URL" "refs/heads/$BRANCH"
fi
printf '* -text -eol -ident -filter -working-tree-encoding\n' >.git/info/attributes
git read-tree "$HEAD"
git checkout-index -a -f --prefix="$WORK_TREE/"
git ls-files -s -z >"$INPUT/files"
from="${BASE:-$(git hash-object -t tree /dev/null)}"
range="$HEAD"
if [ -n "${BASE:-}" ]; then
  range="$BASE..$HEAD"
fi
git -c core.quotePath=false diff --no-color --no-ext-diff --no-textconv "$from" "$HEAD" >"$INPUT/change.diff"
git log --format='%h %s' -n 50 "$range" >"$INPUT/log.txt"
umask 077
printf '%s' "$CURSOR_API_KEY" >"$KEY_FILE"
`

// pod declares the Pod for one attempt at a run on base..head. Its name
// covers the branch, the attempt, and the Pod's spec.
func (r *Runner) pod(in *checks.Input, task Task, base string, attempt int) *Pod {
	yes, no := true, false
	user := int64(65532)
	timeout := max(1, int64(math.Ceil(r.Timeout.Seconds())))
	deadline := timeout + int64(podSlack/time.Second)
	restricted := &SecurityContext{
		AllowPrivilegeEscalation: &no,
		ReadOnlyRootFilesystem:   &yes,
		Capabilities:             &Capabilities{Drop: []string{"ALL"}},
	}
	agentTask, _ := json.Marshal(podTask{
		Backend:        r.Backend,
		Model:          r.Model,
		Instructions:   task.Instructions,
		Edit:           task.Edit,
		TimeoutSeconds: timeout,
		Branch:         in.Spec.Branch,
		Parent:         in.Spec.Parent,
		Head:           in.Spec.Head,
		Base:           base,
		WorkTree:       workTree,
		DiffFile:       inputDir + "/change.diff",
		LogFile:        inputDir + "/log.txt",
		FilesFile:      inputDir + "/files",
		KeyFile:        keyFile,
		ResultFile:     resultFile,
		TerminationLog: "/dev/termination-log",
	})
	prepareEnv := []EnvVar{
		{Name: "URL", Value: in.Repository.Spec.URL},
		{Name: "BRANCH", Value: in.Spec.Branch},
		{Name: "HEAD", Value: in.Spec.Head},
		{Name: "BASE", Value: base},
		{Name: "REPO", Value: "/git/repo"},
		{Name: "WORK_TREE", Value: workTree},
		{Name: "INPUT", Value: inputDir},
		{Name: "KEY_FILE", Value: keyFile},
		{Name: "HOME", Value: "/git"},
		{Name: "GIT_TERMINAL_PROMPT", Value: "0"},
	}
	if ref := in.Repository.Spec.SecretRef; ref != nil {
		prepareEnv = append(prepareEnv,
			EnvVar{Name: "GIT_USERNAME", ValueFrom: &EnvVarSource{SecretKeyRef: &SecretKeySelector{Name: ref.Name, Key: "username", Optional: &yes}}},
			EnvVar{Name: "GIT_PASSWORD", ValueFrom: &EnvVarSource{SecretKeyRef: &SecretKeySelector{Name: ref.Name, Key: "password"}}},
		)
	}
	prepareEnv = append(prepareEnv, EnvVar{Name: "CURSOR_API_KEY", ValueFrom: &EnvVarSource{SecretKeyRef: &SecretKeySelector{Name: r.Secret, Key: "api-key"}}})
	port := r.resultPort()

	p := &Pod{Object: kube.Meta("", map[string]string{"app.kubernetes.io/name": "git-k8s-agent", agentLabel: r.Name})}
	p.Spec = PodSpec{
		RestartPolicy:                "Never",
		AutomountServiceAccountToken: &no,
		EnableServiceLinks:           &no,
		ActiveDeadlineSeconds:        &deadline,
		RuntimeClassName:             r.RuntimeClass,
		SecurityContext: &PodSecurityContext{
			RunAsNonRoot:   &yes,
			RunAsUser:      &user,
			RunAsGroup:     &user,
			FSGroup:        &user,
			SeccompProfile: &SeccompProfile{Type: "RuntimeDefault"},
		},
		Volumes: []Volume{
			{Name: "git", EmptyDir: &EmptyDir{}},
			{Name: "src", EmptyDir: &EmptyDir{}},
			{Name: "input", EmptyDir: &EmptyDir{}},
			{Name: "key", EmptyDir: &EmptyDir{Medium: "Memory", SizeLimit: "1Mi"}},
			{Name: "result", EmptyDir: &EmptyDir{SizeLimit: "64Mi"}},
			{Name: "tmp", EmptyDir: &EmptyDir{}},
		},
		InitContainers: []Container{{
			Name:            "prepare",
			Image:           r.GitImage,
			ImagePullPolicy: "IfNotPresent",
			Command:         []string{"sh", "-c", prepareScript},
			Env:             prepareEnv,
			VolumeMounts: []VolumeMount{
				{Name: "git", MountPath: "/git"},
				{Name: "src", MountPath: "/src"},
				{Name: "input", MountPath: inputDir},
				{Name: "key", MountPath: "/key"},
			},
			SecurityContext:          restricted,
			TerminationMessagePolicy: "FallbackToLogsOnError",
			Resources: &Resources{
				Requests: map[string]k8s.Quantity{"cpu": "100m", "memory": "128Mi"},
				Limits:   map[string]k8s.Quantity{"memory": "1Gi"},
			},
		}, {
			Name:            "agent",
			Image:           r.Image,
			ImagePullPolicy: "IfNotPresent",
			Args:            []string{"run"},
			Env: []EnvVar{
				{Name: "AGENT_TASK", Value: string(agentTask)},
				{Name: "HOME", Value: "/tmp"},
			},
			VolumeMounts: []VolumeMount{
				{Name: "src", MountPath: "/src", ReadOnly: !task.Edit},
				{Name: "input", MountPath: inputDir, ReadOnly: true},
				{Name: "key", MountPath: "/key"},
				{Name: "result", MountPath: "/result"},
				{Name: "tmp", MountPath: "/tmp"},
			},
			SecurityContext:          restricted,
			TerminationMessagePolicy: "FallbackToLogsOnError",
			Resources: &Resources{
				Requests: map[string]k8s.Quantity{"cpu": "100m", "memory": "256Mi"},
				Limits:   map[string]k8s.Quantity{"memory": "2Gi"},
			},
		}},
		Containers: []Container{{
			Name:            "result",
			Image:           r.Image,
			ImagePullPolicy: "IfNotPresent",
			Args:            []string{"serve"},
			Env: []EnvVar{
				{Name: "POD_UID", ValueFrom: &EnvVarSource{FieldRef: &FieldSelector{FieldPath: "metadata.uid"}}},
				{Name: "RESULT_FILE", Value: resultFile},
				{Name: "PORT", Value: strconv.Itoa(port)},
			},
			Ports:                    []ContainerPort{{Name: "result", ContainerPort: int32(port), Protocol: "TCP"}},
			VolumeMounts:             []VolumeMount{{Name: "result", MountPath: "/result", ReadOnly: true}},
			SecurityContext:          restricted,
			TerminationMessagePolicy: "FallbackToLogsOnError",
			Resources: &Resources{
				Requests: map[string]k8s.Quantity{"cpu": "10m", "memory": "32Mi"},
				Limits:   map[string]k8s.Quantity{"memory": "256Mi"},
			},
		}},
	}
	spec, _ := json.Marshal(p.Spec)
	sum := sha256.Sum256(fmt.Appendf(nil, "%s\x00%d\x00%s", in.Meta.Name, attempt, spec))
	p.Name = r.Name + "-" + hex.EncodeToString(sum[:8])
	return p
}

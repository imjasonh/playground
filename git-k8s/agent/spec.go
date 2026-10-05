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
	"github.com/imjasonh/playground/git-k8s/internal/git"
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

// tokenDir holds the prepare container's token for the mirror, which
// expires after tokenSeconds.
const (
	tokenDir     = "/var/run/secrets/git-k8s"
	tokenSeconds = 600
)

// podSlack is how much longer than the agent's timeout a Pod can run. It
// covers pulling images, preparing the source, and waiting for the check
// to fetch the result.
const podSlack = 30 * time.Minute

// defaultSourceSize is the SourceSize of a Runner that doesn't set one.
const defaultSourceSize = "2Gi"

// defaultStorageRequest is the StorageRequest of a Runner that doesn't set
// one.
const defaultStorageRequest = "1Gi"

// The sizes of the agent Pod's volumes other than the source's, and the
// room that the Pod leaves for its containers' logs.
const (
	tmpSize    = 1 << 30
	resultSize = 64 << 20
	logSize    = 256 << 20
)

func (r *Runner) resultPort() int { return cmp.Or(r.port, 8080) }

// sourceBytes is the Runner's SourceSize in bytes, or 0 if it isn't a size.
func (r *Runner) sourceBytes() int64 { return parseSize(cmp.Or(r.SourceSize, defaultSourceSize)) }

// storageBytes is the Runner's StorageRequest in bytes, or 0 if it isn't a
// size.
func (r *Runner) storageBytes() int64 {
	return parseSize(cmp.Or(r.StorageRequest, defaultStorageRequest))
}

// podDisk is each agent Pod's ephemeral-storage limit in bytes.
func (r *Runner) podDisk() int64 { return 3*r.sourceBytes() + tmpSize + resultSize + logSize }

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
	ChangesFile    string `json:"changesFile"`
	KeyFile        string `json:"keyFile"`
	ResultFile     string `json:"resultFile"`
	TerminationLog string `json:"terminationLog"`

	// Only some jobs set these.
	Tools            []string `json:"tools,omitempty"`
	MergeName        string   `json:"mergeName,omitempty"`
	MergeHead        string   `json:"mergeHead,omitempty"`
	ConflictsFile    string   `json:"conflictsFile,omitempty"`
	MergeLogFile     string   `json:"mergeLogFile,omitempty"`
	MergeDiffFile    string   `json:"mergeDiffFile,omitempty"`
	MergeChangesFile string   `json:"mergeChangesFile,omitempty"`
}

// movedStatus is prepareScript's exit status when a branch no longer points
// to the job's commit.
const movedStatus = 3

// prepareScript runs in the prepare container. It fetches the branch at
// HEAD, or exits with status 3 if the branch moved, and writes the head's
// files, its index, the change from BASE, the paths that the change
// touches, the commit log, and the API key, if the Secret holds one, for
// the agent container. With MERGE_HEAD, it also fetches MERGE_REF, or
// exits with status 3 if that no longer contains MERGE_HEAD, and writes the
// files and index of HEAD's merge with MERGE_HEAD instead of the head's,
// the paths that conflict, and the change from BASE to MERGE_HEAD, its
// paths, and its log. It leaves .cursorignore files out of the files and
// index, because Cursor reads them to hide files from the agent. The git
// image has no commands but git and sh, so the script uses only those and
// the shell's builtins, and git init's templates make .git/info. The
// repository goes in a directory that git init creates, because git
// refuses to use one that another user owns, such as the root of an
// emptyDir volume. The attributes file makes the files match their blobs,
// so the runner can tell which ones the agent changed. With TOKEN_FILE, the
// script sends the token in that file, which has no newline, as a bearer
// token from git's environment.
//
// The fetches take the last 50 commits, and fetch the rest of the history
// only when MERGE_HEAD or BASE isn't in them. The merge reads attributes
// from the empty tree instead of the commits, as git.Repo.Merge does, so
// the branch's .gitattributes files can't change it, even with a git that
// reads them from a tree. ATTRIBUTES holds more attributes for the merge,
// which set merge=union for the paths whose conflicts git resolves by
// keeping the lines of both sides.
const prepareScript = `set -eu
if [ -n "${TOKEN_FILE:-}" ]; then
  token=
  IFS= read -r token <"$TOKEN_FILE" || [ -n "$token" ]
  export GIT_CONFIG_COUNT=1 GIT_CONFIG_KEY_0=http.extraHeader GIT_CONFIG_VALUE_0="Authorization: Bearer $token"
fi
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
shallow() {
  [ "$(git rev-parse --is-shallow-repository)" = true ]
}
if [ -n "${MERGE_HEAD:-}" ]; then
  git fetch -q --depth=50 --end-of-options "$URL" "$MERGE_REF"
  contains() {
    git merge-base --is-ancestor --end-of-options "$MERGE_HEAD" FETCH_HEAD 2>/dev/null
  }
  if ! contains && shallow; then
    git fetch -q --unshallow --end-of-options "$URL" "$MERGE_REF"
  fi
  if ! contains; then
    echo "$MERGE_REF no longer contains $MERGE_HEAD" >&2
    exit 3
  fi
fi
if [ -n "${BASE:-}" ] && ! git cat-file -e --end-of-options "$BASE^{commit}" 2>/dev/null && shallow; then
  git fetch -q --unshallow --end-of-options "$URL" "refs/heads/$BRANCH"
fi
printf '* -text -eol -ident -filter -working-tree-encoding\n' >.git/info/attributes
printf '%s' "${ATTRIBUTES:-}" >>.git/info/attributes
tree="$HEAD"
if [ -n "${MERGE_HEAD:-}" ]; then
  empty="$(git hash-object -t tree --stdin </dev/null)"
  merge_tree() {
    git --attr-source="$empty" -c merge.conflictStyle=diff3 merge-tree --write-tree --no-messages --name-only "$@" --merge-base="$BASE" --end-of-options "$HEAD" "$MERGE_HEAD"
  }
  code=0
  merge_tree >.git/merge || code=$?
  [ "$code" -le 1 ] || exit "$code"
  read -r tree <.git/merge
  merge_tree -z >"$INPUT/conflicts" || [ "$?" -eq 1 ]
  git log --format='%h %<(200,trunc)%s' -n 50 --end-of-options "$BASE..$MERGE_HEAD" >"$INPUT/merge-log.txt"
fi
git read-tree --end-of-options "$tree"
git rm -q --cached --ignore-unmatch -- ':(glob)**/.cursorignore'
git checkout-index -a -f --prefix="$WORK_TREE/"
git ls-files -s -z >"$INPUT/files"
from="${BASE:-$(git hash-object -t tree /dev/null)}"
range="$HEAD"
if [ -n "${BASE:-}" ]; then
  range="$BASE..$HEAD"
fi
git -c core.quotePath=false diff --no-color --no-ext-diff --no-textconv --end-of-options "$from" "$HEAD" >"$INPUT/change.diff"
git diff --name-status -z --end-of-options "$from" "$HEAD" >"$INPUT/changes"
git log --format='%h %<(200,trunc)%s' -n 50 --end-of-options "$range" >"$INPUT/log.txt"
if [ -n "${MERGE_HEAD:-}" ]; then
  git -c core.quotePath=false diff --no-color --no-ext-diff --no-textconv --end-of-options "$BASE" "$MERGE_HEAD" >"$INPUT/merge.diff"
  git diff --name-status -z --end-of-options "$BASE" "$MERGE_HEAD" >"$INPUT/merge-changes"
fi
umask 077
printf '%s' "${CURSOR_API_KEY:-}" >"$KEY_FILE"
`

// jobPod declares the Pod for one attempt at job's run. Its name covers
// the job, the attempt, and the Pod's spec.
func (r *Runner) jobPod(job *Job, attempt int) *Pod {
	c := job.Checkout
	yes, no := true, false
	user := int64(65532)
	timeout := max(1, int64(math.Ceil(r.Timeout.Seconds())))
	deadline := timeout + int64(podSlack/time.Second)
	restricted := &SecurityContext{
		AllowPrivilegeEscalation: &no,
		ReadOnlyRootFilesystem:   &yes,
		Capabilities:             &Capabilities{Drop: []string{"ALL"}},
	}
	task := podTask{
		Backend:        r.Backend,
		Model:          r.Model,
		Instructions:   job.Task.Instructions,
		Edit:           job.Task.Edit,
		TimeoutSeconds: timeout,
		Branch:         c.Branch,
		Parent:         c.Parent,
		Head:           c.Head,
		Base:           c.Base,
		WorkTree:       workTree,
		DiffFile:       inputDir + "/change.diff",
		LogFile:        inputDir + "/log.txt",
		FilesFile:      inputDir + "/files",
		ChangesFile:    inputDir + "/changes",
		KeyFile:        keyFile,
		ResultFile:     resultFile,
		TerminationLog: "/dev/termination-log",
		Tools:          job.Tools,
	}
	prepareEnv := []EnvVar{
		{Name: "URL", Value: job.URL},
		{Name: "BRANCH", Value: c.Branch},
		{Name: "HEAD", Value: c.Head},
		{Name: "BASE", Value: c.Base},
		{Name: "REPO", Value: "/git/repo"},
		{Name: "WORK_TREE", Value: workTree},
		{Name: "INPUT", Value: inputDir},
		{Name: "KEY_FILE", Value: keyFile},
		{Name: "HOME", Value: "/git"},
		{Name: "GIT_TERMINAL_PROMPT", Value: "0"},
		{Name: "GIT_ALLOW_PROTOCOL", Value: "http:https:git:ssh"},
	}
	if m := c.Merge; m != nil {
		task.MergeName, task.MergeHead = cmp.Or(m.DisplayName, m.Name), m.Commit
		task.ConflictsFile, task.MergeLogFile = inputDir+"/conflicts", inputDir+"/merge-log.txt"
		task.MergeDiffFile, task.MergeChangesFile = inputDir+"/merge.diff", inputDir+"/merge-changes"
		prepareEnv = append(prepareEnv, EnvVar{Name: "MERGE_REF", Value: m.Name}, EnvVar{Name: "MERGE_HEAD", Value: m.Commit})
		if attributes, _ := git.UnionAttributes(c.Union); attributes != "" {
			prepareEnv = append(prepareEnv, EnvVar{Name: "ATTRIBUTES", Value: attributes})
		}
	}
	agentTask, _ := json.Marshal(task)
	source := cmp.Or(r.SourceSize, defaultSourceSize)
	volumes := []Volume{
		{Name: "git", EmptyDir: &EmptyDir{SizeLimit: source}},
		{Name: "src", EmptyDir: &EmptyDir{SizeLimit: source}},
		{Name: "input", EmptyDir: &EmptyDir{SizeLimit: source}},
		{Name: "key", EmptyDir: &EmptyDir{Medium: "Memory", SizeLimit: "1Mi"}},
		{Name: "result", EmptyDir: &EmptyDir{SizeLimit: formatSize(resultSize)}},
		{Name: "tmp", EmptyDir: &EmptyDir{SizeLimit: formatSize(tmpSize)}},
	}
	prepareMounts := []VolumeMount{
		{Name: "git", MountPath: "/git"},
		{Name: "src", MountPath: "/src"},
		{Name: "input", MountPath: inputDir},
		{Name: "key", MountPath: "/key"},
	}
	if ref := job.Credentials; ref != nil {
		prepareEnv = append(prepareEnv,
			EnvVar{Name: "GIT_USERNAME", ValueFrom: &EnvVarSource{SecretKeyRef: &SecretKeySelector{Name: ref.Name, Key: "username", Optional: &yes}}},
			EnvVar{Name: "GIT_PASSWORD", ValueFrom: &EnvVarSource{SecretKeyRef: &SecretKeySelector{Name: ref.Name, Key: "password"}}},
		)
	}
	if job.Mirror {
		seconds := int64(tokenSeconds)
		volumes = append(volumes, Volume{Name: "mirror-token", Projected: &Projected{Sources: []VolumeProjection{{
			ServiceAccountToken: &ServiceAccountToken{Audience: gitk8s.MirrorAudience, ExpirationSeconds: &seconds, Path: "token"},
		}}}})
		prepareMounts = append(prepareMounts, VolumeMount{Name: "mirror-token", MountPath: tokenDir, ReadOnly: true})
		prepareEnv = append(prepareEnv, EnvVar{Name: "TOKEN_FILE", Value: tokenDir + "/token"})
	}
	// Without the Secret, the runner fails a cursor backend's run and says to
	// check the Secret, instead of the Pod waiting for it until its deadline.
	// The fake backend needs no key.
	prepareEnv = append(prepareEnv, EnvVar{Name: "CURSOR_API_KEY", ValueFrom: &EnvVarSource{SecretKeyRef: &SecretKeySelector{Name: r.Secret, Key: "api-key", Optional: &yes}}})
	port := r.resultPort()
	image := cmp.Or(job.Image, r.Image)
	request := k8s.Quantity(cmp.Or(r.StorageRequest, defaultStorageRequest))
	// The kubelet evicts a Pod whose volumes and logs use more than the
	// Pod's ephemeral-storage limit, which is its init containers' limit, so
	// that limit covers every volume.
	disk := k8s.Quantity(formatSize(r.podDisk()))

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
		Volumes: volumes,
		InitContainers: []Container{{
			Name:                     "prepare",
			Image:                    r.GitImage,
			ImagePullPolicy:          "IfNotPresent",
			Command:                  []string{"sh", "-c", prepareScript},
			Env:                      prepareEnv,
			VolumeMounts:             prepareMounts,
			SecurityContext:          restricted,
			TerminationMessagePolicy: "FallbackToLogsOnError",
			Resources: &Resources{
				Requests: map[string]k8s.Quantity{"cpu": "100m", "memory": "128Mi", "ephemeral-storage": request},
				Limits:   map[string]k8s.Quantity{"memory": "1Gi", "ephemeral-storage": disk},
			},
		}, {
			Name:            "agent",
			Image:           image,
			ImagePullPolicy: "IfNotPresent",
			Args:            []string{"run"},
			Env: []EnvVar{
				{Name: "AGENT_TASK", Value: string(agentTask)},
				{Name: "HOME", Value: "/tmp"},
			},
			VolumeMounts: []VolumeMount{
				{Name: "src", MountPath: "/src", ReadOnly: !job.Task.Edit},
				{Name: "input", MountPath: inputDir, ReadOnly: true},
				{Name: "key", MountPath: "/key"},
				{Name: "result", MountPath: "/result"},
				{Name: "tmp", MountPath: "/tmp"},
			},
			SecurityContext:          restricted,
			TerminationMessagePolicy: "FallbackToLogsOnError",
			Resources: &Resources{
				Requests: map[string]k8s.Quantity{"cpu": "100m", "memory": "256Mi", "ephemeral-storage": request},
				Limits:   map[string]k8s.Quantity{"memory": "2Gi", "ephemeral-storage": disk},
			},
		}},
		Containers: []Container{{
			Name:            "result",
			Image:           image,
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
				Requests: map[string]k8s.Quantity{"cpu": "10m", "memory": "32Mi", "ephemeral-storage": "64Mi"},
				Limits:   map[string]k8s.Quantity{"memory": "256Mi", "ephemeral-storage": "256Mi"},
			},
		}},
	}
	// The name's first half covers the job and the attempt, and its second
	// half covers the spec, so a run can tell a Pod whose spec changed with
	// the Runner's flags from another job's Pod. A job's MaxRuns doesn't
	// change its runs, and nil Tools are the same as none.
	id := *job
	id.MaxRuns = 0
	if len(id.Tools) == 0 {
		id.Tools = nil
	}
	idJSON, _ := json.Marshal(id)
	spec, _ := json.Marshal(p.Spec)
	jobSum := sha256.Sum256(fmt.Appendf(nil, "%d\x00%s", attempt, idJSON))
	specSum := sha256.Sum256(spec)
	p.Name = r.Name + "-" + hex.EncodeToString(jobSum[:4]) + hex.EncodeToString(specSum[:4])
	return p
}

// sameJob reports whether the Pods that jobPod named a and b are for the
// same job and attempt, whatever their specs.
func sameJob(a, b string) bool {
	return len(a) == len(b) && len(a) > 8 && a[:len(a)-8] == b[:len(b)-8]
}

// parseSize returns the bytes in a size such as 2Gi or 500M. It returns 0
// for a size that isn't a positive whole number with a suffix of at most T
// or Ti, and for one so big that adding up the Pod's volumes could
// overflow.
func parseSize(s string) int64 {
	i := 0
	for i < len(s) && '0' <= s[i] && s[i] <= '9' {
		i++
	}
	unit := map[string]int64{"": 1, "k": 1e3, "M": 1e6, "G": 1e9, "T": 1e12, "Ki": 1 << 10, "Mi": 1 << 20, "Gi": 1 << 30, "Ti": 1 << 40}[s[i:]]
	n, err := strconv.ParseInt(s[:i], 10, 64)
	if unit == 0 || err != nil || n <= 0 || n > math.MaxInt64/4/unit {
		return 0
	}
	return n * unit
}

// formatSize writes n bytes as a size in the largest binary unit that
// divides it.
func formatSize(n int64) string {
	units := []string{"", "Ki", "Mi", "Gi", "Ti"}
	i := 0
	for i < len(units)-1 && n%1024 == 0 {
		n /= 1024
		i++
	}
	return strconv.FormatInt(n, 10) + units[i]
}

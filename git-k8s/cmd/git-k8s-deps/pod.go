package main

import (
	"cmp"
	"context"
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"errors"
	"fmt"
	"log/slog"
	"maps"
	"path"
	"slices"
	"strconv"
	"strings"
	"unicode"
	"unicode/utf8"

	"golang.org/x/mod/module"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/agent"
	"github.com/imjasonh/playground/kube"
	"github.com/imjasonh/playground/kube/k8s"
)

// podLabels are the labels on every update Pod.
var podLabels = map[string]string{"app.kubernetes.io/name": "git-k8s-deps"}

// podPhase is what the controller counts unfinished update Pods by.
// Declaring only the phase means that other changes to Pods don't run the
// reconcile again.
type podPhase struct {
	kube.Object `kube:"apiVersion=v1,kind=Pod,plural=pods,scope=Namespaced"`
	Status      struct {
		Phase string `json:"phase,omitempty"`
	} `json:"status"`
}

// Where an update Pod's volumes hold the source, the result, and the
// output of go commands.
const (
	repoDir    = "/src/repo"
	resultFile = "/result/result.json"
	logFile    = "/tmp/update.log"
)

// maxBatch is the most updates that one Pod makes, which keeps its result
// well under agent.FetchResult's limit.
const maxBatch = 10

// allowProtocol is GIT_ALLOW_PROTOCOL for git in update Pods. It keeps a
// repository URL from naming a remote helper, which git runs as a program.
const allowProtocol = "http:https:git:ssh:file"

// prepareScript runs in the prepare container. It checks out the parent at
// HEAD, or exits with status 3 if the parent moved. The attributes file
// makes the files match their blobs, so the go.mod and go.sum files that
// the update container reports differ from the parent's only where go
// changed them. The repository goes in a directory that git init creates,
// because git refuses to use one that another user owns, such as the root
// of an emptyDir volume.
const prepareScript = `set -eu
git init -q "$REPO"
cd "$REPO"
if [ -n "${GIT_PASSWORD:-}" ]; then
  git config credential.helper '!f() { echo "username=${GIT_USERNAME:-git}"; echo "password=${GIT_PASSWORD}"; }; f'
fi
git fetch -q --depth=1 --end-of-options "$URL" "refs/heads/$BRANCH"
if [ "$(git rev-parse FETCH_HEAD)" != "$HEAD" ]; then
  echo "$BRANCH no longer points to $HEAD" >&2
  exit 3
fi
git config --unset credential.helper || true
printf '* -text -eol -ident -filter -working-tree-encoding\n' >.git/info/attributes
git checkout -q --detach FETCH_HEAD
`

// updateScript runs in the update container. UPDATES has a line for each
// update: the module, the version, and the directories of the go.mod files
// to update. For each, the script starts from the parent's files and runs
// go get in each directory. In a module that was tidy, it then runs go mod
// tidy, and in others it adds the checksums that go test needs. It writes
// the go.mod and go.sum files, or the end of go's output, to RESULT_FILE as
// JSON, and the file's SHA-256 digest to TERMINATION_LOG.
//
// The controller writes UPDATES only from module paths, versions, and
// directories that it checked, so none of them holds quotes, spaces, or
// characters that the shell expands.
const updateScript = `set -u
cd "$REPO" || exit 1
printf '{"updates":[' >"$RESULT_FILE" || exit 1
sep=
while read -r module version dirs; do
  [ -n "$module" ] || continue
  git reset -q --hard HEAD && git clean -q -fdx || exit 1
  : >"$LOG_FILE"
  ok=true
  for dir in $dirs; do
    if ! (
      cd "$dir" || exit 1
      tidy=false
      if go mod tidy -diff >/dev/null 2>&1; then tidy=true; fi
      go get "$module@$version" || exit 1
      if [ "$tidy" = true ]; then
        go mod tidy -e
      else
        go list -mod=mod -e -deps -test ./... >/dev/null
      fi
    ) >>"$LOG_FILE" 2>&1; then
      ok=false
      break
    fi
  done
  printf '%s{"module":"%s","version":"%s","ok":%s' "$sep" "$module" "$version" "$ok" >>"$RESULT_FILE"
  sep=,
  if [ "$ok" = true ]; then
    printf ',"files":[' >>"$RESULT_FILE"
    fsep=
    for dir in $dirs; do
      for name in go.mod go.sum; do
        file="$dir/$name"
        [ "$dir" != . ] || file=$name
        [ -f "$file" ] || continue
        printf '%s{"path":"%s","content":"%s"}' "$fsep" "$file" "$(base64 -w0 "$file")" >>"$RESULT_FILE"
        fsep=,
      done
    done
    printf ']' >>"$RESULT_FILE"
  else
    printf ',"output":"%s"' "$(tail -c 4000 "$LOG_FILE" | base64 -w0)" >>"$RESULT_FILE"
  fi
  printf '}' >>"$RESULT_FILE"
done <<EOF
$UPDATES
EOF
printf ']}' >>"$RESULT_FILE"
printf 'sha256:%s' "$(sha256sum "$RESULT_FILE" | cut -d ' ' -f 1)" >"$TERMINATION_LOG"
`

// updateLines returns the value of the update container's UPDATES variable.
func updateLines(updates []update) string {
	var b strings.Builder
	for _, up := range updates {
		fmt.Fprintf(&b, "%s %s %s\n", up.module, up.version, strings.Join(slices.Sorted(maps.Keys(up.from)), " "))
	}
	return b.String()
}

// pod declares the Pod that makes updates on the parent's head. Its name
// covers the parent's GitBranch, the attempt, and the Pod's spec.
func (u *updater) pod(b *Branch, repo *gitk8s.Repository, head string, attempt int, updates []update) *agent.Pod {
	yes, no := true, false
	user := int64(65532)
	deadline := max(1, int64(u.timeout.Seconds()))
	restricted := &agent.SecurityContext{
		AllowPrivilegeEscalation: &no,
		ReadOnlyRootFilesystem:   &yes,
		Capabilities:             &agent.Capabilities{Drop: []string{"ALL"}},
	}
	prepareEnv := []agent.EnvVar{
		{Name: "URL", Value: repo.Spec.URL},
		{Name: "BRANCH", Value: b.Spec.Branch},
		{Name: "HEAD", Value: head},
		{Name: "REPO", Value: repoDir},
		{Name: "HOME", Value: "/tmp"},
		{Name: "GIT_TERMINAL_PROMPT", Value: "0"},
		{Name: "GIT_ALLOW_PROTOCOL", Value: allowProtocol},
	}
	if ref := repo.Spec.SecretRef; ref != nil {
		prepareEnv = append(prepareEnv,
			agent.EnvVar{Name: "GIT_USERNAME", ValueFrom: &agent.EnvVarSource{SecretKeyRef: &agent.SecretKeySelector{Name: ref.Name, Key: "username", Optional: &yes}}},
			agent.EnvVar{Name: "GIT_PASSWORD", ValueFrom: &agent.EnvVarSource{SecretKeyRef: &agent.SecretKeySelector{Name: ref.Name, Key: "password"}}},
		)
	}
	port := u.port()
	p := &agent.Pod{Object: kube.Meta("", maps.Clone(podLabels))}
	p.Spec = agent.PodSpec{
		RestartPolicy:                "Never",
		AutomountServiceAccountToken: &no,
		EnableServiceLinks:           &no,
		ActiveDeadlineSeconds:        &deadline,
		RuntimeClassName:             u.runtimeClass,
		SecurityContext: &agent.PodSecurityContext{
			RunAsNonRoot:   &yes,
			RunAsUser:      &user,
			RunAsGroup:     &user,
			FSGroup:        &user,
			SeccompProfile: &agent.SeccompProfile{Type: "RuntimeDefault"},
		},
		Volumes: []agent.Volume{
			{Name: "src", EmptyDir: &agent.EmptyDir{}},
			{Name: "tmp", EmptyDir: &agent.EmptyDir{}},
			{Name: "result", EmptyDir: &agent.EmptyDir{SizeLimit: "64Mi"}},
		},
		InitContainers: []agent.Container{{
			Name:                     "prepare",
			Image:                    u.gitImage,
			ImagePullPolicy:          "IfNotPresent",
			Command:                  []string{"sh", "-c", prepareScript},
			Env:                      prepareEnv,
			VolumeMounts:             []agent.VolumeMount{{Name: "src", MountPath: "/src"}, {Name: "tmp", MountPath: "/tmp"}},
			SecurityContext:          restricted,
			TerminationMessagePolicy: "FallbackToLogsOnError",
			Resources: &agent.Resources{
				Requests: map[string]k8s.Quantity{"cpu": "100m", "memory": "128Mi"},
				Limits:   map[string]k8s.Quantity{"memory": "1Gi"},
			},
		}, {
			Name:            "update",
			Image:           u.goImage,
			ImagePullPolicy: "IfNotPresent",
			Command:         []string{"sh", "-c", updateScript},
			Env: []agent.EnvVar{
				{Name: "UPDATES", Value: updateLines(updates)},
				{Name: "REPO", Value: repoDir},
				{Name: "RESULT_FILE", Value: resultFile},
				{Name: "LOG_FILE", Value: logFile},
				{Name: "TERMINATION_LOG", Value: "/dev/termination-log"},
				{Name: "HOME", Value: "/tmp"},
				{Name: "GOCACHE", Value: "/tmp/go-build"},
				{Name: "GOPATH", Value: "/tmp/go"},
				{Name: "GOTOOLCHAIN", Value: "local"},
				{Name: "GOWORK", Value: "off"},
				{Name: "GOPROXY", Value: strings.Join(u.proxy.urls, ",")},
				{Name: "GOSUMDB", Value: u.goSumDB},
				{Name: "CGO_ENABLED", Value: "0"},
				{Name: "GIT_TERMINAL_PROMPT", Value: "0"},
				{Name: "GIT_ALLOW_PROTOCOL", Value: allowProtocol},
			},
			VolumeMounts: []agent.VolumeMount{
				{Name: "src", MountPath: "/src"},
				{Name: "tmp", MountPath: "/tmp"},
				{Name: "result", MountPath: "/result"},
			},
			SecurityContext:          restricted,
			TerminationMessagePolicy: "FallbackToLogsOnError",
			Resources: &agent.Resources{
				Requests: map[string]k8s.Quantity{"cpu": "100m", "memory": "256Mi"},
				Limits:   map[string]k8s.Quantity{"memory": "2Gi"},
			},
		}},
		Containers: []agent.Container{{
			Name:            "result",
			Image:           u.resultImage,
			ImagePullPolicy: "IfNotPresent",
			Args:            []string{"serve"},
			Env: []agent.EnvVar{
				{Name: "POD_UID", ValueFrom: &agent.EnvVarSource{FieldRef: &agent.FieldSelector{FieldPath: "metadata.uid"}}},
				{Name: "RESULT_FILE", Value: resultFile},
				{Name: "PORT", Value: strconv.Itoa(port)},
			},
			Ports:                    []agent.ContainerPort{{Name: "result", ContainerPort: int32(port), Protocol: "TCP"}},
			VolumeMounts:             []agent.VolumeMount{{Name: "result", MountPath: "/result", ReadOnly: true}},
			SecurityContext:          restricted,
			TerminationMessagePolicy: "FallbackToLogsOnError",
			Resources: &agent.Resources{
				Requests: map[string]k8s.Quantity{"cpu": "10m", "memory": "32Mi"},
				Limits:   map[string]k8s.Quantity{"memory": "256Mi"},
			},
		}},
	}
	spec, _ := json.Marshal(p.Spec)
	sum := sha256.Sum256(fmt.Appendf(nil, "%s\x00%d\x00%s", b.Name, attempt, spec))
	p.Name = "deps-" + hex.EncodeToString(sum[:8])
	return p
}

// unfinishedPods counts the update Pods in all namespaces that haven't
// finished, or returns 0 if the Pod named name in namespace ns already
// exists, because that Pod needs no new place.
func (u *updater) unfinishedPods(ctx context.Context, ns, name string) int {
	if u.maxPods <= 0 || kube.Get[podPhase](ctx, ns, name) != nil {
		return 0
	}
	n := 0
	for _, p := range kube.List[podPhase](ctx, kube.MatchingLabels(podLabels)) {
		if p.Status.Phase != "Succeeded" && p.Status.Phase != "Failed" {
			n++
		}
	}
	return n
}

// follow starts or follows the Pod that makes updates, and returns their
// outcomes once it can. It returns nil while the Pod runs.
func (u *updater) follow(ctx context.Context, desired *agent.Pod, updates []update, log *slog.Logger) map[module.Version]*outcome {
	pod := kube.Own(ctx, desired)
	if pod == nil {
		log.Info("starting an update Pod", "pod", desired.Name, "updates", len(updates))
		return nil
	}
	failAll := func(format string, args ...any) map[module.Version]*outcome {
		msg := fmt.Sprintf(format, args...)
		out := map[module.Version]*outcome{}
		for _, up := range updates {
			out[up.key()] = &outcome{err: msg}
		}
		return out
	}
	st := &pod.Status
	if t := container(st.InitContainerStatuses, "prepare").Terminated; t != nil && t.ExitCode != 0 {
		return failAll("preparing the source in Pod %s failed: %s", pod.Name, exitMessage(t))
	}
	t := container(st.InitContainerStatuses, "update").Terminated
	switch {
	case t != nil && t.ExitCode != 0:
		return failAll("the update container in Pod %s failed: %s", pod.Name, exitMessage(t))
	case t == nil && st.Phase == "Failed":
		return failAll("Pod %s stopped before the update finished: %s", pod.Name, cmp.Or(st.Message, st.Reason, "no reason given"))
	case t == nil:
		return nil
	}
	server := container(st.ContainerStatuses, "result")
	if server.Terminated != nil || st.Phase == "Failed" || st.Phase == "Succeeded" {
		return failAll("Pod %s stopped before the controller fetched the result", pod.Name)
	}
	if server.Running == nil || st.PodIP == "" {
		return nil
	}
	body, err := agent.FetchResult(ctx, st.PodIP, u.port(), pod.UID, strings.TrimSpace(t.Message))
	if errors.Is(err, agent.ErrInvalidResult) {
		return failAll("the result from Pod %s isn't valid: %v", pod.Name, err)
	}
	if err != nil {
		kube.RequeueAfter(ctx, fetchRetry)
		return nil
	}
	out, err := parseResult(body, updates)
	if err != nil {
		return failAll("the result from Pod %s isn't valid: %v", pod.Name, err)
	}
	return out
}

func container(statuses []agent.ContainerStatus, name string) agent.ContainerState {
	for _, s := range statuses {
		if s.Name == name {
			return s.State
		}
	}
	return agent.ContainerState{}
}

func exitMessage(t *agent.Terminated) string {
	return cmp.Or(strings.TrimSpace(t.Message), t.Reason, fmt.Sprintf("exit code %d", t.ExitCode))
}

// parseResult reads the outcomes of updates from the result that the
// update container wrote.
func parseResult(body []byte, updates []update) (map[module.Version]*outcome, error) {
	var res struct {
		Updates []struct {
			Module  string `json:"module"`
			Version string `json:"version"`
			OK      bool   `json:"ok"`
			Files   []struct {
				Path    string `json:"path"`
				Content []byte `json:"content"`
			} `json:"files"`
			Output []byte `json:"output"`
		} `json:"updates"`
	}
	if err := json.Unmarshal(body, &res); err != nil {
		return nil, err
	}
	want := map[module.Version]update{}
	for _, up := range updates {
		want[up.key()] = up
	}
	out := map[module.Version]*outcome{}
	for _, r := range res.Updates {
		key := module.Version{Path: r.Module, Version: r.Version}
		up, ok := want[key]
		switch {
		case !ok:
			return nil, fmt.Errorf("it has an update to %.200s that wasn't asked for", key)
		case out[key] != nil:
			return nil, fmt.Errorf("it has the update to %s twice", key)
		case !r.OK:
			out[key] = &outcome{err: "go failed: " + clean(string(r.Output))}
			continue
		}
		allowed := map[string]bool{}
		for dir := range up.from {
			allowed[path.Join(dir, "go.mod")] = true
			allowed[path.Join(dir, "go.sum")] = true
		}
		files := map[string][]byte{}
		for _, f := range r.Files {
			if !allowed[f.Path] || files[f.Path] != nil {
				return nil, fmt.Errorf("it has the file %.200q for the update to %s", f.Path, key)
			}
			files[f.Path] = f.Content
		}
		for dir := range up.from {
			if files[path.Join(dir, "go.mod")] == nil {
				return nil, fmt.Errorf("it has no %s for the update to %s", path.Join(dir, "go.mod"), key)
			}
		}
		out[key] = &outcome{files: files}
	}
	if len(out) != len(want) {
		return nil, fmt.Errorf("it has %d of the %d updates", len(out), len(want))
	}
	return out, nil
}

// clean keeps the end of go's output, without control characters other
// than newlines and tabs.
func clean(s string) string {
	s = strings.TrimSpace(strings.Map(func(r rune) rune {
		if r != '\n' && r != '\t' && (unicode.IsControl(r) || r == utf8.RuneError) {
			return -1
		}
		return r
	}, s))
	if len(s) > 1000 {
		s = "..." + s[len(s)-1000:]
	}
	return cmp.Or(s, "no output")
}

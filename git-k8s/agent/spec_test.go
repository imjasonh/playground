package agent

import (
	"encoding/json"
	"errors"
	"fmt"
	"maps"
	"os"
	"os/exec"
	"path/filepath"
	"reflect"
	"regexp"
	"slices"
	"strings"
	"testing"
	"time"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/checks"
	"github.com/imjasonh/playground/git-k8s/internal/git"
	"github.com/imjasonh/playground/git-k8s/internal/gittest"
	"github.com/imjasonh/playground/kube"
)

func TestStartsALockedDownPod(t *testing.T) {
	f := newFixture(t, "s3cret")
	p := f.start()
	if p.Labels["app.kubernetes.io/name"] != "git-k8s-agent" || p.Labels[agentLabel] != "review" || !strings.HasPrefix(p.Name, "review-") {
		t.Errorf("Pod %s has labels %v", p.Name, p.Labels)
	}
	spec := p.Spec
	if *spec.AutomountServiceAccountToken || *spec.EnableServiceLinks || spec.RestartPolicy != "Never" ||
		!*spec.SecurityContext.RunAsNonRoot || spec.SecurityContext.SeccompProfile.Type != "RuntimeDefault" {
		t.Errorf("Pod spec isn't locked down: %+v", spec)
	}
	if got := *spec.ActiveDeadlineSeconds; got != 60+1800 {
		t.Errorf("activeDeadlineSeconds = %d, want the timeout and 30 minutes", got)
	}

	secrets := map[string][]string{}
	mounts := map[string][]string{}
	var task, uid, port string
	for _, c := range slices.Concat(spec.InitContainers, spec.Containers) {
		sc := c.SecurityContext
		if *sc.AllowPrivilegeEscalation || !*sc.ReadOnlyRootFilesystem || !slices.Equal(sc.Capabilities.Drop, []string{"ALL"}) || c.Resources.Limits["memory"] == "" {
			t.Errorf("container %s isn't locked down: %+v, %+v", c.Name, sc, c.Resources)
		}
		for _, e := range c.Env {
			switch {
			case e.ValueFrom != nil && e.ValueFrom.SecretKeyRef != nil:
				secrets[c.Name] = append(secrets[c.Name], e.ValueFrom.SecretKeyRef.Name+"/"+e.ValueFrom.SecretKeyRef.Key)
			case e.ValueFrom != nil:
				uid = c.Name + " " + e.Name + " " + e.ValueFrom.FieldRef.FieldPath
			case e.Name == "AGENT_TASK":
				task = e.Value
			case e.Name == "PORT":
				port = e.Value
			}
		}
		for _, m := range c.VolumeMounts {
			mount := m.Name + ":" + m.MountPath
			if m.ReadOnly {
				mount += ":ro"
			}
			mounts[c.Name] = append(mounts[c.Name], mount)
		}
	}
	if want := map[string][]string{"prepare": {"app-creds/username", "app-creds/password", "cursor-api-key/api-key"}}; !reflect.DeepEqual(secrets, want) {
		t.Errorf("Secrets = %v, want only the prepare container to read them", secrets)
	}
	want := map[string][]string{
		"prepare": {"git:/git", "src:/src", "input:/input", "key:/key"},
		"agent":   {"src:/src:ro", "input:/input:ro", "key:/key", "result:/result", "tmp:/tmp"},
		"result":  {"result:/result:ro"},
	}
	if !reflect.DeepEqual(mounts, want) {
		t.Errorf("mounts = %v, want %v", mounts, want)
	}
	if uid != "result POD_UID metadata.uid" || port != fmt.Sprint(f.r.port) {
		t.Errorf("result container has POD_UID %q and PORT %q", uid, port)
	}
	if v := spec.Volumes[slices.IndexFunc(spec.Volumes, func(v Volume) bool { return v.Name == "key" })]; v.EmptyDir.Medium != "Memory" {
		t.Errorf("key volume = %+v, want it in memory", v)
	}

	var got podTask
	if err := json.Unmarshal([]byte(task), &got); err != nil {
		t.Fatal(err)
	}
	if strings.Contains(task, `"merge"`) {
		t.Errorf("AGENT_TASK = %s, want no merge", task)
	}
	wantTask := podTask{
		Backend: "fake", Model: "composer-2.5", Instructions: "Review the change.", TimeoutSeconds: 60,
		Branch: "c/x", Parent: "main", Head: f.b.Spec.Head, Base: f.base, WorkTree: "/src",
		DiffFile: "/input/change.diff", LogFile: "/input/log.txt", FilesFile: "/input/files", KeyFile: "/key/api-key",
		ResultFile: "/result/result.json", TerminationLog: "/dev/termination-log", ChangesFile: "/input/changes",
	}
	if got != wantTask {
		t.Errorf("AGENT_TASK = %+v, want %+v", got, wantTask)
	}

	t.Log("An agent that can edit gets a writable source volume.")
	f.task.Edit = true
	p = f.start()
	if m := p.Spec.InitContainers[1].VolumeMounts[0]; m.Name != "src" || m.ReadOnly {
		t.Errorf("agent's source mount = %+v, want it writable", m)
	}
}

func TestStartsAMergePod(t *testing.T) {
	f := newMergeFixture(t)
	f.task.Merge.Union = []string{"go.sum"}
	main := f.task.Merge.Commit
	p := f.start()
	prepare, agent := p.Spec.InitContainers[0], p.Spec.InitContainers[1]
	env := map[string]string{}
	for _, e := range prepare.Env {
		env[e.Name] = e.Value
	}
	if env["MERGE"] != main || env["MERGE_REF"] != "refs/heads/main" || env["ATTRIBUTES"] != "go.sum merge=union\n" || env["BASE"] != f.base {
		t.Errorf("prepare's environment = %v, want the merge from the merge base", env)
	}
	if m := agent.VolumeMounts[0]; m.Name != "src" || m.ReadOnly {
		t.Errorf("agent's source mount = %+v, want it writable", m)
	}
	var task podTask
	if err := json.Unmarshal([]byte(agent.Env[0].Value), &task); err != nil {
		t.Fatal(err)
	}
	want := podMerge{Commit: main, Name: "main", ConflictsFile: "/input/conflicts", DiffFile: "/input/merge.diff", LogFile: "/input/merge-log.txt"}
	if !task.Edit || task.Base != f.base || task.Merge != want {
		t.Errorf("AGENT_TASK = %+v, want an edit with the merge %+v", task, want)
	}
}

// fieldsOf returns the fields of a TypeScript interface in a runner source
// file.
func fieldsOf(t *testing.T, file, iface string) []string {
	t.Helper()
	src, err := os.ReadFile(filepath.Join("runner", "src", file))
	if err != nil {
		t.Fatal(err)
	}
	_, body, ok := strings.Cut(string(src), "export interface "+iface+" {\n")
	body, _, _ = strings.Cut(body, "\n}")
	if !ok {
		t.Fatalf("%s has no interface %s", file, iface)
	}
	var fields []string
	for _, m := range regexp.MustCompile(`(?m)^  (\w+)\??: `).FindAllStringSubmatch(body, -1) {
		fields = append(fields, m[1])
	}
	slices.Sort(fields)
	return fields
}

// jsonFields returns the JSON names of a struct's fields.
func jsonFields(v any) []string {
	var fields []string
	typ := reflect.TypeOf(v)
	for i := range typ.NumField() {
		name, _, _ := strings.Cut(typ.Field(i).Tag.Get("json"), ",")
		fields = append(fields, name)
	}
	slices.Sort(fields)
	return fields
}

func TestMatchesTheRunner(t *testing.T) {
	for _, tc := range []struct {
		file, iface string
		v           any
	}{
		{"task.ts", "Task", podTask{}},
		{"task.ts", "Merge", podMerge{}},
		{"result.ts", "Result", Result{}},
		{"result.ts", "Usage", Usage{}},
		{"result.ts", "ChangedFile", File{}},
	} {
		if got, want := jsonFields(tc.v), fieldsOf(t, tc.file, tc.iface); !slices.Equal(got, want) {
			t.Errorf("%T has JSON fields %v, but %s in runner/src/%s has %v", tc.v, got, tc.iface, tc.file, want)
		}
	}
}

// runMerge makes the merge that Run commits, of m into head from base, in a
// new repository that fetches main and c/x from remote. It returns the
// merged tree and its a.txt, and expects a.txt to be the only conflict.
func runMerge(t *testing.T, remote git.Remote, head string, m *Merge, base string) (string, string) {
	t.Helper()
	ctx := t.Context()
	repo, err := (&git.Git{}).Open(ctx, filepath.Join(t.TempDir(), "app.git"))
	if err != nil {
		t.Fatal(err)
	}
	if err := repo.Fetch(ctx, remote, "main", "c/x"); err != nil {
		t.Fatal(err)
	}
	tree, conflicts, err := repo.Merge(ctx, head, m.Commit, git.MergeOptions{Base: base, Union: m.Union})
	if err != nil || len(conflicts) != 1 || conflicts[0].Path != "a.txt" {
		t.Fatalf("Merge = %v, %v; want a conflict in a.txt", conflicts, err)
	}
	b, err := repo.ReadBlob(ctx, tree+":a.txt")
	if err != nil {
		t.Fatal(err)
	}
	return tree, string(b)
}

func TestPrepareScript(t *testing.T) {
	sh, err := exec.LookPath("sh")
	if err != nil {
		t.Skip("sh isn't installed")
	}
	// The git image has no other commands, so the script gets a PATH with
	// only git.
	git, err := exec.LookPath("git")
	if err != nil {
		t.Fatal(err)
	}
	bin := t.TempDir()
	if err := os.Symlink(git, filepath.Join(bin, "git")); err != nil {
		t.Fatal(err)
	}
	srv := gittest.NewServer(t, "s3cret")
	w := srv.NewWork(t, "app")
	w.Write(".gitattributes", "* text eol=crlf\n")
	w.Write("a.txt", "one\ntwo\n")
	w.Write(".cursorignore", "a.txt\n")
	base := w.Commit("main")
	w.Push("main")
	w.Branch("c/x", base)
	for i := range 60 {
		w.Write("a.txt", fmt.Sprintf("one\ntwo\n%d\n", i))
		msg := fmt.Sprintf("change %d", i)
		if i == 59 {
			msg += strings.Repeat(" long", 100)
		}
		w.Commit(msg)
	}
	w.Write("dir/b.txt", "b\n")
	w.Write("dir/.cursorignore", "b.txt\n")
	head := w.Commit("add b")
	w.Push("c/x")
	repo, secret := srv.Repository("app")

	// prepare runs the script with the prepare container's environment,
	// with its volumes in a temporary directory.
	prepare := func(t *testing.T, task Task, head, base string) (string, string, error) {
		r := &Runner{Name: "review", Image: "agent", GitImage: "git", Backend: "fake", Model: "m", Secret: "cursor-api-key", Timeout: time.Minute}
		spec := &gitk8s.GitBranchSpec{Branch: "c/x", Parent: "main", Head: head}
		in := &checks.Input{Meta: &kube.ObjectMeta{Name: "app-c-x"}, Spec: spec, Repository: &gitk8s.Repository{Spec: repo.Spec}}
		c := r.pod(in, task, base, 1).Spec.InitContainers[0]
		dir := t.TempDir()
		for _, m := range c.VolumeMounts {
			if err := os.MkdirAll(dir+m.MountPath, 0o755); err != nil {
				t.Fatal(err)
			}
		}
		data := maps.Clone(secret.Data)
		data["api-key"] = []byte("key-123")
		if c.Command[0] != "sh" {
			t.Fatalf("prepare runs %q, want sh", c.Command)
		}
		cmd := exec.Command(sh, c.Command[1:]...)
		cmd.Env = []string{"PATH=" + bin, "GIT_CONFIG_NOSYSTEM=1"}
		for _, e := range c.Env {
			v := e.Value
			if e.ValueFrom != nil {
				v = string(data[e.ValueFrom.SecretKeyRef.Key])
			} else if strings.HasPrefix(v, "/") {
				v = dir + v
			}
			cmd.Env = append(cmd.Env, e.Name+"="+v)
		}
		out, err := cmd.CombinedOutput()
		return dir, string(out), err
	}
	read := func(path string) string {
		t.Helper()
		b, err := os.ReadFile(path)
		if err != nil {
			t.Fatal(err)
		}
		return string(b)
	}

	dir, out, err := prepare(t, Task{}, head, base)
	if err != nil {
		t.Fatalf("prepare: %v\n%s", err, out)
	}
	if got := read(dir + "/src/a.txt"); got != "one\ntwo\n59\n" {
		t.Errorf("a.txt = %q, want the blob's bytes", got)
	}
	if got := read(dir + "/src/dir/b.txt"); got != "b\n" {
		t.Errorf("dir/b.txt = %q", got)
	}
	if _, err := os.Stat(dir + "/src/.git"); !os.IsNotExist(err) {
		t.Errorf("the work tree has a .git: %v", err)
	}
	for _, path := range []string{"/src/.cursorignore", "/src/dir/.cursorignore"} {
		if _, err := os.Stat(dir + path); !os.IsNotExist(err) {
			t.Errorf("the work tree has %s: %v", path, err)
		}
	}
	if got, want := read(dir+"/input/changes"), "M\x00a.txt\x00A\x00dir/.cursorignore\x00A\x00dir/b.txt\x00"; got != want {
		t.Errorf("changes = %q, want %q", got, want)
	}
	if files := read(dir + "/input/files"); strings.Count(files, "\x00") != 3 || !strings.Contains(files, " 0\tdir/b.txt\x00") {
		t.Errorf("files = %q, want the head's 3 files", files)
	}
	if diff := read(dir + "/input/change.diff"); !strings.Contains(diff, "+59") || !strings.Contains(diff, "diff --git a/dir/b.txt b/dir/b.txt") {
		t.Errorf("change.diff =\n%s", diff)
	}
	if log := strings.Split(strings.TrimSpace(read(dir+"/input/log.txt")), "\n"); len(log) != 50 || !strings.HasSuffix(strings.TrimRight(log[0], " "), " add b") {
		t.Errorf("log.txt = %q, want the newest 50 commits", log)
	} else if long := log[1]; len(long) > 220 || !strings.HasSuffix(long, " long lon..") {
		t.Errorf("log.txt has %q, want its subject cut at 200 columns", long)
	}
	if fi, err := os.Stat(dir + "/key/api-key"); err != nil || fi.Mode().Perm() != 0o600 || read(dir+"/key/api-key") != "key-123" {
		t.Errorf("api-key = %v, %v; want key-123 that only its owner can read", fi, err)
	}

	t.Log("Without a merge base, the change is every file.")
	dir, out, err = prepare(t, Task{}, head, "")
	if err != nil {
		t.Fatalf("prepare: %v\n%s", err, out)
	}
	if diff := read(dir + "/input/change.diff"); !strings.Contains(diff, "new file mode 100644\nindex 0000000..") || !strings.Contains(diff, "+one") {
		t.Errorf("change.diff =\n%s", diff)
	}

	t.Log("A branch that moved fails with status 3.")
	_, out, err = prepare(t, Task{}, base, base)
	var exit *exec.ExitError
	if !errors.As(err, &exit) || exit.ExitCode() != 3 || !strings.Contains(out, "c/x no longer points to "+base) {
		t.Errorf("prepare = %v\n%s; want status 3", err, out)
	}

	t.Log("A merge writes the merge's files, even when its ref moved more than 50 commits past it.")
	w.Branch("main", base)
	w.Write("a.txt", "one\ntwo\nmain\n")
	w.Write("go.sum", "y v2\n")
	merge := w.Commit("change main" + strings.Repeat(" long", 100))
	for i := range 55 {
		w.Write("later.txt", fmt.Sprintf("%d\n", i))
		w.Commit(fmt.Sprintf("later %d", i))
	}
	w.Push("main")
	w.Branch("c/x", head)
	w.Write("go.sum", "z v3\n")
	head = w.Commit("add go.sum")
	w.Push("c/x")
	task := Task{Merge: &Merge{Commit: merge, Ref: "refs/heads/main", Name: "main", Union: []string{"go.sum"}}}
	dir, out, err = prepare(t, task, head, base)
	if err != nil {
		t.Fatalf("prepare: %v\n%s", err, out)
	}
	tree, merged := runMerge(t, srv.Remote("app"), head, task.Merge, base)
	if got, want := read(dir+"/input/conflicts"), tree+"\x00a.txt\x00"; got != want {
		t.Errorf("conflicts = %q, want %q, from the merge that Run commits", got, want)
	}
	if got := read(dir + "/src/a.txt"); got != merged || !strings.Contains(got, "<<<<<<< "+head+"\n") {
		t.Errorf("a.txt = %q, want the merge's %q", got, merged)
	}
	if got := read(dir + "/src/go.sum"); got != "z v3\ny v2\n" {
		t.Errorf("go.sum = %q, want both sides' lines", got)
	}
	if _, err := os.Stat(dir + "/src/later.txt"); !os.IsNotExist(err) {
		t.Errorf("the work tree has later.txt, from after the merge's commit: %v", err)
	}
	for _, path := range []string{"/src/.cursorignore", "/src/dir/.cursorignore"} {
		if _, err := os.Stat(dir + path); !os.IsNotExist(err) {
			t.Errorf("the merge's work tree has %s: %v", path, err)
		}
	}
	if files := read(dir + "/input/files"); strings.Count(files, "\x00") != 4 || !strings.Contains(files, "\tgo.sum\x00") {
		t.Errorf("files = %q, want the merge's 4 files", files)
	}
	if diff := read(dir + "/input/merge.diff"); !strings.Contains(diff, "+main") || !strings.Contains(diff, "+y v2") || strings.Contains(diff, "later.txt") {
		t.Errorf("merge.diff =\n%s", diff)
	}
	if log := strings.Split(strings.TrimSpace(read(dir+"/input/merge-log.txt")), "\n"); len(log) != 1 || !strings.Contains(log[0], " change main long") {
		t.Errorf("merge-log.txt = %q, want main's commit since the merge base", log)
	} else if len(log[0]) > 220 || !strings.HasSuffix(log[0], "..") {
		t.Errorf("merge-log.txt has %q, want its subject cut at 200 columns", log[0])
	}
	if diff := read(dir + "/input/change.diff"); !strings.Contains(diff, "+z v3") || strings.Contains(diff, "+y v2") {
		t.Errorf("change.diff =\n%s\nwant the branch's change", diff)
	}

	t.Log("A merge whose ref no longer holds its commit fails with status 3.")
	w.Branch("main", base)
	w.Push("main")
	_, out, err = prepare(t, task, head, base)
	if !errors.As(err, &exit) || exit.ExitCode() != 3 || !strings.Contains(out, "refs/heads/main no longer holds "+merge) {
		t.Errorf("prepare = %v\n%s; want status 3", err, out)
	}

	t.Log("A URL that looks like an option is still a URL.")
	marker := filepath.Join(t.TempDir(), "ran")
	repo.Spec.URL = "--upload-pack=echo >" + marker
	if _, out, err = prepare(t, Task{}, head, base); err == nil {
		t.Errorf("prepare succeeded with an option for a URL\n%s", out)
	}
	if _, err := os.Stat(marker); !os.IsNotExist(err) {
		t.Errorf("prepare ran the URL's --upload-pack: %v", err)
	}

	t.Log("A merge ref that looks like an option is still a ref.")
	// git runs a fetch's --upload-pack for a file URL, but not for an HTTP
	// one.
	local := filepath.Join(t.TempDir(), "app.git")
	w.Git("clone", "--quiet", "--bare", w.Dir, local)
	repo.Spec.URL = "file://" + local
	marker = filepath.Join(t.TempDir(), "ran")
	task.Merge.Ref = "--upload-pack=echo >" + marker
	if _, out, err = prepare(t, task, head, base); err == nil {
		t.Errorf("prepare succeeded with an option for a merge ref\n%s", out)
	}
	if _, err := os.Stat(marker); !os.IsNotExist(err) {
		t.Errorf("prepare ran the merge ref's --upload-pack: %v", err)
	}
}

package main

import (
	"bytes"
	"context"
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"errors"
	"flag"
	"log"
	"log/slog"
	"net/http"
	"net/http/httptest"
	"net/url"
	"os"
	"path/filepath"
	"slices"
	"strconv"
	"strings"
	"sync"
	"testing"
	"time"

	"golang.org/x/mod/modfile"
	"golang.org/x/mod/module"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/agent"
	"github.com/imjasonh/playground/git-k8s/checks"
	"github.com/imjasonh/playground/git-k8s/internal/git"
	"github.com/imjasonh/playground/git-k8s/internal/gittest"
	"github.com/imjasonh/playground/kube"
)

const (
	greet       = "example.com/greet"
	greetBranch = "deps/go/example.com/greet@v1"
	agentFix    = "Apply changes from the deps agent\n\nGit-K8s-Fixer: deps\nGit-K8s-Agent: deps"
)

// checksID is the identity that checks commit their fixes as.
var checksID = git.Identity{Name: "git-k8s", Email: "checks@example.com"}

// modAt returns the app's go.mod file, which requires greet at version.
func modAt(version string) string {
	return "module example.com/app\n\ngo 1.24\n\nrequire example.com/greet " + version + "\n"
}

// sumAt returns the app's go.sum file for greet at version.
func sumAt(version string) string {
	return "example.com/greet " + version + " h1:" + version + "=\nexample.com/greet " + version + "/go.mod h1:" + version + "=\n"
}

// modWith returns the app's go.mod file with requirements, given as pairs
// of module paths and versions.
func modWith(reqs ...string) string {
	s := "module example.com/app\n\ngo 1.24\n\nrequire (\n"
	for i := 0; i < len(reqs); i += 2 {
		s += "\t" + reqs[i] + " " + reqs[i+1] + "\n"
	}
	return s + ")\n"
}

// captureLogs sends what the controller logs to the returned buffer until
// the test ends.
func captureLogs(t *testing.T) *bytes.Buffer {
	var buf bytes.Buffer
	old, w, flags := slog.Default(), log.Writer(), log.Flags()
	slog.SetDefault(slog.New(slog.NewTextHandler(&buf, nil)))
	t.Cleanup(func() {
		slog.SetDefault(old)
		log.SetOutput(w)
		log.SetFlags(flags)
	})
	return &buf
}

// fixture is a repository on a git server whose main branch requires greet
// v1.0.0, a module proxy that has greet v1.0.0 and v1.1.0, an updater for
// them, and a server that stands in for the result containers of its Pods.
// The updater has no -min-age, which would hold back each version from when
// it first shows up.
type fixture struct {
	t     *testing.T
	srv   *gittest.Server
	work  *gittest.Work
	proxy *fakeProxy
	u     *updater
	b     *Branch
	rules []gitk8s.BranchRule
	clock time.Time

	mu   sync.Mutex
	body []byte
	uid  string
}

func newFixture(t *testing.T) *fixture {
	srv := gittest.NewServer(t, "s3cret")
	w := srv.NewWork(t, "app")
	w.Write("go.mod", modAt("v1.0.0"))
	w.Write("go.sum", sumAt("v1.0.0"))
	w.Write("app.go", "package app\n")
	main := w.Commit("main")
	w.Push("main")

	fp := newFakeProxy(t)
	fp.publish(greet, "v1.0.0", longAgo, "")
	fp.publish(greet, "v1.1.0", longAgo, "")

	f := &fixture{t: t, srv: srv, work: w, proxy: fp, clock: today}
	f.rules = []gitk8s.BranchRule{
		{Match: "main", Merge: &gitk8s.MergePolicy{Checks: []gitk8s.CheckPolicy{{Name: "base", MayPush: true}, {Name: "gotest"}}}},
		{Match: "deps/**", Parent: "main"},
	}
	f.b = &Branch{Object: kube.Meta(gitk8s.BranchObjectName("app", "main"), nil)}
	f.b.Namespace = "default"
	f.b.Spec = gitk8s.GitBranchSpec{Repository: "app", Branch: "main", Head: main}

	hs := httptest.NewServer(http.HandlerFunc(f.serveResult))
	t.Cleanup(hs.Close)
	u, err := url.Parse(hs.URL)
	if err != nil {
		t.Fatal(err)
	}
	port, err := strconv.Atoi(u.Port())
	if err != nil {
		t.Fatal(err)
	}
	f.u = &updater{
		cfg:        checks.Config{CacheDir: t.TempDir(), Identity: git.Identity{Name: "git-k8s-deps", Email: "deps@example.com"}},
		checkEmail: checksID.Email,
		prefix:     "deps/", goProxy: fp.URL, goSumDB: "off",
		goImage: "registry.example.com/go:test", gitImage: "registry.example.com/git:test", resultImage: "registry.example.com/agent-runner:test",
		timeout: time.Minute, sourceSize: "2Gi", goCacheSize: "4Gi", maxPods: 10, interval: time.Hour,
		now: func() time.Time { return f.clock }, resultPort: port,
	}
	return f
}

func (f *fixture) serveResult(w http.ResponseWriter, req *http.Request) {
	f.mu.Lock()
	body, uid := f.body, f.uid
	f.mu.Unlock()
	if req.URL.Path != "/result" || req.Header.Get("Authorization") != "Bearer "+uid {
		http.Error(w, "no", http.StatusUnauthorized)
		return
	}
	w.Write(body)
}

// serve makes the result server serve body to requests with uid, and
// returns body's digest.
func (f *fixture) serve(body []byte, uid string) string {
	f.mu.Lock()
	defer f.mu.Unlock()
	f.body, f.uid = body, uid
	sum := sha256.Sum256(body)
	return "sha256:" + hex.EncodeToString(sum[:])
}

func (f *fixture) reconcile(world ...any) *kube.Recorder {
	f.t.Helper()
	repo, secret := f.srv.Repository("app", f.rules...)
	ctx, rec := kube.Fake(f.t.Context(), f.b, append([]any{repo, secret}, world...)...)
	if err := f.u.Reconcile(ctx, f.b); err != nil {
		f.t.Fatal(err)
	}
	return rec
}

// start reconciles, expects the controller to start one Pod, and returns
// the Pod as the API server would hold it.
func (f *fixture) start(world ...any) *agent.Pod {
	f.t.Helper()
	pods := kube.Owned[agent.Pod](f.reconcile(world...))
	if len(pods) != 1 {
		f.t.Fatalf("owned Pods = %d, want 1", len(pods))
	}
	p := pods[0]
	p.Namespace = "default"
	p.UID = "uid-" + p.Name
	p.CreationTimestamp = f.clock
	return p
}

func terminated(t *agent.Terminated) agent.ContainerState { return agent.ContainerState{Terminated: t} }

// finished sets p's status to that of a Pod whose update container
// reported digest and whose result container is serving.
func finished(p *agent.Pod, digest string) *agent.Pod {
	p.Status = agent.PodStatus{
		Phase: "Running", PodIP: "127.0.0.1",
		InitContainerStatuses: []agent.ContainerStatus{
			{Name: "prepare", State: terminated(&agent.Terminated{Reason: "Completed"})},
			{Name: "update", State: terminated(&agent.Terminated{Reason: "Completed", Message: digest})},
		},
		ContainerStatuses: []agent.ContainerStatus{{Name: "result", State: agent.ContainerState{Running: &struct{}{}}}},
	}
	return p
}

// finish serves body as p's result and reconciles with p finished.
func (f *fixture) finish(p *agent.Pod, body []byte) *kube.Recorder {
	f.t.Helper()
	return f.reconcile(finished(p, f.serve(body, p.UID)))
}

type fileJSON struct {
	Path    string `json:"path"`
	Content []byte `json:"content"`
}

type updateJSON struct {
	Module  string     `json:"module"`
	Version string     `json:"version"`
	OK      bool       `json:"ok"`
	Files   []fileJSON `json:"files,omitempty"`
	Output  []byte     `json:"output,omitempty"`
}

// result returns the result that the update container writes.
func result(updates ...updateJSON) []byte {
	b, err := json.Marshal(map[string][]updateJSON{"updates": append([]updateJSON{}, updates...)})
	if err != nil {
		panic(err)
	}
	return b
}

// updated is the outcome of updating greet to version in the app.
func updated(version string) updateJSON {
	return withFiles(version, "go.mod", modAt(version), "go.sum", sumAt(version))
}

// withFiles is the outcome of updating greet to version that reports
// files, given as pairs of paths and contents.
func withFiles(version string, files ...string) updateJSON {
	up := updateJSON{Module: greet, Version: version, OK: true}
	for i := 0; i < len(files); i += 2 {
		up.Files = append(up.Files, fileJSON{Path: files[i], Content: []byte(files[i+1])})
	}
	return up
}

func env(c agent.Container, name string) string {
	for _, e := range c.Env {
		if e.Name == name {
			return e.Value
		}
	}
	return ""
}

// secrets returns the Secret that each of a container's variables comes
// from, if any.
func secrets(c agent.Container) map[string]string {
	out := map[string]string{}
	for _, e := range c.Env {
		if e.ValueFrom != nil && e.ValueFrom.SecretKeyRef != nil {
			out[e.Name] = e.ValueFrom.SecretKeyRef.Name
		}
	}
	return out
}

// update has the controller update greet to version on its branch, and
// returns the branch's head.
func (f *fixture) update(version string) string {
	f.t.Helper()
	p := f.start()
	if got, want := env(p.Spec.InitContainers[1], "UPDATES"), greet+" "+version+" .\n"; got != want {
		f.t.Fatalf("UPDATES = %q, want %q", got, want)
	}
	f.finish(p, result(updated(version)))
	head := f.srv.Heads(f.t, "app")[greetBranch]
	if head == "" {
		f.t.Fatalf("the controller didn't push %s", greetBranch)
	}
	f.work.Fetch(greetBranch)
	if got := f.work.Show(head, "go.mod"); got != strings.TrimSpace(modAt(version)) {
		f.t.Fatalf("go.mod on %s = %q, want greet at %s", greetBranch, got, version)
	}
	if pods := kube.Owned[agent.Pod](f.reconcile(p)); len(pods) != 0 {
		f.t.Fatalf("owned Pods = %d after the update, want 0", len(pods))
	}
	return head
}

// moveMain commits a file to main, pushes it, and returns main's new head.
func (f *fixture) moveMain(path, content string) string {
	f.t.Helper()
	f.work.Branch("main", f.b.Spec.Head)
	f.work.Write(path, content)
	f.b.Spec.Head = f.work.Commit("Change " + path)
	f.work.Push("main")
	return f.b.Spec.Head
}

// pushTo commits a file on a branch with message, pushes it, and returns
// the branch's new head.
func (f *fixture) pushTo(branch, path, content, message string) string {
	f.t.Helper()
	f.work.Branch("work", f.work.Fetch(branch))
	f.work.Write(path, content)
	head := f.work.Commit(message)
	f.work.Push(branch)
	return head
}

// commitAs commits the working repository's index on parents as id, with
// message, and checks the commit out.
func (f *fixture) commitAs(id git.Identity, message string, parents ...string) string {
	f.t.Helper()
	ctx := f.t.Context()
	repo, err := (&git.Git{}).Open(ctx, filepath.Join(f.work.Dir, ".git"))
	if err != nil {
		f.t.Fatal(err)
	}
	commit, err := repo.CommitTree(ctx, f.work.Git("write-tree"), parents, message, id, f.clock.Unix())
	if err != nil {
		f.t.Fatal(err)
	}
	f.work.Git("reset", "--quiet", "--hard", commit)
	return commit
}

// pushFix commits a file on greet's branch as a check would, with message,
// pushes it, and returns the branch's new head.
func (f *fixture) pushFix(path, content, message string) string {
	f.t.Helper()
	head := f.work.Fetch(greetBranch)
	f.work.Branch("work", head)
	f.work.Write(path, content)
	f.work.Git("add", "-A")
	fix := f.commitAs(checksID, message, head)
	f.work.Push(greetBranch)
	return fix
}

// checkBranch checks that a reconcile leaves greet's branch at head, or
// absent if head is "".
func (f *fixture) checkBranch(head string, world ...any) *kube.Recorder {
	f.t.Helper()
	rec := f.reconcile(world...)
	if got := f.srv.Heads(f.t, "app")[greetBranch]; got != head {
		f.t.Errorf("%s = %q, want %q", greetBranch, got, head)
	}
	return rec
}

// failure returns why the update to greet's version failed, or "".
func (f *fixture) failure(version string) string {
	f.u.mu.Lock()
	defer f.u.mu.Unlock()
	for _, st := range f.u.states {
		if o := st.outcomes[module.Version{Path: greet, Version: version}]; o != nil {
			return o.err
		}
	}
	return ""
}

// checkStays checks that a reconcile declares no Pod and leaves greet's
// branch at head, or absent if head is "".
func (f *fixture) checkStays(head string, world ...any) *kube.Recorder {
	f.t.Helper()
	rec := f.checkBranch(head, world...)
	if pods := kube.Owned[agent.Pod](rec); len(pods) != 0 {
		f.t.Errorf("owned Pods = %d, want 0", len(pods))
	}
	return rec
}

// restart replaces the updater with one that has the same flags and
// nothing in memory, as when the controller restarts or another replica
// takes over.
func (f *fixture) restart() {
	old := f.u
	f.u = &updater{
		cfg: old.cfg, checkEmail: old.checkEmail, prefix: old.prefix, goProxy: old.goProxy, goSumDB: old.goSumDB,
		goImage: old.goImage, gitImage: old.gitImage, resultImage: old.resultImage, runtimeClass: old.runtimeClass,
		timeout: old.timeout, sourceSize: old.sourceSize, goCacheSize: old.goCacheSize, maxPods: old.maxPods,
		interval: old.interval, minAge: old.minAge, seenConfigMap: old.seenConfigMap, now: old.now, resultPort: old.resultPort,
	}
}

// inNamespace runs the controller in namespace ns, as the namespace file of
// its Pod says.
func inNamespace(t *testing.T, ns string) {
	old := namespaceFile
	t.Cleanup(func() { namespaceFile = old })
	namespaceFile = filepath.Join(t.TempDir(), "namespace")
	if err := os.WriteFile(namespaceFile, []byte(ns+"\n"), 0o644); err != nil {
		t.Fatal(err)
	}
}

func TestIgnoresBranchesThatArentParents(t *testing.T) {
	for _, tc := range []struct {
		name   string
		branch string
		repo   string
		rules  []gitk8s.BranchRule
	}{
		{name: "a branch without dependency branches", branch: "c/x"},
		{name: "a dependency branch", branch: greetBranch},
		{name: "a repository that doesn't exist", branch: "main", repo: "other"},
		{name: "a parent of other branches", branch: "main", rules: []gitk8s.BranchRule{{Match: "main"}, {Match: "c/**", Parent: "main"}}},
		{name: "a parent of branches under another prefix", branch: "main", rules: []gitk8s.BranchRule{{Match: "main"}, {Match: "deps-x/**", Parent: "main"}}},
	} {
		t.Run(tc.name, func(t *testing.T) {
			f := newFixture(t)
			f.b.Spec.Branch = tc.branch
			if tc.repo != "" {
				f.b.Spec.Repository = tc.repo
			}
			if tc.rules != nil {
				f.rules = tc.rules
			}
			if rec := f.checkStays(""); rec.RequeueAfter() != 0 {
				t.Errorf("RequeueAfter() = %v, want 0", rec.RequeueAfter())
			}
			if n := f.proxy.hitsOf(greet, "list"); n != 0 {
				t.Errorf("the controller read greet's versions %d times, want 0", n)
			}
		})
	}
}

func TestUpdatesAModule(t *testing.T) {
	f := newFixture(t)
	main := f.b.Spec.Head
	rec := f.reconcile()
	pods := kube.Owned[agent.Pod](rec)
	if len(pods) != 1 || rec.RequeueAfter() != time.Hour {
		t.Fatalf("owned Pods = %d and RequeueAfter() = %v, want one Pod and the interval", len(pods), rec.RequeueAfter())
	}
	p := pods[0]
	prepare, update, server := p.Spec.InitContainers[0], p.Spec.InitContainers[1], p.Spec.Containers[0]
	for _, c := range []struct{ name, got, want string }{
		{"URL", env(prepare, "URL"), f.srv.Remote("app").URL},
		{"BRANCH", env(prepare, "BRANCH"), "main"},
		{"HEAD", env(prepare, "HEAD"), main},
		{"UPDATES", env(update, "UPDATES"), greet + " v1.1.0 .\n"},
		{"GOPROXY", env(update, "GOPROXY"), f.proxy.URL},
		{"GOSUMDB", env(update, "GOSUMDB"), "off"},
		{"GOTOOLCHAIN", env(update, "GOTOOLCHAIN"), "local"},
		{"PORT", env(server, "PORT"), strconv.Itoa(f.u.resultPort)},
	} {
		if c.got != c.want {
			t.Errorf("%s = %q, want %q", c.name, c.got, c.want)
		}
	}
	if got := secrets(prepare); len(got) != 2 || got["GIT_USERNAME"] != "app-creds" || got["GIT_PASSWORD"] != "app-creds" {
		t.Errorf("the prepare container's Secrets = %v, want the repository's credentials", got)
	}
	for _, c := range []agent.Container{update, server} {
		if got := secrets(c); len(got) != 0 {
			t.Errorf("container %s reads Secrets %v, want none", c.Name, got)
		}
	}
	if a := p.Spec.AutomountServiceAccountToken; a == nil || *a {
		t.Error("the Pod mounts a service account token")
	}
	if got := f.srv.Heads(t, "app")[greetBranch]; got != "" {
		t.Fatalf("the controller pushed %s before the Pod finished", greetBranch)
	}

	t.Log("While a container waits for a reason that often passes, and while go runs, the controller follows the Pod.")
	p.Namespace, p.UID = "default", "uid-"+p.Name
	for _, status := range []agent.PodStatus{{Phase: "Pending", InitContainerStatuses: []agent.ContainerStatus{
		{Name: "prepare", State: agent.ContainerState{Waiting: &agent.Waiting{Reason: "CreateContainerError", Message: "context deadline exceeded"}}},
	}}, {Phase: "Pending", InitContainerStatuses: []agent.ContainerStatus{
		{Name: "prepare", State: terminated(&agent.Terminated{Reason: "Completed"})},
		{Name: "update", State: agent.ContainerState{Running: &struct{}{}}},
	}}} {
		p.Status = status
		if pods := kube.Owned[agent.Pod](f.reconcile(p)); len(pods) != 1 || pods[0].Name != p.Name {
			t.Fatalf("owned Pods = %d, want Pod %s", len(pods), p.Name)
		}
	}

	t.Log("Until the result container serves the result, the controller tries again.")
	finished(p, f.serve(result(updated("v1.1.0")), "another-uid"))
	rec = f.reconcile(p)
	if pods := kube.Owned[agent.Pod](rec); len(pods) != 1 || rec.RequeueAfter() != fetchRetry {
		t.Fatalf("owned Pods = %d and RequeueAfter() = %v, want the Pod and %v", len(pods), rec.RequeueAfter(), fetchRetry)
	}

	t.Log("Once it does, the controller pushes the update to the module's branch.")
	rec = f.finish(p, result(updated("v1.1.0")))
	if rec.RequeueAfter() != time.Second {
		t.Errorf("RequeueAfter() = %v, want 1s, to stop declaring the Pod", rec.RequeueAfter())
	}
	head := f.work.Fetch(greetBranch)
	if got := f.work.Git("rev-parse", head+"^"); got != main {
		t.Errorf("the update's parent = %s, want main at %s", got, main)
	}
	msg := "Update example.com/greet to v1.1.0\n\nUpdate example.com/greet from v1.0.0 to v1.1.0 in go.mod.\n\nGit-K8s-Deps: go example.com/greet v1.1.0"
	if got := f.work.Git("log", "-1", "--format=%B", head); got != msg {
		t.Errorf("the update's message = %q, want %q", got, msg)
	}
	if got := f.work.Git("log", "-1", "--format=%an <%ae>", head); got != "git-k8s-deps <deps@example.com>" {
		t.Errorf("the update's author = %q, want the configured identity", got)
	}
	for path, want := range map[string]string{"go.mod": modAt("v1.1.0"), "go.sum": sumAt("v1.1.0"), "app.go": "package app\n"} {
		if got := f.work.Show(head, path); got != strings.TrimSpace(want) {
			t.Errorf("%s = %q, want %q", path, got, want)
		}
	}

	t.Log("Then it stops declaring the Pod and leaves the branch alone.")
	if rec := f.checkStays(head, p); rec.RequeueAfter() != time.Hour {
		t.Errorf("RequeueAfter() = %v, want the interval", rec.RequeueAfter())
	}
}

func TestWaitsForTheMinimumAge(t *testing.T) {
	for _, tc := range []struct {
		name string
		// published is the time that the proxy reports for v1.1.0.
		published time.Time
	}{
		{name: "a day-old version", published: today.Add(-24 * time.Hour)},
		{name: "a backdated version", published: longAgo},
	} {
		t.Run(tc.name, func(t *testing.T) {
			f := newFixture(t)
			f.u.interval, f.u.minAge = 100*time.Hour, 72*time.Hour
			f.proxy.publish(greet, "v1.1.0", tc.published, "")
			if rec := f.checkStays(""); rec.RequeueAfter() != 72*time.Hour {
				t.Errorf("RequeueAfter() = %v, want 72h, until the controller has seen v1.1.0 for 72h", rec.RequeueAfter())
			}
			f.clock = f.clock.Add(72*time.Hour - time.Second)
			if rec := f.checkStays(""); rec.RequeueAfter() != time.Second {
				t.Errorf("RequeueAfter() = %v, want 1s", rec.RequeueAfter())
			}
			f.clock = f.clock.Add(time.Second)
			f.update("v1.1.0")
		})
	}
}

func TestWaitsForTheVersionsThatAnUpdateRaises(t *testing.T) {
	const (
		other = "example.com/other"
		fresh = "example.com/fresh"
		late  = "example.com/late"
		// pseudo is a pseudo-version, which no proxy lists.
		pseudo = "v0.0.0-20251201000000-abcdefabcdef"
	)
	for _, tc := range []struct {
		name string
		// setup sets up main and the proxy before the controller first
		// looks, and returns the go.mod file that greet's update writes.
		setup func(f *fixture) string
		// later changes the proxy after the controller first looks.
		later func(f *fixture)
		// raises is the version that greet's update waits for, and until
		// is when that version is old enough.
		raises string
		until  time.Time
		// direct means that main requires the module that greet's update
		// raises, so the controller also updates it once it's old enough.
		direct bool
	}{{
		name: "a direct requirement that came out after the update",
		setup: func(f *fixture) string {
			f.proxy.publish(other, "v1.0.0", longAgo, "")
			f.moveMain("go.mod", modWith(greet, "v1.0.0", other, "v1.0.0"))
			return modWith(greet, "v1.1.0", other, "v1.5.0")
		},
		later:  func(f *fixture) { f.proxy.publish(other, "v1.5.0", f.clock, "") },
		raises: other + "@v1.5.0",
		until:  today.Add(144 * time.Hour),
		direct: true,
	}, {
		name: "a direct requirement whose time is later than when the controller saw it",
		setup: func(f *fixture) string {
			f.proxy.publish(other, "v1.0.0", longAgo, "")
			f.proxy.publish(other, "v1.5.0", today.Add(100*time.Hour), "")
			f.moveMain("go.mod", modWith(greet, "v1.0.0", other, "v1.0.0"))
			return modWith(greet, "v1.1.0", other, "v1.5.0")
		},
		raises: other + "@v1.5.0",
		until:  today.Add(172 * time.Hour),
		direct: true,
	}, {
		name: "a new module with a backdated time",
		setup: func(f *fixture) string {
			f.proxy.publish(fresh, "v1.0.0", longAgo, "")
			return modWith(greet, "v1.1.0", fresh, "v1.0.0")
		},
		raises: fresh + "@v1.0.0",
		until:  today.Add(144 * time.Hour),
	}, {
		name: "a pseudo-version",
		setup: func(f *fixture) string {
			f.proxy.set(fresh, "list", "")
			f.proxy.set(fresh, pseudo+".info", `{"Version":"`+pseudo+`","Time":"2025-12-01T00:00:00Z"}`)
			return modWith(greet, "v1.1.0", fresh, pseudo)
		},
		raises: fresh + "@" + pseudo,
		until:  today.Add(144 * time.Hour),
	}, {
		name: "the later of two versions",
		setup: func(f *fixture) string {
			f.proxy.publish(fresh, "v1.0.0", longAgo, "")
			f.proxy.publish(late, "v1.0.0", today.Add(100*time.Hour), "")
			return modWith(greet, "v1.1.0", fresh, "v1.0.0", late, "v1.0.0")
		},
		raises: late + "@v1.0.0",
		until:  today.Add(172 * time.Hour),
	}} {
		t.Run(tc.name, func(t *testing.T) {
			f := newFixture(t)
			f.u.interval, f.u.minAge = 100*time.Hour, 72*time.Hour
			logs := captureLogs(t)
			mod := tc.setup(f)
			f.checkStays("")
			if tc.later != nil {
				tc.later(f)
			}

			t.Log("Once greet's v1.1.0 is old enough, the controller updates greet, but doesn't push the update.")
			f.clock = today.Add(72 * time.Hour)
			p := f.start()
			if got, want := env(p.Spec.InitContainers[1], "UPDATES"), greet+" v1.1.0 .\n"; got != want {
				t.Fatalf("UPDATES = %q, want %q", got, want)
			}
			f.finish(p, result(withFiles("v1.1.0", "go.mod", mod, "go.sum", sumAt("v1.1.0"))))
			if head := f.srv.Heads(t, "app")[greetBranch]; head != "" {
				t.Fatalf("the controller pushed %s to %s before %s is old enough", head, greetBranch, tc.raises)
			}
			if want := "raises=" + tc.raises + " until=" + tc.until.Format("2006-01-02T15:04:05.000Z07:00"); !strings.Contains(logs.String(), want) {
				t.Errorf("the controller logged %q, want a line with %q", logs, want)
			}

			t.Log("It starts no Pod for the update until then, even when main moves.")
			if rec := f.checkStays(""); rec.RequeueAfter() != tc.until.Sub(f.clock) {
				t.Errorf("RequeueAfter() = %v, want %v", rec.RequeueAfter(), tc.until.Sub(f.clock))
			}
			f.clock = today.Add(100 * time.Hour)
			f.moveMain("README.md", "# app\n")
			f.checkStays("")
			f.clock = tc.until.Add(-time.Second)
			f.checkStays("")

			t.Log("Then it updates greet again, and pushes the update.")
			f.clock = tc.until
			p = f.start()
			updates, want := []updateJSON{withFiles("v1.1.0", "go.mod", mod, "go.sum", sumAt("v1.1.0"))}, greet+" v1.1.0 .\n"
			if tc.direct {
				updates = append(updates, updateJSON{Module: other, Version: "v1.5.0", OK: true, Files: []fileJSON{{Path: "go.mod", Content: []byte(modWith(greet, "v1.0.0", other, "v1.5.0"))}}})
				want += other + " v1.5.0 .\n"
			}
			if got := env(p.Spec.InitContainers[1], "UPDATES"); got != want {
				t.Fatalf("UPDATES = %q, want %q", got, want)
			}
			f.finish(p, result(updates...))
			head := f.srv.Heads(t, "app")[greetBranch]
			if head == "" {
				t.Fatalf("the controller didn't push %s once %s is old enough", greetBranch, tc.raises)
			}
			f.work.Fetch(greetBranch)
			if got := f.work.Show(head, "go.mod"); got != strings.TrimSpace(mod) {
				t.Errorf("go.mod on %s = %q, want %q", greetBranch, got, mod)
			}
		})
	}
}

func TestDoesntPushAnUpdateWhoseRaisedVersionsItCantRead(t *testing.T) {
	const fresh = "example.com/fresh"
	for _, tc := range []struct {
		name string
		// The proxy fails requests for fresh's file.
		file string
		// until is when fresh v1.0.0 is old enough: -min-age after the
		// controller first read fresh's list.
		until time.Time
	}{
		{name: "the proxy fails", file: "list", until: today.Add(144*time.Hour + errorRetry)},
		{name: "the proxy fails to serve the version's time", file: "v1.0.0.info", until: today.Add(144 * time.Hour)},
	} {
		t.Run(tc.name, func(t *testing.T) {
			f := newFixture(t)
			f.u.interval, f.u.minAge = 100*time.Hour, 72*time.Hour
			f.proxy.publish(fresh, "v1.0.0", longAgo, "")
			f.proxy.fail(fresh, tc.file, http.StatusInternalServerError)
			mod := modWith(greet, "v1.1.0", fresh, "v1.0.0")
			f.checkStays("")
			f.clock = today.Add(72 * time.Hour)
			p := f.start()
			f.finish(p, result(withFiles("v1.1.0", "go.mod", mod, "go.sum", sumAt("v1.1.0"))))
			if head := f.srv.Heads(t, "app")[greetBranch]; head != "" {
				t.Fatalf("the controller pushed %s to %s without reading %s's %s", head, greetBranch, fresh, tc.file)
			}
			if rec := f.checkStays(""); rec.RequeueAfter() != errorRetry {
				t.Errorf("RequeueAfter() = %v, want %v", rec.RequeueAfter(), errorRetry)
			}

			t.Log("Once the proxy serves the file, the update waits until fresh v1.0.0 is old enough.")
			f.proxy.fail(fresh, tc.file, 0)
			f.clock = f.clock.Add(errorRetry)
			f.checkStays("")
			f.clock = tc.until.Add(-time.Second)
			f.checkStays("")
			f.clock = tc.until
			p = f.start()
			f.finish(p, result(withFiles("v1.1.0", "go.mod", mod, "go.sum", sumAt("v1.1.0"))))
			if f.srv.Heads(t, "app")[greetBranch] == "" {
				t.Errorf("the controller didn't push %s once %s v1.0.0 is old enough", greetBranch, fresh)
			}
		})
	}
}

func TestFailsAnUpdateThatRaisesAVersionThatNoProxyHas(t *testing.T) {
	const fresh = "example.com/fresh"
	for _, tc := range []struct {
		name string
		// No proxy has fresh's file.
		file string
		// pushed is when the controller pushes greet's update: once it
		// makes the update again and fresh v1.0.0 is old enough.
		pushed time.Time
	}{
		{name: "the module", file: "list", pushed: today.Add(244 * time.Hour)},
		{name: "the version", file: "v1.0.0.info", pushed: today.Add(172 * time.Hour)},
	} {
		t.Run(tc.name, func(t *testing.T) {
			f := newFixture(t)
			f.u.interval, f.u.minAge = 100*time.Hour, 72*time.Hour
			f.proxy.publish(fresh, "v1.0.0", longAgo, "")
			f.proxy.fail(fresh, tc.file, http.StatusNotFound)
			mod := modWith(greet, "v1.1.0", fresh, "v1.0.0")
			f.checkStays("")
			f.clock = today.Add(72 * time.Hour)
			p := f.start()
			f.finish(p, result(withFiles("v1.1.0", "go.mod", mod, "go.sum", sumAt("v1.1.0"))))
			if head := f.srv.Heads(t, "app")[greetBranch]; head != "" {
				t.Fatalf("the controller pushed %s to %s, though no proxy has %s's %s", head, greetBranch, fresh, tc.file)
			}
			if got, want := f.failure("v1.1.0"), "the update raises example.com/fresh to v1.0.0, which no module proxy has"; got != want {
				t.Errorf("the update's failure = %q, want %q", got, want)
			}

			t.Log("The controller starts no Pod for the update until -interval later, even when main moves.")
			if rec := f.checkStays(""); rec.RequeueAfter() != f.u.interval {
				t.Errorf("RequeueAfter() = %v, want %v", rec.RequeueAfter(), f.u.interval)
			}
			f.clock = today.Add(80 * time.Hour)
			f.moveMain("README.md", "# app\n")
			f.checkStays("")
			f.proxy.fail(fresh, tc.file, 0)
			retry := today.Add(172 * time.Hour)
			f.clock = retry.Add(-time.Second)
			f.checkStays("")

			t.Log("Then it makes the update again, and pushes it once fresh v1.0.0 is old enough.")
			f.clock = retry
			p = f.start()
			f.finish(p, result(withFiles("v1.1.0", "go.mod", mod, "go.sum", sumAt("v1.1.0"))))
			if tc.pushed.After(retry) {
				f.checkStays("")
				f.clock = tc.pushed.Add(-time.Second)
				f.checkStays("")
				f.clock = tc.pushed
				p = f.start()
				f.finish(p, result(withFiles("v1.1.0", "go.mod", mod, "go.sum", sumAt("v1.1.0"))))
			}
			if f.srv.Heads(t, "app")[greetBranch] == "" {
				t.Errorf("the controller didn't push %s at %v", greetBranch, tc.pushed.Sub(today))
			}
		})
	}
}

func TestKeepsItsBranchesAfterARestart(t *testing.T) {
	for _, tc := range []struct {
		name string
		// change changes greet's branch after the controller updates greet
		// to v1.1.0, and returns the branch's new head.
		change func(f *fixture, head string) string
		// moved moves main after the restart.
		moved bool
	}{{
		name: "an update",
	}, {
		name: "an update with a fix",
		change: func(f *fixture, head string) string {
			return f.pushFix("app.go", "package app\n\n// fixed\n", agentFix)
		},
	}, {
		name: "an update on an older one",
		change: func(f *fixture, head string) string {
			f.proxy.publish(greet, "v1.2.0", f.clock, "")
			f.work.Branch("work", head)
			f.work.Write("go.mod", modAt("v1.2.0"))
			f.work.Write("go.sum", sumAt("v1.2.0"))
			f.work.Git("add", "-A")
			head = f.commitAs(f.u.cfg.Identity, "Update example.com/greet to v1.2.0\n\nGit-K8s-Deps: go example.com/greet v1.2.0\n", head)
			f.work.Push(greetBranch)
			return head
		},
	}, {
		name:  "an update behind main",
		moved: true,
	}} {
		t.Run(tc.name, func(t *testing.T) {
			f := newFixture(t)
			f.u.interval, f.u.minAge = 100*time.Hour, 72*time.Hour
			f.checkStays("")
			f.clock = f.clock.Add(f.u.minAge)
			head := f.update("v1.1.0")
			if tc.change != nil {
				head = tc.change(f, head)
			}
			f.restart()
			if !tc.moved {
				f.checkStays(head)
				return
			}
			main := f.moveMain("README.md", "# app\n")
			if head := f.update("v1.1.0"); f.work.Git("rev-parse", head+"^") != main {
				t.Errorf("%s = %s, want an update on main at %s", greetBranch, head, main)
			}
		})
	}
}

func TestKeepsFirstSeenTimesAcrossAFailover(t *testing.T) {
	for _, tc := range []struct {
		name      string
		configMap string
		// wait is how long the replica that takes over waits for v1.1.0.
		wait time.Duration
	}{
		{name: "in a ConfigMap", configMap: "first-seen", wait: time.Hour},
		{name: "only in memory", wait: 72 * time.Hour},
	} {
		t.Run(tc.name, func(t *testing.T) {
			inNamespace(t, "git-k8s-deps")
			f := newFixture(t)
			f.u.interval, f.u.minAge, f.u.seenConfigMap = 100*time.Hour, 72*time.Hour, tc.configMap
			stored := kube.Applied[configMap](f.checkStays(""))
			want := f.proxy.URL + " " + greet + " v1.1.0 " + today.Format(time.RFC3339) + "\n"
			switch {
			case tc.configMap == "" && len(stored) != 0:
				t.Fatalf("the controller wrote %d ConfigMaps, want none", len(stored))
			case tc.configMap != "" && (len(stored) != 1 || stored[0].Namespace != "git-k8s-deps" || stored[0].Name != "first-seen" || stored[0].Data[seenData] != want):
				t.Fatalf("written ConfigMaps = %+v, want git-k8s-deps/first-seen with %q", stored, want)
			}
			var world []any
			for _, cm := range stored {
				world = append(world, cm)
			}

			t.Log("Until the times change, the controller doesn't write them again.")
			f.clock = f.clock.Add(time.Hour)
			if n := len(kube.Applied[configMap](f.checkStays("", world...))); n != 0 {
				t.Errorf("the controller wrote %d ConfigMaps, want none", n)
			}

			t.Log("Another replica takes over.")
			f.clock = f.clock.Add(70 * time.Hour)
			f.restart()
			rec := f.checkStays("", world...)
			if rec.RequeueAfter() != tc.wait {
				t.Errorf("RequeueAfter() = %v, want %v", rec.RequeueAfter(), tc.wait)
			}
			if n := len(kube.Applied[configMap](rec)); n != 0 {
				t.Errorf("the replica that took over wrote %d ConfigMaps, want none", n)
			}
			f.clock = f.clock.Add(tc.wait)
			f.update("v1.1.0")
		})
	}
}

func TestWritesFirstSeenTimesOnlyAfterReadingThem(t *testing.T) {
	inNamespace(t, "git-k8s-deps")
	f := newFixture(t)
	f.u.interval, f.u.minAge, f.u.seenConfigMap = 100*time.Hour, 72*time.Hour, "first-seen"
	reads := 0
	var readErr error
	f.u.fetchConfigMap = func(ctx context.Context, namespace, name string) (*configMap, error) {
		reads++
		if readErr != nil {
			return nil, readErr
		}
		return kube.Fetch[configMap](ctx, namespace, name)
	}

	t.Log("When the controller can't read the times, it uses the ones in its memory and doesn't write them.")
	readErr = errors.New(`configmaps "first-seen" is forbidden`)
	rec := f.checkStays("")
	if n := len(kube.Applied[configMap](rec)); reads != 1 || n != 0 || rec.RequeueAfter() != 72*time.Hour {
		t.Errorf("after %d reads, the controller wrote %d ConfigMaps and waits %v, want 1 read, none written, and 72h", reads, n, rec.RequeueAfter())
	}

	t.Log("Once it can read them, it writes the times that it kept in memory.")
	readErr = nil
	f.clock = f.clock.Add(time.Hour)
	rec = f.checkStays("")
	want := f.proxy.URL + " " + greet + " v1.1.0 " + today.Format(time.RFC3339) + "\n"
	if stored := kube.Applied[configMap](rec); len(stored) != 1 || stored[0].Data[seenData] != want || rec.RequeueAfter() != 71*time.Hour {
		t.Errorf("written ConfigMaps = %+v, and the controller waits %v, want %q and 71h", stored, rec.RequeueAfter(), want)
	}

	t.Log("A reconcile of a branch whose modules require nothing doesn't read the times.")
	reads = 0
	f.moveMain("go.mod", "module example.com/app\n\ngo 1.24\n")
	if n := len(kube.Applied[configMap](f.checkStays(""))); reads != 0 || n != 0 {
		t.Errorf("the controller read the times %d times and wrote %d ConfigMaps, want neither", reads, n)
	}
}

func TestWarnsWhenFirstSeenTimesDontFit(t *testing.T) {
	defer func(old int) { maxStored = old }(maxStored)
	inNamespace(t, "git-k8s-deps")
	f := newFixture(t)
	f.u.interval, f.u.minAge, f.u.seenConfigMap = 100*time.Hour, 72*time.Hour, "first-seen"
	f.proxy.publish(greet, "v1.2.0", longAgo, "")
	line := func(v string) string {
		return f.proxy.URL + " " + greet + " " + v + " " + today.Format(time.RFC3339) + "\n"
	}
	maxStored = len(line("v1.1.0"))
	logs := captureLogs(t)
	const warning = "the ConfigMap leaves out the oldest first-seen times"

	t.Log("The controller writes the times that fit, and warns how many it left out.")
	stored := kube.Applied[configMap](f.checkStays(""))
	if len(stored) != 1 || stored[0].Data[seenData] != line("v1.1.0") {
		t.Fatalf("written ConfigMaps = %+v, want one with %q", stored, line("v1.1.0"))
	}
	if !strings.Contains(logs.String(), warning) || !strings.Contains(logs.String(), "configmap=git-k8s-deps/first-seen dropped=1") {
		t.Errorf("logs = %q, want a warning that the ConfigMap left out 1 time", logs)
	}

	t.Log("It warns again while they don't fit, though the ConfigMap already holds the times that do.")
	logs.Reset()
	f.clock = f.clock.Add(time.Hour)
	if n := len(kube.Applied[configMap](f.checkStays("", stored[0]))); n != 0 || !strings.Contains(logs.String(), "dropped=1") {
		t.Errorf("the controller wrote %d ConfigMaps and logged %q, want none written and a warning", n, logs)
	}

	t.Log("Once they fit, it writes them all without a warning.")
	logs.Reset()
	maxStored = 2 * len(line("v1.1.0"))
	if again := kube.Applied[configMap](f.checkStays("", stored[0])); len(again) != 1 || again[0].Data[seenData] != line("v1.1.0")+line("v1.2.0") || strings.Contains(logs.String(), warning) {
		t.Errorf("written ConfigMaps = %+v, and logs = %q, want both times written without a warning", again, logs)
	}
}

func TestWritesFirstSeenTimesAfterTheUpdatePod(t *testing.T) {
	inNamespace(t, "git-k8s-deps")
	f := newFixture(t)
	f.u.interval, f.u.minAge, f.u.seenConfigMap = 100*time.Hour, 72*time.Hour, "first-seen"
	stored := kube.Applied[configMap](f.checkStays(""))
	if len(stored) != 1 {
		t.Fatalf("written ConfigMaps = %d, want 1", len(stored))
	}

	t.Log("Once v1.1.0 is old enough, v1.2.0 comes out, so the reconcile that starts the update Pod also writes the times.")
	f.clock = f.clock.Add(f.u.minAge)
	f.proxy.publish(greet, "v1.2.0", f.clock, "")
	repo, secret := f.srv.Repository("app", f.rules...)
	ctx, rec := kube.Fake(t.Context(), f.b, repo, secret, stored[0])
	podsBefore := -1
	f.u.applyConfigMap = func(ctx context.Context, cm *configMap) {
		podsBefore = len(kube.Owned[agent.Pod](rec))
		kube.Apply(ctx, cm)
	}
	if err := f.u.Reconcile(ctx, f.b); err != nil {
		t.Fatal(err)
	}
	pods, written := kube.Owned[agent.Pod](rec), kube.Applied[configMap](rec)
	if len(pods) != 1 || len(written) != 1 || !strings.Contains(written[0].Data[seenData], " v1.2.0 ") {
		t.Fatalf("the reconcile declared %d Pods and wrote %+v, want 1 Pod and the times with v1.2.0", len(pods), written)
	}
	// kube writes objects in the order that they're declared and stops at
	// an error, so a ConfigMap that it can't write would keep the Pod from
	// starting if the Pod came second.
	if podsBefore != 1 {
		t.Errorf("the reconcile declared %d Pods before it wrote the times, want 1", podsBefore)
	}
}

func TestDeletesABranchWhoseVersionGoesBad(t *testing.T) {
	for _, tc := range []struct {
		name   string
		change func(f *fixture)
	}{{
		name: "a version too young to update to retracts it",
		change: func(f *fixture) {
			f.proxy.publish(greet, "v1.2.0", f.clock, "retract v1.1.0\n")
			f.clock = f.clock.Add(f.u.interval / 2)
		},
	}, {
		name: "main excludes it",
		change: func(f *fixture) {
			f.moveMain("go.mod", modAt("v1.0.0")+"\nexclude example.com/greet v1.1.0\n")
		},
	}} {
		t.Run(tc.name, func(t *testing.T) {
			f := newFixture(t)
			f.u.interval, f.u.minAge = 100*time.Hour, 72*time.Hour
			f.checkStays("")
			f.clock = f.clock.Add(f.u.minAge)
			f.update("v1.1.0")
			tc.change(f)
			f.checkStays("")
		})
	}
}

func TestReplacesABranchWhenANewerVersionComesOut(t *testing.T) {
	f := newFixture(t)
	main := f.b.Spec.Head
	first := f.update("v1.1.0")

	t.Log("v1.2.0 comes out before the branch lands. Once the list of versions expires, the controller replaces the branch.")
	f.proxy.publish(greet, "v1.2.0", longAgo, "")
	f.checkStays(first)
	f.clock = f.clock.Add(f.u.interval / 2)
	second := f.update("v1.2.0")
	if second == first || f.work.Git("rev-parse", second+"^") != main {
		t.Errorf("%s = %s, want a new commit on main", greetBranch, second)
	}
	for name := range f.srv.Heads(t, "app") {
		if strings.HasPrefix(name, "deps/") && name != greetBranch {
			t.Errorf("the controller pushed another branch, %s", name)
		}
	}
}

func TestRemakesABranchBehindItsParent(t *testing.T) {
	f := newFixture(t)
	f.update("v1.1.0")
	main := f.moveMain("README.md", "# app\n")
	head := f.update("v1.1.0")
	if got := f.work.Git("rev-parse", head+"^"); got != main {
		t.Errorf("the update's parent = %s, want main at %s", got, main)
	}
}

func TestBranchesWithFixes(t *testing.T) {
	for _, tc := range []struct {
		name string
		// conflict makes main change the file that the fix changed.
		conflict bool
		limit    int32
		// merge has check-base merge main into the branch.
		merge bool
		kept  bool
	}{
		{name: "merges cleanly", kept: true},
		{name: "has check-base's merge", merge: true, kept: true},
		{name: "conflicts", conflict: true},
		{name: "has no automated commits left", limit: 1},
	} {
		t.Run(tc.name, func(t *testing.T) {
			f := newFixture(t)
			if tc.limit > 0 {
				f.rules[0].Merge.MaxAutomatedCommits = &tc.limit
			}
			f.update("v1.1.0")
			fix := f.pushFix("app.go", "package app\n\n// fixed\n", agentFix)
			main := f.moveMain("README.md", "# app\n")
			if tc.conflict {
				main = f.moveMain("app.go", "package app\n\n// main\n")
			}
			if tc.merge {
				f.work.Branch("work", fix)
				f.work.Git("merge", "--quiet", "--no-ff", "--no-commit", main)
				fix = f.commitAs(checksID, "Merge main into "+greetBranch+"\n\nGit-K8s-Fixer: base\n", fix, main)
				f.work.Push(greetBranch)
			}
			if tc.kept {
				f.checkStays(fix)
				return
			}
			head := f.update("v1.1.0")
			if got := f.work.Git("rev-parse", head+"^"); got != main {
				t.Errorf("the update's parent = %s, want main at %s", got, main)
			}
		})
	}
}

func TestDeletesBranchesWithNoUpdateLeft(t *testing.T) {
	for _, tc := range []struct {
		name   string
		change func(f *fixture, head string)
	}{{
		name: "the update landed",
		change: func(f *fixture, head string) {
			f.work.Branch("main", head)
			f.work.Push("main")
			f.b.Spec.Head = head
		},
	}, {
		name: "main no longer requires the module",
		change: func(f *fixture, head string) {
			f.moveMain("go.mod", "module example.com/app\n\ngo 1.24\n")
		},
	}, {
		name: "the version was retracted",
		change: func(f *fixture, head string) {
			f.proxy.publish(greet, "v1.1.1", longAgo, "retract [v1.1.0, v1.1.1]\n")
			f.clock = f.clock.Add(f.u.interval / 2)
		},
	}} {
		t.Run(tc.name, func(t *testing.T) {
			f := newFixture(t)
			tc.change(f, f.update("v1.1.0"))
			f.checkStays("")
		})
	}
}

func TestLeavesPeoplesBranchesAlone(t *testing.T) {
	t.Run("a commit on the controller's branch", func(t *testing.T) {
		f := newFixture(t)
		f.update("v1.1.0")
		head := f.pushTo(greetBranch, "app.go", "package app\n\n// Greet takes a name.\n", "Make Greet take a name")
		f.proxy.publish(greet, "v1.2.0", longAgo, "")
		f.clock = f.clock.Add(f.u.interval / 2)
		f.checkStays(head)
		f.moveMain("README.md", "# app\n")
		f.checkStays(head)
	})
	t.Run("a branch that a person made", func(t *testing.T) {
		f := newFixture(t)
		f.work.Branch(greetBranch, f.b.Spec.Head)
		f.work.Write("go.mod", modAt("v1.1.0"))
		head := f.work.Commit("Update greet")
		f.work.Push(greetBranch)
		f.checkStays(head)
	})
	for _, tc := range []struct {
		name string
		// change changes greet's branch after the controller updates greet
		// to v1.1.0, and returns the branch's new head.
		change func(f *fixture, update string) string
	}{{
		name: "an update that a person amended",
		change: func(f *fixture, update string) string {
			f.work.Branch("work", update)
			f.work.Write("app.go", "package app\n\n// Greet takes a name.\n")
			f.work.Git("add", "-A")
			f.work.Git("commit", "--quiet", "--amend", "--no-edit")
			f.work.Push(greetBranch)
			return f.work.Git("rev-parse", "HEAD")
		},
	}, {
		name: "a fix that a person squashed with their own",
		change: func(f *fixture, update string) string {
			f.pushFix("app.go", "package app\n\n// fixed\n", agentFix)
			f.pushTo(greetBranch, "app.go", "package app\n\n// fixed by a person\n", "Fix Greet by hand")
			f.work.Git("reset", "--quiet", "--soft", update)
			head := f.work.Commit("Fix Greet by hand\n\n" + agentFix)
			f.work.Push(greetBranch)
			return head
		},
	}, {
		name: "a commit as a check whose trailer isn't at the end",
		change: func(f *fixture, update string) string {
			f.work.Branch("work", update)
			f.work.Write("app.go", "package app\n\n// fixed\n")
			f.work.Git("add", "-A")
			head := f.commitAs(checksID, "Fix Greet\n\nGit-K8s-Fixer: deps\n\nA person wrote this commit.\n", update)
			f.work.Push(greetBranch)
			return head
		},
	}, {
		name: "a commit as the controller without its trailer",
		change: func(f *fixture, update string) string {
			f.work.Branch("work", update)
			f.work.Write("app.go", "package app\n\n// Greet takes a name.\n")
			f.work.Git("add", "-A")
			head := f.commitAs(f.u.cfg.Identity, "Make Greet take a name\n", update)
			f.work.Push(greetBranch)
			return head
		},
	}, {
		name: "a commit as the controller with a longer trailer",
		change: func(f *fixture, update string) string {
			f.work.Branch("work", update)
			f.work.Write("app.go", "package app\n\n// Greet takes a name.\n")
			f.work.Git("add", "-A")
			head := f.commitAs(f.u.cfg.Identity, "Make Greet take a name\n\nGit-K8s-Depsx: go example.com/greet v1.1.0\n", update)
			f.work.Push(greetBranch)
			return head
		},
	}, {
		name: "a commit as the controller with a trailer that ends in its trailer's name",
		change: func(f *fixture, update string) string {
			f.work.Branch("work", update)
			f.work.Write("app.go", "package app\n\n// Greet takes a name.\n")
			f.work.Git("add", "-A")
			head := f.commitAs(f.u.cfg.Identity, "Make Greet take a name\n\nX-Git-K8s-Deps: go example.com/greet v1.1.0\n", update)
			f.work.Push(greetBranch)
			return head
		},
	}} {
		t.Run(tc.name, func(t *testing.T) {
			f := newFixture(t)
			head := tc.change(f, f.update("v1.1.0"))
			f.proxy.publish(greet, "v1.2.0", longAgo, "")
			f.clock = f.clock.Add(f.u.interval / 2)
			f.checkStays(head)
			f.moveMain("README.md", "# app\n")
			f.checkStays(head)
		})
	}
}

func TestLeavesBranchesWithTooManyCommitsAlone(t *testing.T) {
	for _, tc := range []struct {
		fixes int
		owned bool
	}{{fixes: maxOwned - 1, owned: true}, {fixes: maxOwned}} {
		t.Run(strconv.Itoa(tc.fixes)+" fixes", func(t *testing.T) {
			f := newFixture(t)
			head := f.update("v1.1.0")
			f.work.Branch("work", head)
			for i := range tc.fixes {
				head = f.commitAs(checksID, "Fix "+strconv.Itoa(i)+"\n\nGit-K8s-Fixer: gofmt\n", head)
			}
			f.work.Push(greetBranch)
			f.moveMain("README.md", "# app\n")
			if tc.owned {
				f.update("v1.1.0")
				return
			}
			f.checkStays(head)
		})
	}
}

func TestComparesIdentitiesAsGitWritesThem(t *testing.T) {
	f := newFixture(t)
	f.u.cfg.Identity.Email = " <deps@example.com>"
	f.u.checkEmail = checksID.Email + "\n"
	f.update("v1.1.0")
	f.pushFix("app.go", "package app\n\n// fixed\n", agentFix)
	main := f.moveMain("app.go", "package app\n\n// main\n")
	if head := f.update("v1.1.0"); f.work.Git("rev-parse", head+"^") != main {
		t.Errorf("%s = %s, want an update on main at %s", greetBranch, head, main)
	}
}

func TestSkipsModulesThatAnEarlierRuleClaims(t *testing.T) {
	for _, claim := range []gitk8s.BranchRule{
		{Match: "deps/go/example.com/greet@*"},
		{Match: "deps/go/example.com/**", Parent: "release"},
	} {
		f := newFixture(t)
		f.rules = []gitk8s.BranchRule{f.rules[0], claim, f.rules[1]}
		f.checkStays("")
	}
}

func TestDoesntPushWhatAPodGetsWrong(t *testing.T) {
	for _, tc := range []struct {
		name   string
		result []byte
		// status makes the Pod fail instead of serving result.
		status func(p *agent.Pod)
		// age is how old the Pod is when it reports status.
		age    time.Duration
		digest string
		// want is part of why the update failed, if the case checks it.
		want string
	}{
		{name: "go fails", result: result(updateJSON{Module: greet, Version: "v1.1.0", Output: []byte("go: example.com/greet@v1.1.0: missing go.sum entry\n")})},
		{name: "another version", result: result(withFiles("v1.1.0", "go.mod", modAt("v1.0.0")))},
		{name: "a new replace directive", result: result(withFiles("v1.1.0", "go.mod", modAt("v1.1.0")+"\nreplace example.com/greet => ../greet\n"))},
		{name: "another module path", result: result(withFiles("v1.1.0", "go.mod", strings.Replace(modAt("v1.1.0"), "example.com/app", "example.com/other", 1)))},
		{name: "a go.mod file that doesn't parse", result: result(withFiles("v1.1.0", "go.mod", "module example.com/app\nrequire (\n"))},
		{name: "another file", result: result(withFiles("v1.1.0", "go.mod", modAt("v1.1.0"), "app.go", "package app\n\n// oops\n"))},
		{name: "a path outside the directory", result: result(withFiles("v1.1.0", "go.mod", modAt("v1.1.0"), "tools/../go.sum", sumAt("v1.1.0")))},
		{name: "no go.mod file", result: result(withFiles("v1.1.0", "go.sum", sumAt("v1.1.0")))},
		{name: "an update that wasn't asked for", result: result(updated("v1.1.0"), updateJSON{Module: "example.com/other", Version: "v1.0.0"})},
		{name: "no update", result: result()},
		{name: "JSON that doesn't parse", result: []byte(`{"updates":[`)},
		{name: "another digest", result: result(updated("v1.1.0")), digest: "sha256:" + strings.Repeat("0", 64)},
		{name: "the source doesn't check out", status: func(p *agent.Pod) {
			p.Status = agent.PodStatus{Phase: "Failed", InitContainerStatuses: []agent.ContainerStatus{
				{Name: "prepare", State: terminated(&agent.Terminated{ExitCode: 3, Message: "main no longer points to 0123abcd"})},
			}}
		}},
		{name: "the update container fails", status: func(p *agent.Pod) {
			p.Status = agent.PodStatus{Phase: "Failed", InitContainerStatuses: []agent.ContainerStatus{
				{Name: "prepare", State: terminated(&agent.Terminated{Reason: "Completed"})},
				{Name: "update", State: terminated(&agent.Terminated{ExitCode: 137, Reason: "OOMKilled"})},
			}}
		}},
		{name: "the Pod runs out of time", status: func(p *agent.Pod) {
			p.Status = agent.PodStatus{Phase: "Failed", Reason: "DeadlineExceeded", InitContainerStatuses: []agent.ContainerStatus{
				{Name: "prepare", State: terminated(&agent.Terminated{Reason: "Completed"})},
				{Name: "update", State: agent.ContainerState{Running: &struct{}{}}},
			}}
		}},
		{name: "the result container stops", status: func(p *agent.Pod) {
			finished(p, "sha256:"+strings.Repeat("0", 64))
			p.Status.ContainerStatuses[0].State = terminated(&agent.Terminated{ExitCode: 1})
		}},
		{name: "the repository's Secret doesn't exist", status: func(p *agent.Pod) {
			p.Status = agent.PodStatus{Phase: "Pending", InitContainerStatuses: []agent.ContainerStatus{
				{Name: "prepare", State: agent.ContainerState{Waiting: &agent.Waiting{Reason: "CreateContainerConfigError", Message: `secret "app-creds" not found`}}},
			}}
		}, age: stuckAfter, want: `couldn't start in 5 minutes: container prepare is waiting: CreateContainerConfigError: secret "app-creds" not found`},
		{name: "the go image can't be pulled", status: func(p *agent.Pod) {
			p.Status = agent.PodStatus{Phase: "Pending", InitContainerStatuses: []agent.ContainerStatus{
				{Name: "prepare", State: terminated(&agent.Terminated{Reason: "Completed"})},
				{Name: "update", State: agent.ContainerState{Waiting: &agent.Waiting{Reason: "ImagePullBackOff"}}},
			}}
		}, age: stuckAfter, want: "couldn't start in 5 minutes: container update is waiting: ImagePullBackOff"},
		{name: "the result image can't be pulled", status: func(p *agent.Pod) {
			finished(p, "sha256:"+strings.Repeat("0", 64))
			p.Status.ContainerStatuses[0].State = agent.ContainerState{Waiting: &agent.Waiting{Reason: "ErrImagePull"}}
		}, age: stuckAfter, want: "couldn't start in 5 minutes: container result is waiting: ErrImagePull"},
		{name: "the go image's name isn't valid", status: func(p *agent.Pod) {
			p.Status = agent.PodStatus{Phase: "Pending", InitContainerStatuses: []agent.ContainerStatus{
				{Name: "prepare", State: terminated(&agent.Terminated{Reason: "Completed"})},
				{Name: "update", State: agent.ContainerState{Waiting: &agent.Waiting{Reason: "InvalidImageName", Message: `Failed to apply default image tag "go:": couldn't parse image name`}}},
			}}
		}, want: `can't start: container update is waiting: InvalidImageName: Failed to apply default image tag "go:": couldn't parse image name`},
		{name: "go fills the cache volume", status: func(p *agent.Pod) {
			p.Status = agent.PodStatus{Phase: "Failed", Reason: "Evicted", Message: `Usage of EmptyDir volume "tmp" exceeds the limit "4Gi". `, InitContainerStatuses: []agent.ContainerStatus{
				{Name: "prepare", State: terminated(&agent.Terminated{Reason: "Completed"})},
				{Name: "update", State: terminated(&agent.Terminated{ExitCode: 137, Reason: "Error"})},
			}}
		}, want: `was evicted: Usage of EmptyDir volume "tmp" exceeds the limit "4Gi".`},
		{name: "the Pod is evicted before the result is fetched", status: func(p *agent.Pod) {
			finished(p, "sha256:"+strings.Repeat("0", 64))
			p.Status.Phase, p.Status.Reason = "Failed", "Evicted"
			p.Status.Message = "Pod ephemeral local storage usage exceeds the total limit of containers 6464Mi. "
		}, want: "was evicted: Pod ephemeral local storage usage exceeds the total limit of containers 6464Mi."},
	} {
		t.Run(tc.name, func(t *testing.T) {
			f := newFixture(t)
			p := f.start()
			digest := f.serve(tc.result, p.UID)
			switch {
			case tc.status != nil:
				tc.status(p)
			case tc.digest != "":
				finished(p, tc.digest)
			default:
				finished(p, digest)
			}
			f.clock = f.clock.Add(tc.age)
			if rec := f.checkBranch("", p); rec.RequeueAfter() != time.Second {
				t.Errorf("RequeueAfter() = %v, want 1s, to stop declaring the Pod", rec.RequeueAfter())
			}
			if got := f.failure("v1.1.0"); got == "" || !strings.Contains(got, tc.want) {
				t.Errorf("the update failed with %q, want %q", got, tc.want)
			}

			t.Log("Until -interval passes, the controller doesn't try again.")
			if rec := f.checkStays("", p); rec.RequeueAfter() != f.u.interval {
				t.Errorf("RequeueAfter() = %v, want the interval", rec.RequeueAfter())
			}
			f.clock = f.clock.Add(f.u.interval - time.Second)
			if rec := f.checkStays(""); rec.RequeueAfter() != time.Second {
				t.Errorf("RequeueAfter() = %v, want 1s", rec.RequeueAfter())
			}
			f.clock = f.clock.Add(time.Second)
			if again := f.start(); again.Name == p.Name {
				t.Errorf("trying again starts Pod %s again, want a new Pod", p.Name)
			}
		})
	}
}

func TestGivesAStuckPodTime(t *testing.T) {
	for _, reason := range []string{"CreateContainerConfigError", "ErrImagePull", "ImagePullBackOff"} {
		t.Run(reason, func(t *testing.T) {
			f := newFixture(t)
			p := f.start()
			p.Status = agent.PodStatus{Phase: "Pending", InitContainerStatuses: []agent.ContainerStatus{
				{Name: "prepare", State: agent.ContainerState{Waiting: &agent.Waiting{Reason: reason, Message: "not yet"}}},
			}}
			f.clock = f.clock.Add(stuckAfter - time.Minute)
			rec := f.checkBranch("", p)
			if pods := kube.Owned[agent.Pod](rec); len(pods) != 1 || pods[0].Name != p.Name {
				t.Errorf("owned Pods = %d, want Pod %s", len(pods), p.Name)
			}
			if got := f.failure("v1.1.0"); got != "" {
				t.Errorf("the update failed before its Pod was %v old: %s", stuckAfter, got)
			}
			if d := rec.RequeueAfter(); d != time.Minute {
				t.Errorf("RequeueAfter() = %v, want 1m, when the Pod is %v old", d, stuckAfter)
			}

			f.clock = f.clock.Add(time.Minute)
			if rec := f.checkBranch("", p); rec.RequeueAfter() != time.Second {
				t.Errorf("RequeueAfter() = %v, want 1s, to stop declaring the Pod", rec.RequeueAfter())
			}
			want := "Pod " + p.Name + " couldn't start in 5 minutes: container prepare is waiting: " + reason + ": not yet"
			if got := f.failure("v1.1.0"); got != want {
				t.Errorf("the update failed with %q, want %q", got, want)
			}
		})
	}
}

func TestFailsAPodThatCantBeScheduled(t *testing.T) {
	f := newFixture(t)
	p := f.start()
	why := "0/3 nodes are available: 3 Insufficient ephemeral-storage."
	p.Status = agent.PodStatus{Phase: "Pending", Conditions: []agent.PodCondition{{Type: "PodScheduled", Status: "False", Reason: "Unschedulable", Message: why}}}
	f.clock = f.clock.Add(time.Minute)
	rec := f.checkBranch("", p)
	if pods := kube.Owned[agent.Pod](rec); len(pods) != 1 || pods[0].Name != p.Name {
		t.Errorf("owned Pods = %d, want Pod %s", len(pods), p.Name)
	}
	if got := f.failure("v1.1.0"); got != "" {
		t.Errorf("the update failed a minute after kube created its Pod: %s", got)
	}
	if d := rec.RequeueAfter(); d != stuckAfter-time.Minute {
		t.Errorf("RequeueAfter() = %v, want a reconcile when the Pod is %v old", d, stuckAfter)
	}

	t.Log("A scheduled Pod that's still pending isn't stuck.")
	f.clock = f.clock.Add(stuckAfter)
	p.Status.Conditions[0].Status = "True"
	if pods := kube.Owned[agent.Pod](f.checkBranch("", p)); len(pods) != 1 {
		t.Errorf("owned Pods = %d, want 1", len(pods))
	}
	if got := f.failure("v1.1.0"); got != "" {
		t.Errorf("the update of a scheduled Pod failed: %s", got)
	}

	t.Log("Once a Pod that isn't scheduled is stuckAfter old, its updates fail, and the next reconcile doesn't declare it, so kube deletes it and frees its place in -max-pods.")
	p.Status.Conditions[0].Status = "False"
	if rec := f.checkBranch("", p); rec.RequeueAfter() != time.Second {
		t.Errorf("RequeueAfter() = %v, want 1s, to stop declaring the Pod", rec.RequeueAfter())
	}
	if got, want := f.failure("v1.1.0"), "Pod "+p.Name+" couldn't be scheduled in 5 minutes: "+why; got != want {
		t.Errorf("the update failed with %q, want %q", got, want)
	}
	f.checkStays("", p)
}

func TestCountsTheGraceFromWhenAContainerCanStart(t *testing.T) {
	pull := func(name string) agent.ContainerStatus {
		return agent.ContainerStatus{Name: name, State: agent.ContainerState{Waiting: &agent.Waiting{Reason: "ErrImagePull", Message: "unexpected status code 503 Service Unavailable"}}}
	}
	done := func(name string, at time.Time) agent.ContainerStatus {
		return agent.ContainerStatus{Name: name, State: terminated(&agent.Terminated{Reason: "Completed", FinishedAt: at})}
	}
	for _, tc := range []struct {
		name   string
		status agent.PodStatus
		// left is how long the container has before the updates fail, or 0
		// if they fail now.
		left time.Duration
	}{{
		name:   "prepare in a Pod that waited for a node",
		status: agent.PodStatus{Phase: "Pending", StartTime: today.Add(-30 * time.Second), InitContainerStatuses: []agent.ContainerStatus{pull("prepare")}},
		left:   stuckAfter - 30*time.Second,
	}, {
		name:   "prepare in a Pod that started long ago",
		status: agent.PodStatus{Phase: "Pending", StartTime: today.Add(-stuckAfter), InitContainerStatuses: []agent.ContainerStatus{pull("prepare")}},
	}, {
		name:   "update after prepare finished",
		status: agent.PodStatus{Phase: "Pending", StartTime: today.Add(-9 * time.Minute), InitContainerStatuses: []agent.ContainerStatus{done("prepare", today.Add(-time.Minute)), pull("update")}},
		left:   stuckAfter - time.Minute,
	}, {
		name:   "update long after prepare finished",
		status: agent.PodStatus{Phase: "Pending", StartTime: today.Add(-9 * time.Minute), InitContainerStatuses: []agent.ContainerStatus{done("prepare", today.Add(-stuckAfter)), pull("update")}},
	}, {
		name: "result after update finished",
		status: agent.PodStatus{Phase: "Pending", StartTime: today.Add(-9 * time.Minute),
			InitContainerStatuses: []agent.ContainerStatus{done("prepare", today.Add(-8*time.Minute)), done("update", today.Add(-2*time.Minute))},
			ContainerStatuses:     []agent.ContainerStatus{pull("result")}},
		left: stuckAfter - 2*time.Minute,
	}} {
		t.Run(tc.name, func(t *testing.T) {
			f := newFixture(t)
			p := f.start()
			p.CreationTimestamp = today.Add(-10 * time.Minute)
			p.Status = tc.status
			rec := f.checkBranch("", p)
			got, d := f.failure("v1.1.0"), rec.RequeueAfter()
			switch {
			case tc.left == 0 && !strings.Contains(got, "couldn't start in 5 minutes"):
				t.Errorf("the update failed with %q, want it to fail", got)
			case tc.left > 0 && (got != "" || d != tc.left):
				t.Errorf("the update failed with %q and RequeueAfter() = %v, want no failure and a reconcile in %v", got, d, tc.left)
			}
		})
	}
}

func TestCheckResult(t *testing.T) {
	const parent = `module example.com/app

go 1.24

require example.com/greet v1.0.0

replace (
	example.com/z => ./z
	example.com/b v1.0.0 => example.com/fork v1.0.1
)

exclude (
	example.com/greet v0.9.0
	example.com/greet v0.8.0
	example.com/greet v0.9.0
)

retract (
	[v0.2.0, v0.3.0]
	v1.0.1 // Published by mistake.
)

tool (
	example.com/z/cmd/z
	example.com/b/cmd/b
)

godebug (
	panicnil=1
	asynctimerchan=1
)

ignore (
	./web
	./dist
)
`
	// updated is parent as go get example.com/greet@v1.1.0 writes it, with
	// each block sorted and the repeated exclude directive dropped.
	const updated = `module example.com/app

go 1.24

require example.com/greet v1.1.0

replace (
	example.com/b v1.0.0 => example.com/fork v1.0.1
	example.com/z => ./z
)

exclude (
	example.com/greet v0.8.0
	example.com/greet v0.9.0
)

retract (
	v1.0.1 // Published by mistake.
	[v0.2.0, v0.3.0]
)

tool (
	example.com/b/cmd/b
	example.com/z/cmd/z
)

godebug (
	asynctimerchan=1
	panicnil=1
)

ignore (
	./dist
	./web
)
`
	f, err := modfile.Parse("go.mod", []byte(parent), nil)
	if err != nil {
		t.Fatal(err)
	}
	mods := map[string]*modFile{".": {data: []byte(parent), file: f}}
	up := update{module: greet, version: "v1.1.0", from: map[string]string{".": "v1.0.0"}}
	for _, tc := range []struct {
		name, old, new string
		// want is the error, or empty when checkResult accepts the file.
		want string
	}{
		{name: "sorted blocks"},
		{name: "module path", old: "module example.com/app", new: "module example.com/other", want: "go.mod changes the module path"},
		{name: "requirement", old: "greet v1.1.0", new: "greet v1.0.0", want: "go.mod doesn't require example.com/greet v1.1.0"},
		{name: "replace", old: "example.com/z => ./z", new: "example.com/z => ../z", want: "go.mod changes replace directives"},
		{name: "dropped replace", old: "\texample.com/z => ./z\n", want: "go.mod changes replace directives"},
		{name: "exclude", old: "greet v0.8.0", new: "greet v0.7.0", want: "go.mod changes exclude directives"},
		{name: "retract", old: "[v0.2.0, v0.3.0]", new: "[v0.2.0, v0.4.0]", want: "go.mod changes retract directives"},
		{name: "retract rationale", old: "// Published by mistake.", new: "// Fine.", want: "go.mod changes retract directives"},
		{name: "tool", old: "example.com/z/cmd/z", new: "example.com/z/cmd/zz", want: "go.mod changes tool directives"},
		{name: "added tool", old: "\texample.com/z/cmd/z\n", new: "\texample.com/z/cmd/z\n\texample.com/y/cmd/y\n", want: "go.mod changes tool directives"},
		{name: "godebug", old: "panicnil=1", new: "panicnil=0", want: "go.mod changes godebug directives"},
		{name: "ignore", old: "./dist", new: "./build", want: "go.mod changes ignore directives"},
	} {
		t.Run(tc.name, func(t *testing.T) {
			files := map[string][]byte{"go.mod": []byte(strings.Replace(updated, tc.old, tc.new, 1))}
			got := ""
			if err := checkResult(mods, up, files); err != nil {
				got = err.Error()
			}
			if got != tc.want {
				t.Errorf("checkResult() = %q, want %q", got, tc.want)
			}
		})
	}
}

func TestRaised(t *testing.T) {
	file := func(path string, reqs ...string) string {
		s := "module " + path + "\n\ngo 1.24\n\nrequire (\n"
		for _, r := range reqs {
			s += "\t" + r + "\n"
		}
		return s + ")\n\nreplace example.com/forked => ./forked\n\nreplace example.com/pinned v1.3.0 => ./pinned\n"
	}
	parse := func(path, data string) *modFile {
		f, err := modfile.Parse(path, []byte(data), nil)
		if err != nil {
			t.Fatal(err)
		}
		return &modFile{data: []byte(data), file: f}
	}
	mods := map[string]*modFile{
		".":     parse("go.mod", file("example.com/app", "example.com/greet v1.0.0", "example.com/other v1.2.0", "example.com/low v1.0.0 // indirect")),
		"tools": parse("tools/go.mod", file("example.com/app/tools", "example.com/greet v1.0.0")),
	}
	up := update{module: greet, version: "v1.1.0", from: map[string]string{".": "v1.0.0", "tools": "v1.0.0"}}
	v := func(path, version string) module.Version { return module.Version{Path: path, Version: version} }
	for _, tc := range []struct {
		name string
		// root and tools are the requirements other than greet in the
		// update's go.mod files.
		root, tools []string
		want        []module.Version
	}{
		{name: "none", root: []string{"example.com/other v1.2.0", "example.com/low v1.0.0 // indirect"}},
		{name: "a direct requirement", root: []string{"example.com/other v1.3.0"}, want: []module.Version{v("example.com/other", "v1.3.0")}},
		{name: "an indirect requirement", root: []string{"example.com/low v1.1.0 // indirect"}, want: []module.Version{v("example.com/low", "v1.1.0")}},
		{name: "a new module", root: []string{"example.com/fresh v0.1.0 // indirect"}, want: []module.Version{v("example.com/fresh", "v0.1.0")}},
		{name: "a lower version", root: []string{"example.com/other v1.1.0"}},
		{name: "a replaced module", root: []string{"example.com/forked v1.9.0"}},
		{name: "a version that a replace directive names", root: []string{"example.com/pinned v1.3.0"}},
		{name: "a version that no replace directive names", root: []string{"example.com/pinned v1.4.0"}, want: []module.Version{v("example.com/pinned", "v1.4.0")}},
		{name: "a module that only another go.mod file requires", tools: []string{"example.com/other v1.2.0"}, want: []module.Version{v("example.com/other", "v1.2.0")}},
		{name: "a version in two go.mod files", root: []string{"example.com/other v1.3.0"}, tools: []string{"example.com/other v1.3.0"}, want: []module.Version{v("example.com/other", "v1.3.0")}},
	} {
		t.Run(tc.name, func(t *testing.T) {
			files := map[string][]byte{
				"go.mod":       []byte(file("example.com/app", append([]string{"example.com/greet v1.1.0"}, tc.root...)...)),
				"go.sum":       []byte("example.com/sum v9.0.0 h1:x=\n"),
				"tools/go.mod": []byte(file("example.com/app/tools", append([]string{"example.com/greet v1.1.0"}, tc.tools...)...)),
			}
			if got := raised(mods, up, files); !slices.Equal(got, tc.want) {
				t.Errorf("raised() = %v, want %v", got, tc.want)
			}
		})
	}
}

// TestStartsANewPodOnceAnUpdateHasWaited checks that an update that waited
// for the versions that it raises doesn't read the result of its first Pod
// again, which may have stopped.
func TestStartsANewPodOnceAnUpdateHasWaited(t *testing.T) {
	const fresh = "example.com/fresh"
	f := newFixture(t)
	f.u.interval, f.u.minAge = 100*time.Hour, 72*time.Hour
	f.proxy.publish(fresh, "v1.0.0", longAgo, "")
	mod := modWith(greet, "v1.1.0", fresh, "v1.0.0")
	f.checkStays("")
	f.clock = today.Add(72 * time.Hour)
	first := f.start()
	f.finish(first, result(withFiles("v1.1.0", "go.mod", mod)))

	t.Log("When the wait is over, the first Pod is still there, and its result container has stopped.")
	f.clock = today.Add(144 * time.Hour)
	first.Status.Phase = "Succeeded"
	first.Status.ContainerStatuses = []agent.ContainerStatus{{Name: "result", State: terminated(&agent.Terminated{Reason: "Completed"})}}
	p := f.start(first)
	if p.Name == first.Name || f.failure("v1.1.0") != "" {
		t.Fatalf("the controller declared Pod %s again and recorded %q, want a new Pod", p.Name, f.failure("v1.1.0"))
	}
	f.finish(p, result(withFiles("v1.1.0", "go.mod", mod)))
	if f.srv.Heads(t, "app")[greetBranch] == "" {
		t.Errorf("the controller didn't push %s", greetBranch)
	}
}

func TestRefusesAnUpdateThatRaisesARequirementToARetractedVersion(t *testing.T) {
	const other = "example.com/other"
	f := newFixture(t)
	f.u.interval = 100 * time.Hour
	f.proxy.publish(other, "v1.5.0", longAgo, "")
	f.proxy.publish(other, "v1.6.0", longAgo, "retract v1.5.0 // Corrupts data.\n")
	p := f.start()
	f.finish(p, result(withFiles("v1.1.0", "go.mod", modWith(greet, "v1.1.0", other, "v1.5.0"))))
	if head := f.srv.Heads(t, "app")[greetBranch]; head != "" {
		t.Errorf("the controller pushed %s to %s, want no push", greetBranch, head)
	}
	if got, want := f.failure("v1.1.0"), "the update raises example.com/other to v1.5.0, which the module retracts"; got != want {
		t.Errorf("the update failed with %q, want %q", got, want)
	}

	t.Log("After -interval, the controller tries again, and pushes an update that raises other past the retraction.")
	f.clock = f.clock.Add(f.u.interval - time.Second)
	f.checkStays("")
	f.clock = f.clock.Add(time.Second)
	p = f.start()
	f.finish(p, result(withFiles("v1.1.0", "go.mod", modWith(greet, "v1.1.0", other, "v1.6.0"))))
	if f.srv.Heads(t, "app")[greetBranch] == "" {
		t.Errorf("the controller didn't push %s", greetBranch)
	}
}

func TestDeletesABranchThatRaisesARetractedVersion(t *testing.T) {
	const other = "example.com/other"
	for _, tc := range []struct {
		name string
		// pushed is the go.mod file on greet's branch, which the controller
		// pushes before other retracts v1.5.0.
		pushed string
		// again makes the controller make an update to version again.
		again   func(f *fixture)
		version string
		deleted bool
	}{{
		name:    "main moves, and the branch raises the retracted version",
		pushed:  modWith(greet, "v1.1.0", other, "v1.5.0"),
		again:   func(f *fixture) { f.moveMain("README.md", "# app\n") },
		version: "v1.1.0",
		deleted: true,
	}, {
		name:    "a newer version comes out, and the branch raises no retracted version",
		pushed:  modAt("v1.1.0"),
		again:   func(f *fixture) { f.proxy.publish(greet, "v1.2.0", longAgo, "") },
		version: "v1.2.0",
	}} {
		t.Run(tc.name, func(t *testing.T) {
			f := newFixture(t)
			f.u.interval = 100 * time.Hour
			f.proxy.publish(other, "v1.5.0", longAgo, "")
			p := f.start()
			f.finish(p, result(withFiles("v1.1.0", "go.mod", tc.pushed)))
			head := f.srv.Heads(t, "app")[greetBranch]
			if head == "" {
				t.Fatalf("the controller didn't push %s", greetBranch)
			}

			t.Log("other v1.6.0 retracts v1.5.0. Once the lists of versions expire, the update that the controller makes again raises other to v1.5.0.")
			logs := captureLogs(t)
			f.proxy.publish(other, "v1.6.0", longAgo, "retract v1.5.0\n")
			tc.again(f)
			f.clock = f.clock.Add(f.u.interval / 2)
			p = f.start()
			f.finish(p, result(withFiles(tc.version, "go.mod", modWith(greet, tc.version, other, "v1.5.0"))))
			if got, want := f.failure(tc.version), "the update raises example.com/other to v1.5.0, which the module retracts"; got != want {
				t.Errorf("the update failed with %q, want %q", got, want)
			}
			want := head
			if tc.deleted {
				want = ""
			}
			if got := f.srv.Heads(t, "app")[greetBranch]; got != want {
				t.Errorf("%s = %q, want %q", greetBranch, got, want)
			}
			if logged := strings.Contains(logs.String(), "deleted a branch that raises a requirement to a version that its module retracts"); logged != tc.deleted {
				t.Errorf("logs = %q, want the deletion logged: %v", logs, tc.deleted)
			}
		})
	}
}

func TestWaitsForFreePods(t *testing.T) {
	f := newFixture(t)
	f.u.maxPods = 2
	var others []any
	for i, phase := range []string{"Running", "Pending", "Succeeded", "Failed"} {
		p := &agent.Pod{Object: kube.Meta("gitk8sdeps"+strconv.Itoa(i), podLabels)}
		p.Namespace = "other"
		p.Status.Phase = phase
		others = append(others, p)
	}
	if rec := f.checkStays("", others...); rec.RequeueAfter() != time.Minute {
		t.Errorf("RequeueAfter() = %v, want 1m", rec.RequeueAfter())
	}
	f.u.maxPods = 3
	f.start(others...)
}

func TestUpdatesEveryGoModFile(t *testing.T) {
	f := newFixture(t)
	rootMod := `module example.com/app

go 1.24

require (
	example.com/greet v1.0.0
	example.com/indirect v1.0.0 // indirect
	example.com/other v1.0.0
	example.com/replaced v1.0.0
)

replace example.com/replaced => ./replaced

exclude example.com/other v1.1.0
`
	f.work.Write("go.mod", rootMod)
	f.work.Write("tools/go.mod", "module example.com/app/tools\n\ngo 1.24\n\nrequire example.com/greet v1.0.0\n")
	f.work.Write("old/go.mod", "module example.com/app/old\n\ngo 1.24\n\nrequire example.com/greet v1.1.0\n")
	for _, dir := range []string{"vendored", "testdata/x", "bad dir", "-x", "broken", "nomodule"} {
		f.work.Write(dir+"/go.mod", "module example.com/app/x\n\nrequire example.com/greet v1.0.0\n")
	}
	f.work.Write("vendored/vendor/modules.txt", "# example.com/greet v1.0.0\n")
	f.work.Write("broken/go.mod", "module example.com/app/broken\n\nrequire (\n")
	f.work.Write("nomodule/go.mod", "go 1.24\n")
	f.work.Write("go116/go.mod", "module example.com/app/go116\n\ngo 1.16\n\nrequire example.com/greet v1.0.0\n")
	f.work.Write("nogo/go.mod", "module example.com/app/nogo\n\nrequire example.com/greet v1.0.0\n")
	logs := captureLogs(t)
	f.b.Spec.Head = f.work.Commit("modules")
	f.work.Push("main")
	for _, v := range []string{"v1.0.0", "v1.0.1", "v1.1.0"} {
		f.proxy.publish("example.com/other", v, longAgo, "")
	}
	f.proxy.publish("example.com/indirect", "v1.1.0", longAgo, "")
	f.proxy.publish("example.com/replaced", "v1.1.0", longAgo, "")

	p := f.start()
	want := "example.com/greet v1.1.0 . nogo tools\nexample.com/other v1.0.1 .\n"
	if got := env(p.Spec.InitContainers[1], "UPDATES"); got != want {
		t.Errorf("UPDATES = %q, want %q", got, want)
	}
	for _, m := range []string{"example.com/indirect", "example.com/replaced"} {
		if n := f.proxy.hitsOf(m, "list"); n != 0 {
			t.Errorf("the controller read the versions of %s, want it skipped", m)
		}
	}
	if !slices.ContainsFunc(strings.Split(logs.String(), "\n"), func(l string) bool {
		return strings.Contains(l, "whose go line is older than 1.17") && strings.HasSuffix(l, " path=go116/go.mod")
	}) || strings.Contains(logs.String(), "path=nogo/go.mod") {
		t.Errorf("the controller didn't warn that it skips go116/go.mod, or warned about nogo/go.mod, which has no go line; logs:\n%s", logs)
	}

	t.Log("The branch updates the three files in one commit; old/go.mod already requires v1.1.0, and go get adds a go line to nogo/go.mod.")
	toolsMod := "module example.com/app/tools\n\ngo 1.24\n\nrequire example.com/greet v1.1.0\n"
	nogoMod := "module example.com/app/nogo\n\ngo 1.26.0\n\nrequire example.com/greet v1.1.0\n"
	f.finish(p, result(
		withFiles("v1.1.0", "go.mod", strings.Replace(rootMod, "greet v1.0.0", "greet v1.1.0", 1), "nogo/go.mod", nogoMod, "tools/go.mod", toolsMod),
		updateJSON{Module: "example.com/other", Version: "v1.0.1", Output: []byte("no")},
	))
	heads := f.srv.Heads(t, "app")
	head := heads[greetBranch]
	if head == "" || heads["deps/go/example.com/other@v1"] != "" {
		t.Fatalf("heads = %v, want only %s", heads, greetBranch)
	}
	f.work.Fetch(greetBranch)
	msg := "Update example.com/greet to v1.1.0\n\n" +
		"Update example.com/greet from v1.0.0 to v1.1.0 in go.mod.\n" +
		"Update example.com/greet from v1.0.0 to v1.1.0 in nogo/go.mod.\n" +
		"Update example.com/greet from v1.0.0 to v1.1.0 in tools/go.mod.\n\n" +
		"Git-K8s-Deps: go example.com/greet v1.1.0"
	if got := f.work.Git("log", "-1", "--format=%B", head); got != msg {
		t.Errorf("the update's message = %q, want %q", got, msg)
	}
	if got := f.work.Show(head, "tools/go.mod"); got != strings.TrimSpace(toolsMod) {
		t.Errorf("tools/go.mod = %q, want greet at v1.1.0", got)
	}
	if got := f.work.Show(head, "nogo/go.mod"); got != strings.TrimSpace(nogoMod) {
		t.Errorf("nogo/go.mod = %q, want greet at v1.1.0", got)
	}
}

func TestRefusesToPushOtherBranches(t *testing.T) {
	u := &updater{prefix: "deps/"}
	for _, branch := range []string{"main", "deps", "deps/../main", "deps/go/x@v1.lock", "deps-x/go"} {
		if err := u.push(t.Context(), nil, git.Remote{}, branch, "0123abcd", ""); err == nil {
			t.Errorf("push(%q) = nil, want an error", branch)
		}
	}
}

func TestSafeDir(t *testing.T) {
	for dir, want := range map[string]bool{
		".": true, "tools": true, "a/b-c/d_e.f": true,
		"": false, "a//b": false, "./a": false, "a/..": false, "-a": false, "a b": false, "a/$(x)": false, "a\"b": false,
	} {
		if got := safeDir(dir); got != want {
			t.Errorf("safeDir(%q) = %v, want %v", dir, got, want)
		}
	}
}

func TestUpdatedTo(t *testing.T) {
	for trailer, want := range map[string]string{
		"Git-K8s-Deps: go example.com/greet v1.1.0":     "v1.1.0",
		"Git-K8s-Deps:  go  example.com/greet  v1.2.0 ": "v1.2.0",
		"Git-K8s-Deps: go example.com/greet/v2 v2.0.0":  "",
		"Git-K8s-Deps: go example.com/other v1.1.0":     "",
		"Git-K8s-Deps: npm example.com/greet v1.1.0":    "",
		"Git-K8s-Deps: go example.com/greet v1.1.0 x":   "",
		"Git-K8s-Deps: go example.com/greet":            "",
		"Git-K8s-Depsx: go example.com/greet v1.1.0":    "",
		"X-Git-K8s-Deps: go example.com/greet v1.1.0":   "",
	} {
		c := git.ListedCommit{Trailers: []string{"Git-K8s-Fixer: deps", trailer}}
		if got := updatedTo(c, moduleMajor{path: greet, major: "v1"}); got != want {
			t.Errorf("updatedTo(%q) = %q, want %q", trailer, got, want)
		}
	}
}

func TestFlags(t *testing.T) {
	inNamespace(t, "git-k8s-deps")
	parse := func(args ...string) *updater {
		u := &updater{}
		fs := flag.NewFlagSet("git-k8s-deps", flag.ContinueOnError)
		u.addFlags(fs)
		if err := fs.Parse(append([]string{"-result-image=agent-runner"}, args...)); err != nil {
			t.Fatal(err)
		}
		return u
	}
	u := parse()
	if err := u.setup(); err != nil {
		t.Fatalf("setup() with the defaults = %v", err)
	}
	if u.prefix != "deps/" || u.interval != time.Hour || u.minAge != 72*time.Hour || u.proxy.urls[0] != "https://proxy.golang.org" || u.proxy.ttl != 30*time.Minute ||
		u.sourceSize != "2Gi" || u.goCacheSize != "4Gi" || u.checkEmail != u.cfg.Identity.Email || u.checkEmail != "git-k8s@users.noreply.github.com" ||
		u.seenObject != (kube.Key{Namespace: "git-k8s-deps", Name: "git-k8s-deps-first-seen"}) {
		t.Errorf("the defaults = %+v", u)
	}
	for arg, want := range map[string]kube.Key{
		"-seen-configmap=times.v1": {Namespace: "git-k8s-deps", Name: "times.v1"},
		"-seen-configmap=":         {},
		"-min-age=0":               {},
		"-seen-configmap=" + strings.Repeat("b", 253): {Namespace: "git-k8s-deps", Name: strings.Repeat("b", 253)},
	} {
		u := parse(arg)
		if err := u.setup(); err != nil || u.seenObject != want {
			t.Errorf("setup() with %s = %v and the ConfigMap %v, want %v", arg, err, u.seenObject, want)
		}
	}
	for _, args := range [][]string{
		{"-seen-configmap=Times"},
		{"-seen-configmap=deps/times"},
		{"-seen-configmap=git-k8s-deps/times"},
		{"-seen-configmap=a/b/c"},
		{"-seen-configmap=/times"},
		{"-seen-configmap=deps/"},
		{"-seen-configmap=times..v1"},
		{"-seen-configmap=" + strings.Repeat("b", 254)},
		{"-identity-email=<>"},
		{"-check-identity-email="},
		{"-prefix=deps"},
		{"-prefix="},
		{"-prefix=deps..x/"},
		{"-result-image="},
		{"-go-image="},
		{"-gosumdb="},
		{"-goproxy=direct"},
		{"-min-age=-1s"},
		{"-interval=1ms"},
		{"-timeout=0s"},
		{"-source-size=2GB"},
		{"-go-cache-size=0"},
	} {
		u := parse(args...)
		if err := u.setup(); err == nil {
			t.Errorf("setup() with %q = nil, want an error", args)
		}
	}

	t.Log("The ConfigMap is in the namespace that the namespace file names.")
	inNamespace(t, "Not_A_Namespace")
	if err := parse().setup(); err == nil || !strings.Contains(err.Error(), "Not_A_Namespace") {
		t.Errorf("setup() with a bad namespace file = %v, want an error that names what it holds", err)
	}
	ns := strings.Repeat("a", 63)
	inNamespace(t, ns)
	u = parse()
	if err := u.setup(); err != nil || u.seenObject.Namespace != ns {
		t.Errorf("setup() with a 63-character namespace = %v and the ConfigMap in %q, want %q", err, u.seenObject.Namespace, ns)
	}
	inNamespace(t, ns+"a")
	if err := parse().setup(); err == nil {
		t.Error("setup() with a 64-character namespace = nil, want an error")
	}

	t.Log("Outside a Pod, there is no namespace for the ConfigMap, unless the controller doesn't wait.")
	namespaceFile = filepath.Join(t.TempDir(), "namespace")
	if err := parse().setup(); err == nil || !strings.Contains(err.Error(), "set -seen-configmap= to keep") {
		t.Errorf("setup() without a namespace file = %v, want an error that suggests -seen-configmap=", err)
	}
	for _, arg := range []string{"-min-age=0", "-seen-configmap="} {
		if err := parse(arg).setup(); err != nil {
			t.Errorf("setup() with %s and without a namespace file = %v", arg, err)
		}
	}

	t.Log("A reconcile reports a bad flag as a permanent error.")
	f := newFixture(t)
	f.u.prefix = "deps"
	repo, secret := f.srv.Repository("app", f.rules...)
	ctx, _ := kube.Fake(t.Context(), f.b, repo, secret)
	if err := f.u.Reconcile(ctx, f.b); !kube.IsPermanent(err) {
		t.Errorf("Reconcile() = %v, want a permanent error", err)
	}
}

package main

import (
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"flag"
	"net/http"
	"net/http/httptest"
	"net/url"
	"path/filepath"
	"strconv"
	"strings"
	"sync"
	"testing"
	"time"

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

// fixture is a repository on a git server whose main branch requires greet
// v1.0.0, a module proxy that has greet v1.0.0 and v1.1.0, an updater for
// them, and a server that stands in for the result containers of its Pods.
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
		timeout: time.Minute, sourceSize: "2Gi", goCacheSize: "4Gi", maxPods: 10, interval: time.Hour, minAge: 72 * time.Hour,
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
	f := newFixture(t)
	f.u.interval = 100 * time.Hour
	f.proxy.publish(greet, "v1.1.0", today.Add(-24*time.Hour), "")
	if rec := f.checkStays(""); rec.RequeueAfter() != 48*time.Hour {
		t.Errorf("RequeueAfter() = %v, want 48h, until v1.1.0 is 72h old", rec.RequeueAfter())
	}
	f.clock = f.clock.Add(48 * time.Hour)
	f.update("v1.1.0")
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
		}},
		{name: "the go image can't be pulled", status: func(p *agent.Pod) {
			p.Status = agent.PodStatus{Phase: "Pending", InitContainerStatuses: []agent.ContainerStatus{
				{Name: "prepare", State: terminated(&agent.Terminated{Reason: "Completed"})},
				{Name: "update", State: agent.ContainerState{Waiting: &agent.Waiting{Reason: "ImagePullBackOff"}}},
			}}
		}},
		{name: "the result image can't be pulled", status: func(p *agent.Pod) {
			finished(p, "sha256:"+strings.Repeat("0", 64))
			p.Status.ContainerStatuses[0].State = agent.ContainerState{Waiting: &agent.Waiting{Reason: "ErrImagePull"}}
		}},
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

func TestWaitsForFreePods(t *testing.T) {
	f := newFixture(t)
	f.u.maxPods = 2
	var others []any
	for i, phase := range []string{"Running", "Pending", "Succeeded", "Failed"} {
		p := &agent.Pod{Object: kube.Meta("deps-"+strconv.Itoa(i), podLabels)}
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
	f.b.Spec.Head = f.work.Commit("modules")
	f.work.Push("main")
	for _, v := range []string{"v1.0.0", "v1.0.1", "v1.1.0"} {
		f.proxy.publish("example.com/other", v, longAgo, "")
	}
	f.proxy.publish("example.com/indirect", "v1.1.0", longAgo, "")
	f.proxy.publish("example.com/replaced", "v1.1.0", longAgo, "")

	p := f.start()
	want := "example.com/greet v1.1.0 . tools\nexample.com/other v1.0.1 .\n"
	if got := env(p.Spec.InitContainers[1], "UPDATES"); got != want {
		t.Errorf("UPDATES = %q, want %q", got, want)
	}
	for _, m := range []string{"example.com/indirect", "example.com/replaced"} {
		if n := f.proxy.hitsOf(m, "list"); n != 0 {
			t.Errorf("the controller read the versions of %s, want it skipped", m)
		}
	}

	t.Log("The branch updates both files in one commit; old/go.mod already requires v1.1.0.")
	toolsMod := "module example.com/app/tools\n\ngo 1.24\n\nrequire example.com/greet v1.1.0\n"
	f.finish(p, result(
		withFiles("v1.1.0", "go.mod", strings.Replace(rootMod, "greet v1.0.0", "greet v1.1.0", 1), "tools/go.mod", toolsMod),
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
		"Update example.com/greet from v1.0.0 to v1.1.0 in tools/go.mod.\n\n" +
		"Git-K8s-Deps: go example.com/greet v1.1.0"
	if got := f.work.Git("log", "-1", "--format=%B", head); got != msg {
		t.Errorf("the update's message = %q, want %q", got, msg)
	}
	if got := f.work.Show(head, "tools/go.mod"); got != strings.TrimSpace(toolsMod) {
		t.Errorf("tools/go.mod = %q, want greet at v1.1.0", got)
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

func TestValidBranch(t *testing.T) {
	for name, want := range map[string]bool{
		"deps/go/example.com/greet@v1":   true,
		"deps/go/gopkg.in/yaml.v3@v3":    true,
		"deps/go/github.com/A/B_c-d~@v1": false,
		"":                               false,
		"@":                              false,
		"-x":                             false,
		"deps/":                          false,
		"deps//go":                       false,
		"deps/.go":                       false,
		"deps/go.lock":                   false,
		"deps/go.":                       false,
		"deps/go..x":                     false,
		"deps/go@{1}":                    false,
		"deps/go x":                      false,
		"deps/go:x":                      false,
		"deps/go\x7f":                    false,
	} {
		if got := validBranch(name); got != want {
			t.Errorf("validBranch(%q) = %v, want %v", name, got, want)
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

func TestFlags(t *testing.T) {
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
		u.sourceSize != "2Gi" || u.goCacheSize != "4Gi" || u.checkEmail != u.cfg.Identity.Email || u.checkEmail != "git-k8s@users.noreply.github.com" {
		t.Errorf("the defaults = %+v", u)
	}
	for _, args := range [][]string{
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

	t.Log("A reconcile reports a bad flag as a permanent error.")
	f := newFixture(t)
	f.u.prefix = "deps"
	repo, secret := f.srv.Repository("app", f.rules...)
	ctx, _ := kube.Fake(t.Context(), f.b, repo, secret)
	if err := f.u.Reconcile(ctx, f.b); !kube.IsPermanent(err) {
		t.Errorf("Reconcile() = %v, want a permanent error", err)
	}
}

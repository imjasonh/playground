package mirror

import (
	"bytes"
	"cmp"
	"compress/gzip"
	"crypto/rand"
	"encoding/base64"
	"fmt"
	"io"
	"net"
	"net/http"
	"net/http/httptest"
	"slices"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"testing"
	"time"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/internal/caller"
	"github.com/imjasonh/playground/kube"
	"github.com/imjasonh/playground/kube/k8s"
)

const (
	podNameExtra = "authentication.kubernetes.io/pod-name"
	podUIDExtra  = "authentication.kubernetes.io/pod-uid"
)

// fixture serves a mirror whose copy of default/app has main at base and
// feature at feature. Main's merge policy lets the gofmt check push and
// lists the approval check, and the service account git-k8s-deps may start
// branches under deps/. The git-k8s-checks ConfigMap makes check-gofmt in
// the namespace check-gofmt and bot in the namespace checks the gofmt check,
// check-approval in the namespace checks the approval check, and
// check-other in the namespace check-other the other check. It also names
// the gofmt check for the core program, which is never a check.
type fixture struct {
	*world
	srv           *httptest.Server
	base, feature string
	// standby makes the server act as a replica that reconciles nothing,
	// so kube.Trigger returns false.
	standby atomic.Bool

	mu        sync.Mutex
	triggered []kube.Key
}

func newFixture(t *testing.T) *fixture {
	t.Helper()
	w := newWorld(t)
	w.repo.Spec.Branches = []gitk8s.BranchRule{
		{Match: "main", Merge: &gitk8s.MergePolicy{Checks: []gitk8s.CheckPolicy{{Name: "gofmt", MayPush: true}, {Name: "approval"}}}},
		{Match: "**", Parent: "main"},
	}
	w.m.Prefixes = []Prefix{{Namespace: "git-k8s-deps", ServiceAccount: "git-k8s-deps", Prefix: "deps/"}}
	f := &fixture{world: w}
	f.base = w.commit("", "base")
	f.feature = w.commit(f.base, "feature")
	w.pushExternal("main", f.base)
	w.pushExternal("feature", f.feature)
	w.sync(SyncOptions{})

	repo := &gitk8s.TrackedRepository{Object: w.repo.Object, Spec: w.repo.Spec}
	unsynced := &gitk8s.TrackedRepository{Object: kube.Meta("unsynced", nil), Spec: gitk8s.TrackedRepositorySpec{URL: "https://example.com/unsynced.git"}}
	unsynced.Namespace, unsynced.UID = "default", "uid-unsynced"
	// The gotest check runs the Pod gotest-1 on feature. On the branch
	// squatted, another check made the Pod that the gotest check's result
	// names. On the branch running, the gotest check's Pod has started its
	// tests.
	branch := func(name, pod string) *gitk8s.TrackedBranch {
		b := &gitk8s.TrackedBranch{Object: kube.Meta(name, map[string]string{gitk8s.RepositoryLabel: "app"})}
		b.Namespace = "default"
		b.Spec.Merge = &gitk8s.MergePolicy{Checks: []gitk8s.CheckPolicy{{Name: gitk8s.GoTestCheck}}}
		b.Status.Checks = map[string]gitk8s.CheckResult{gitk8s.GoTestCheck: {State: gitk8s.Running, Pod: pod}}
		return b
	}
	pod := func(name, controller, phase string) *k8s.Pod {
		p := &k8s.Pod{Object: kube.Meta(name, map[string]string{gitk8s.ControllerLabel: controller})}
		p.Namespace, p.UID = "default", "uid-"+name
		p.Status.Phase = phase
		return p
	}
	token := func(token, user string, extra map[string][]string) kube.FakeToken {
		return kube.FakeToken{Token: token, User: kube.UserInfo{Username: user, Extra: extra}, Audiences: []string{gitk8s.MirrorAudience}}
	}
	podToken := func(token, namespace, pod, uid string) kube.FakeToken {
		return kube.FakeToken{
			Token:     token,
			User:      kube.UserInfo{Username: "system:serviceaccount:" + namespace + ":default", Extra: map[string][]string{podNameExtra: {pod}, podUIDExtra: {uid}}},
			Audiences: []string{gitk8s.MirrorAudience},
		}
	}
	checks := &k8s.ConfigMap{Object: kube.Meta(caller.ChecksConfigMap, nil), Data: map[string]string{
		"check-gofmt.check-gofmt": "gofmt", "checks.check-approval": "approval", "check-other.check-other": "other",
		"checks.bot": "gofmt", "git-k8s.git-k8s": "gofmt",
	}}
	checks.Namespace = caller.ChecksNamespace
	objects := []any{
		repo,
		unsynced,
		checks,
		branch("app-feature", "gotest-1"),
		pod("gotest-1", gitk8s.GoTestController, "Pending"),
		branch("app-squatted", "gotest-squatted"),
		pod("gotest-squatted", "check-other", "Pending"),
		branch("app-running", "gotest-running"),
		pod("gotest-running", gitk8s.GoTestController, "Running"),
		token("gofmt", "system:serviceaccount:check-gofmt:check-gofmt", nil),
		token("approval", "system:serviceaccount:checks:check-approval", nil),
		token("namesake", "system:serviceaccount:check-approval:check-approval", nil),
		token("other", "system:serviceaccount:check-other:check-other", nil),
		token("deps", "system:serviceaccount:git-k8s-deps:git-k8s-deps", nil),
		token("bot", "system:serviceaccount:checks:bot", nil),
		token("core", "system:serviceaccount:git-k8s:git-k8s", nil),
		podToken("pod", "default", "gotest-1", "uid-gotest-1"),
		podToken("stray-pod", "default", "gotest-2", "uid-gotest-2"),
		podToken("team-pod", "team", "gotest-1", "uid-gotest-1"),
		podToken("earlier-pod", "default", "gotest-1", "uid-earlier"),
		podToken("squatter", "default", "gotest-squatted", "uid-gotest-squatted"),
		podToken("running-pod", "default", "gotest-running", "uid-gotest-running"),
		token("no-uid-pod", "system:serviceaccount:default:default", map[string][]string{podNameExtra: {"gotest-1"}}),
		token("unbound", "system:serviceaccount:default:default", nil),
		token("person", "jane@example.com", nil),
		kube.FakeToken{Token: "api", User: kube.UserInfo{Username: "system:serviceaccount:check-gofmt:check-gofmt"}},
	}
	f.srv = httptest.NewServer(http.HandlerFunc(func(rw http.ResponseWriter, r *http.Request) {
		world := objects
		if f.standby.Load() {
			world = append(slices.Clip(world), kube.FakeStandby{})
		}
		ctx, rec := kube.FakeRequest(r.Context(), world...)
		w.m.ServeHTTP(rw, r.WithContext(ctx))
		if err := rec.Err(); err != nil {
			t.Errorf("the handler did what a kube.Serve handler can't: %v", err)
		}
		f.mu.Lock()
		defer f.mu.Unlock()
		f.triggered = append(f.triggered, kube.Triggered[gitk8s.TrackedRepository](rec)...)
	}))
	t.Cleanup(f.srv.Close)
	return f
}

func (f *fixture) url(repo string) string { return f.srv.URL + "/default/" + repo + ".git" }

// git runs git with token as its bearer token.
func (f *fixture) git(token string, args ...string) (string, error) {
	return f.work.TryGit(append([]string{"-c", "http.extraHeader=Authorization: Bearer " + token}, args...)...)
}

// takeTriggered returns the keys that the server triggered since the last
// call.
func (f *fixture) takeTriggered() []kube.Key {
	f.mu.Lock()
	defer f.mu.Unlock()
	t := f.triggered
	f.triggered = nil
	return t
}

func (f *fixture) do(t *testing.T, method, path, token string, header http.Header, body io.Reader) (*http.Response, string) {
	t.Helper()
	req, err := http.NewRequestWithContext(t.Context(), method, f.srv.URL+path, body)
	if err != nil {
		t.Fatal(err)
	}
	for k, v := range header {
		req.Header[k] = v
	}
	if token != "" {
		req.Header.Set("Authorization", "Bearer "+token)
	}
	resp, err := f.srv.Client().Do(req)
	if err != nil {
		t.Fatal(err)
	}
	defer resp.Body.Close()
	b, err := io.ReadAll(resp.Body)
	if err != nil {
		t.Fatal(err)
	}
	return resp, string(b)
}

func TestServeHTTPStatus(t *testing.T) {
	f := newFixture(t)
	const (
		fetch = "/default/app.git/info/refs?service=git-upload-pack"
		push  = "/default/app.git/info/refs?service=git-receive-pack"
	)
	for _, tc := range []struct {
		name, method, path, token string
		want                      int
		body                      string
	}{
		{name: "no token", path: fetch, want: http.StatusUnauthorized},
		{name: "a token for the API server", path: fetch, token: "api", want: http.StatusUnauthorized},
		{name: "a person's token", path: fetch, token: "person", want: http.StatusUnauthorized},
		{name: "an unknown token", path: fetch, token: "nope", want: http.StatusUnauthorized},
		{name: "a check that the repository doesn't list", path: fetch, token: "other", want: http.StatusNotFound, body: "no TrackedRepository default/app that check-other/check-other may fetch"},
		{name: "a listed check fetches", path: fetch, token: "approval", want: http.StatusOK, body: "001e# service=git-upload-pack\n0000"},
		{name: "a check that may push", path: push, token: "gofmt", want: http.StatusOK, body: "001f# service=git-receive-pack\n0000"},
		{name: "a check that may not push", path: push, token: "approval", want: http.StatusForbidden, body: "checks/check-approval may not push to default/app"},
		{name: "generate's account for a check that runs elsewhere", path: fetch, token: "namesake", want: http.StatusNotFound, body: "no TrackedRepository default/app that check-approval/check-approval may fetch"},
		{name: "a controller with a prefix", path: push, token: "deps", want: http.StatusOK},
		{name: "a check through its ConfigMap entry", path: push, token: "bot", want: http.StatusOK},
		{name: "the core program, whose ConfigMap entry names a check", path: fetch, token: "core", want: http.StatusNotFound, body: "no TrackedRepository default/app that git-k8s/git-k8s may fetch"},
		{name: "a test Pod fetches", path: fetch, token: "pod", want: http.StatusOK},
		{name: "a test Pod pushes", path: push, token: "pod", want: http.StatusForbidden},
		{name: "a Pod that no check runs", path: fetch, token: "stray-pod", want: http.StatusNotFound},
		{name: "a Pod in another namespace", path: fetch, token: "team-pod", want: http.StatusNotFound},
		{name: "an earlier Pod with a test Pod's name", path: fetch, token: "earlier-pod", want: http.StatusNotFound},
		{name: "a Pod with another check's label", path: fetch, token: "squatter", want: http.StatusNotFound},
		{name: "a token with a Pod's name and no UID", path: fetch, token: "no-uid-pod", want: http.StatusNotFound},
		{name: "a token that isn't bound to a Pod", path: fetch, token: "unbound", want: http.StatusNotFound},
		{name: "a repository that doesn't exist", path: "/default/nope.git/info/refs?service=git-upload-pack", token: "deps", want: http.StatusNotFound},
		{name: "a repository that the mirror hasn't fetched", path: "/default/unsynced.git/info/refs?service=git-upload-pack", token: "deps", want: http.StatusServiceUnavailable, body: "hasn't fetched"},
		{name: "dumb HTTP", path: "/default/app.git/info/refs", token: "gofmt", want: http.StatusForbidden},
		{name: "another service", path: "/default/app.git/info/refs?service=git-upload-archive", token: "gofmt", want: http.StatusForbidden},
		{name: "a POST of info/refs", method: http.MethodPost, path: fetch, token: "gofmt", want: http.StatusMethodNotAllowed},
		{name: "a GET of a service", path: "/default/app.git/git-upload-pack", token: "gofmt", want: http.StatusMethodNotAllowed},
		{name: "a file in the repository", path: "/default/app.git/HEAD", token: "gofmt", want: http.StatusNotFound},
		{name: "no .git", path: "/default/app/info/refs?service=git-upload-pack", token: "gofmt", want: http.StatusNotFound},
		{name: "a parent directory", path: "/default/../app.git/info/refs?service=git-upload-pack", token: "gofmt", want: http.StatusNotFound},
		{name: "an uppercase namespace", path: "/Default/app.git/info/refs?service=git-upload-pack", token: "gofmt", want: http.StatusNotFound},
	} {
		t.Run(tc.name, func(t *testing.T) {
			resp, body := f.do(t, cmp.Or(tc.method, http.MethodGet), tc.path, tc.token, nil, nil)
			if resp.StatusCode != tc.want || !strings.Contains(body, tc.body) {
				t.Errorf("status %d with body %q; want %d with %q", resp.StatusCode, body, tc.want, tc.body)
			}
			if tc.want == http.StatusUnauthorized && resp.Header.Get("WWW-Authenticate") == "" {
				t.Error("a 401 without WWW-Authenticate")
			}
		})
	}
	if got := f.takeTriggered(); len(got) > 0 {
		t.Errorf("requests without pushes triggered %v", got)
	}
}

func TestChecksFetchAndPush(t *testing.T) {
	f := newFixture(t)
	for _, protocol := range []string{"0", "2"} {
		if _, err := f.git("approval", "-c", "protocol.version="+protocol, "fetch", "--quiet", f.url("app"), "refs/heads/feature"); err != nil {
			t.Fatalf("fetch with protocol %s: %v", protocol, err)
		}
		if got := f.work.Git("rev-parse", "FETCH_HEAD"); got != f.feature {
			t.Errorf("with protocol %s, fetched %s; want %s", protocol, got, f.feature)
		}
	}

	// A push bigger than git's post buffer streams the request.
	f.work.Git("checkout", "--quiet", "--detach", f.feature)
	big := make([]byte, 600<<10)
	rand.Read(big)
	f.work.Write("big.txt", base64.StdEncoding.EncodeToString(big))
	fix := f.work.Commit("fix")
	if out, err := f.git("gofmt", "push", f.url("app"), fix+":refs/heads/feature"); err != nil {
		t.Fatalf("push: %v\n%s", err, out)
	}
	wantHeads(t, "the copy's branches", f.copyRefs("refs/heads/"), map[string]string{"main": f.base, "feature": fix})
	if got, want := f.takeTriggered(), []kube.Key{{Namespace: "default", Name: "app"}}; !slices.Equal(got, want) {
		t.Errorf("the push triggered %v; want %v", got, want)
	}

	// The mirror took the push before the external repository has it.
	wantHeads(t, "before a sync, the external repository's branches", f.externalHeads(), map[string]string{"main": f.base, "feature": f.feature})
	f.sync(SyncOptions{Push: true})
	wantHeads(t, "after a sync, the external repository's branches", f.externalHeads(), map[string]string{"main": f.base, "feature": fix})
}

func TestServeRefusesPushes(t *testing.T) {
	f := newFixture(t)
	fix := f.commit(f.feature, "fix")
	for _, tc := range []struct {
		name  string
		token string
		refs  []string
		want  []string
	}{
		{name: "a parent", token: "gofmt", refs: []string{fix + ":refs/heads/main"}, want: []string{"main is a parent branch, which only the merge controller updates"}},
		{name: "a new branch", token: "gofmt", refs: []string{fix + ":refs/heads/new"}, want: []string{"checks may not create branches"}},
		{name: "a deletion", token: "gofmt", refs: []string{":refs/heads/feature"}, want: []string{"checks may not delete branches"}},
		{name: "a tag", token: "gofmt", refs: []string{fix + ":refs/tags/v1"}, want: []string{"the mirror takes only branches"}},
		{name: "the mirror's refs", token: "gofmt", refs: []string{fix + ":refs/git-k8s/downstream/heads/feature"}, want: []string{"the mirror takes only branches"}},
		{
			name:  "a branch and a parent",
			token: "gofmt",
			refs:  []string{fix + ":refs/heads/feature", fix + ":refs/heads/main"},
			want:  []string{"feature (another update in the push was refused)", "main (main is a parent branch"},
		},
		{name: "a branch outside a controller's prefix", token: "deps", refs: []string{fix + ":refs/heads/feature"}, want: []string{"git-k8s-deps/git-k8s-deps may push only branches under deps/"}},
		{name: "a check that may not push", token: "approval", refs: []string{fix + ":refs/heads/feature"}, want: []string{"403"}},
		{name: "a test Pod", token: "pod", refs: []string{fix + ":refs/heads/feature"}, want: []string{"403"}},
	} {
		t.Run(tc.name, func(t *testing.T) {
			out, err := f.git(tc.token, append([]string{"push", f.url("app")}, tc.refs...)...)
			if err == nil {
				t.Fatalf("push succeeded:\n%s", out)
			}
			for _, want := range tc.want {
				if !strings.Contains(err.Error(), want) {
					t.Errorf("push failed with\n%v\nwant %q", err, want)
				}
			}
			wantHeads(t, "the copy's branches", f.copyRefs("refs/heads/"), map[string]string{"main": f.base, "feature": f.feature})
			if got := f.takeTriggered(); len(got) > 0 {
				t.Errorf("a refused push triggered %v", got)
			}
		})
	}
}

func TestServeLetsControllersStartBranches(t *testing.T) {
	f := newFixture(t)
	bump := f.commit(f.base, "bump")
	for _, step := range []struct {
		ref  string
		want map[string]string
	}{
		{ref: f.base + ":refs/heads/deps/bump", want: map[string]string{"main": f.base, "feature": f.feature, "deps/bump": f.base}},
		{ref: bump + ":refs/heads/deps/bump", want: map[string]string{"main": f.base, "feature": f.feature, "deps/bump": bump}},
		{ref: ":refs/heads/deps/bump", want: map[string]string{"main": f.base, "feature": f.feature}},
	} {
		if out, err := f.git("deps", "push", f.url("app"), step.ref); err != nil {
			t.Fatalf("push %s: %v\n%s", step.ref, err, out)
		}
		wantHeads(t, "after push "+step.ref+", the copy's branches", f.copyRefs("refs/heads/"), step.want)
	}
	if got := f.takeTriggered(); len(got) != 3 {
		t.Errorf("3 pushes triggered %v; want 3 triggers", got)
	}
}

// TestServeMapsChecksWithTheConfigMap pushes as a service account that only
// the git-k8s-checks ConfigMap makes a check.
func TestServeMapsChecksWithTheConfigMap(t *testing.T) {
	f := newFixture(t)
	fix := f.commit(f.feature, "fix")
	if out, err := f.git("bot", "push", f.url("app"), fix+":refs/heads/feature"); err != nil {
		t.Fatalf("push: %v\n%s", err, out)
	}
	wantHeads(t, "the copy's branches", f.copyRefs("refs/heads/"), map[string]string{"main": f.base, "feature": fix})
	if out, err := f.git("bot", "push", f.url("app"), fix+":refs/heads/main"); err == nil || !strings.Contains(err.Error(), "main is a parent branch") {
		t.Errorf("push to main: %v\n%s; want a refusal", err, out)
	}
}

// TestServeTakesPushWithoutTrigger pushes to a replica that can't trigger a
// reconcile, as while its controllers start. git doesn't retry a push, so
// the mirror takes it and leaves it for the next poll.
func TestServeTakesPushWithoutTrigger(t *testing.T) {
	f := newFixture(t)
	f.standby.Store(true)
	fix := f.commit(f.feature, "fix")
	if out, err := f.git("gofmt", "push", f.url("app"), fix+":refs/heads/feature"); err != nil {
		t.Fatalf("push: %v\n%s", err, out)
	}
	wantHeads(t, "the copy's branches", f.copyRefs("refs/heads/"), map[string]string{"main": f.base, "feature": fix})
	if got := f.takeTriggered(); len(got) > 0 {
		t.Errorf("a replica that reconciles nothing triggered %v", got)
	}
	f.sync(SyncOptions{Push: true})
	wantHeads(t, "after a sync, the external repository's branches", f.externalHeads(), map[string]string{"main": f.base, "feature": fix})
}

func TestServeTestPods(t *testing.T) {
	f := newFixture(t)
	if out, err := f.git("pod", "fetch", "--quiet", "--depth=1", f.url("app"), "refs/heads/feature"); err != nil {
		t.Fatalf("the test Pod's fetch: %v\n%s", err, out)
	}
	if got := f.work.Git("rev-parse", "FETCH_HEAD"); got != f.feature {
		t.Errorf("fetched %s; want %s", got, f.feature)
	}
	for _, token := range []string{"stray-pod", "team-pod", "earlier-pod", "squatter", "running-pod", "no-uid-pod", "unbound"} {
		if _, err := f.git(token, "fetch", "--quiet", f.url("app"), "refs/heads/feature"); err == nil || !strings.Contains(err.Error(), "not found") {
			t.Errorf("fetch with %s = %v; want not found", token, err)
		}
	}
	if _, err := f.git("deps", "fetch", "--quiet", f.url("unsynced"), "refs/heads/main"); err == nil || !strings.Contains(err.Error(), "503") {
		t.Errorf("fetch of a repository that the mirror hasn't fetched = %v; want 503", err)
	}
}

// TestServeReadsPushLikeReceivePack sends pushes that git doesn't, to check
// that the mirror judges the updates that receive-pack would make.
func TestServeReadsPushLikeReceivePack(t *testing.T) {
	f := newFixture(t)
	fix := f.commit(f.feature, "fix")
	gz := func(s string) io.Reader {
		var b bytes.Buffer
		zw := gzip.NewWriter(&b)
		zw.Write([]byte(s))
		zw.Close()
		return &b
	}
	header := func(kv ...string) http.Header {
		h := http.Header{"Content-Type": {"application/x-git-receive-pack-request"}}
		for i := 0; i < len(kv); i += 2 {
			h.Set(kv[i], kv[i+1])
		}
		return h
	}
	const path = "/default/app.git/git-receive-pack"
	for _, tc := range []struct {
		name   string
		header http.Header
		body   io.Reader
		want   string
	}{
		{
			name:   "a parent named after a NUL on a later line",
			header: header(),
			body: strings.NewReader(pkt(f.feature+" "+fix+" refs/heads/feature\x00report-status side-band-64k\n") +
				pkt(f.base+" "+fix+" refs/heads/main\x00x\n") + "0000"),
			want: "ng refs/heads/main main is a parent branch",
		},
		{
			name:   "a gzipped push to a parent",
			header: header("Content-Encoding", "gzip"),
			body:   gz(pkt(f.base+" "+fix+" refs/heads/main\x00report-status\n") + "0000"),
			want:   "ng refs/heads/main main is a parent branch",
		},
		{
			name:   "no report-status",
			header: header(),
			body:   strings.NewReader(pkt(f.base+" "+fix+" refs/heads/main\n") + "0000"),
			want:   "main is a parent branch",
		},
	} {
		t.Run(tc.name, func(t *testing.T) {
			_, body := f.do(t, http.MethodPost, path, "gofmt", tc.header, tc.body)
			if !strings.Contains(body, tc.want) {
				t.Errorf("response %q; want %q", body, tc.want)
			}
		})
	}

	// git sends a push with no updates to check its credentials first.
	resp, body := f.do(t, http.MethodPost, path, "gofmt", header(), strings.NewReader("0000"))
	if resp.StatusCode != http.StatusOK {
		t.Errorf("a push with no updates: status %d, %q", resp.StatusCode, body)
	}
	wantHeads(t, "the copy's branches", f.copyRefs("refs/heads/"), map[string]string{"main": f.base, "feature": f.feature})
	if got := f.takeTriggered(); len(got) > 0 {
		t.Errorf("refused pushes triggered %v", got)
	}
}

// zeros is a request body of n zero bytes that counts the bytes read.
type zeros struct{ n, read int64 }

func (z *zeros) Read(p []byte) (int, error) {
	if z.read == z.n {
		return 0, io.EOF
	}
	n := int(min(int64(len(p)), z.n-z.read))
	clear(p[:n])
	z.read += int64(n)
	return n, nil
}

// TestRefuseAllStopsReading refuses a push whose pack is bigger than a copy
// takes.
func TestRefuseAllStopsReading(t *testing.T) {
	body := &zeros{n: maxPushSize + 1<<20}
	rec := httptest.NewRecorder()
	p := &pushRequest{commands: []command{{Old: oidA, New: oidB, Ref: "refs/heads/main"}}, caps: []string{"report-status"}}
	refuseAll(rec, httptest.NewRequest(http.MethodPost, "/default/app.git/git-receive-pack", body), p, []string{"main is a parent branch"})
	if body.read > maxPushSize {
		t.Errorf("read %d bytes of a refused push; want at most %d", body.read, maxPushSize)
	}
	if got, want := rec.Body.String(), "ng refs/heads/main main is a parent branch"; !strings.Contains(got, want) {
		t.Errorf("response %q; want %q", got, want)
	}
}

// TestServeRefusesPushWithBigPack refuses a push whose pack is bigger than
// the 256 KiB of a request that Go's server reads after the handler
// returns. git reads the response only after it sends the whole pack, so
// git gets the reasons only if the mirror reads the pack.
func TestServeRefusesPushWithBigPack(t *testing.T) {
	f := newFixture(t)
	f.work.Git("checkout", "--quiet", "--detach", f.base)
	big := make([]byte, 8<<20)
	rand.Read(big)
	f.work.Write("big.bin", string(big))
	fix := f.work.Commit("big")
	out, err := f.git("gofmt", "push", f.url("app"), fix+":refs/heads/main")
	if err == nil || !strings.Contains(err.Error(), "main is a parent branch") {
		t.Fatalf("push = %v\n%s; want the reason for refusing it", err, out)
	}
	wantHeads(t, "the copy's branches", f.copyRefs("refs/heads/"), map[string]string{"main": f.base, "feature": f.feature})
}

// TestServeStopsWaitingForPush sends the start of a push and then nothing.
// The mirror gives up on the push, and doesn't hold the copy open while it
// waits.
func TestServeStopsWaitingForPush(t *testing.T) {
	f := newFixture(t)
	f.m.readTimeout = time.Second
	pr, pw := io.Pipe()
	t.Cleanup(func() { pw.Close() })
	start := pkt(f.feature + " " + f.base + " refs/heads/feature\x00report-status\n")
	go pw.Write([]byte(start[:20]))

	type result struct {
		status int
		body   string
		err    error
	}
	done := make(chan result, 1)
	go func() {
		req, err := http.NewRequest(http.MethodPost, f.srv.URL+"/default/app.git/git-receive-pack", pr)
		if err != nil {
			done <- result{err: err}
			return
		}
		req.Header.Set("Authorization", "Bearer gofmt")
		resp, err := f.srv.Client().Do(req)
		if err != nil {
			done <- result{err: err}
			return
		}
		defer resp.Body.Close()
		b, err := io.ReadAll(resp.Body)
		done <- result{status: resp.StatusCode, body: string(b), err: err}
	}()

	e := f.m.entry(f.repo)
	tick := time.NewTicker(10 * time.Millisecond)
	defer tick.Stop()
	timeout := time.After(30 * time.Second)
	for {
		select {
		case res := <-done:
			if res.err != nil {
				t.Fatal(res.err)
			}
			if res.status != http.StatusBadRequest || !strings.Contains(res.body, "i/o timeout") {
				t.Errorf("status %d with body %q; want %d with a timeout", res.status, res.body, http.StatusBadRequest)
			}
			return
		case <-tick.C:
			if !e.mu.TryLock() {
				t.Fatal("the mirror holds the copy open while it waits for a push")
			}
			e.mu.Unlock()
		case <-timeout:
			t.Fatal("the mirror still waits for the push after 30s")
		}
	}
}

// TestServeStopsWritingToAClientThatDoesntRead fetches a pack too big for
// the connection's buffers and never reads the response. The mirror stops
// writing at its write deadline and closes the copy, instead of holding it
// open until the client disconnects.
func TestServeStopsWritingToAClientThatDoesntRead(t *testing.T) {
	f := newFixture(t)
	big := make([]byte, 32<<20)
	rand.Read(big)
	f.work.Git("checkout", "--quiet", "--detach", f.base)
	f.work.Write("big.bin", string(big))
	bigCommit := f.work.Commit("big")
	f.pushExternal("big", bigCommit)
	f.sync(SyncOptions{Fetch: true})
	f.m.readTimeout = time.Second

	addr := strings.TrimPrefix(f.srv.URL, "http://")
	conn, err := net.Dial("tcp", addr)
	if err != nil {
		t.Fatal(err)
	}
	defer conn.Close()
	body := pkt("want "+bigCommit+"\n") + "0000" + pkt("done\n")
	if _, err := fmt.Fprintf(conn, "POST /default/app.git/git-upload-pack HTTP/1.1\r\nHost: %s\r\nAuthorization: Bearer gofmt\r\nContent-Type: application/x-git-upload-pack-request\r\nContent-Length: %d\r\n\r\n%s", addr, len(body), body); err != nil {
		t.Fatal(err)
	}
	start := time.Now()

	e := f.m.entry(f.repo)
	free := func() bool {
		if !e.mu.TryLock() {
			return false
		}
		e.mu.Unlock()
		return true
	}
	for free() {
		if time.Since(start) > 10*time.Second {
			t.Fatal("the mirror didn't open the copy within 10s")
		}
		time.Sleep(5 * time.Millisecond)
	}
	for !free() {
		if time.Since(start) > 15*time.Second {
			t.Fatal("the mirror still holds the copy open 15s after a request that may take 1s, for a client that doesn't read")
		}
		time.Sleep(20 * time.Millisecond)
	}
	t.Logf("the mirror closed the copy %v after the request", time.Since(start).Round(10*time.Millisecond))
}

// TestServeRefusesBigPack pushes a bigger pack than the copy takes.
func TestServeRefusesBigPack(t *testing.T) {
	f := newFixture(t)
	if got, want := f.work.Git("--git-dir="+f.copyDir(), "config", "receive.maxInputSize"), strconv.Itoa(maxPushSize); got != want {
		t.Fatalf("the copy takes packs of up to %s bytes; want %s", got, want)
	}
	// Pushing maxPushSize bytes takes too long for a test.
	f.work.Git("--git-dir="+f.copyDir(), "config", "receive.maxInputSize", "100000")
	f.work.Git("checkout", "--quiet", "--detach", f.feature)
	big := make([]byte, 600<<10)
	rand.Read(big)
	f.work.Write("big.txt", base64.StdEncoding.EncodeToString(big))
	fix := f.work.Commit("fix")
	if out, err := f.git("gofmt", "push", f.url("app"), fix+":refs/heads/feature"); err == nil || !strings.Contains(err.Error(), "pack exceeds maximum allowed size") {
		t.Fatalf("push = %v\n%s; want an error about the pack's size", err, out)
	}
	wantHeads(t, "the copy's branches", f.copyRefs("refs/heads/"), map[string]string{"main": f.base, "feature": f.feature})
}

package mirror

import (
	"bytes"
	"cmp"
	"compress/gzip"
	"crypto/rand"
	"encoding/base64"
	"io"
	"net/http"
	"net/http/httptest"
	"slices"
	"strings"
	"sync"
	"sync/atomic"
	"testing"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/kube"
)

const podNameExtra = "authentication.kubernetes.io/pod-name"

// fixture serves a mirror whose copy of default/app has main at base and
// feature at feature. Main's merge policy lets the gofmt check push and
// lists the approval check, and the service account git-k8s-deps may start
// branches under deps/.
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

	repo := &gitk8s.GitRepository{Object: w.repo.Object, Spec: w.repo.Spec}
	unsynced := &gitk8s.GitRepository{Object: kube.Meta("unsynced", nil), Spec: gitk8s.GitRepositorySpec{URL: "https://example.com/unsynced.git"}}
	unsynced.Namespace, unsynced.UID = "default", "uid-unsynced"
	branch := &gitk8s.GitBranch{Object: kube.Meta("app-feature", map[string]string{gitk8s.RepositoryLabel: "app"})}
	branch.Namespace = "default"
	branch.Status.Checks = map[string]gitk8s.CheckResult{"gotest": {State: gitk8s.Running, Outputs: map[string]string{"pod": "gotest-1"}}}
	token := func(token, user string, extra map[string][]string) kube.FakeToken {
		return kube.FakeToken{Token: token, User: kube.UserInfo{Username: user, Extra: extra}, Audiences: []string{gitk8s.MirrorAudience}}
	}
	objects := []any{
		repo,
		unsynced,
		branch,
		token("gofmt", "system:serviceaccount:check-gofmt:check-gofmt", nil),
		token("approval", "system:serviceaccount:check-approval:check-approval", nil),
		token("other", "system:serviceaccount:check-other:check-other", nil),
		token("deps", "system:serviceaccount:git-k8s-deps:git-k8s-deps", nil),
		token("pod", "system:serviceaccount:default:default", map[string][]string{podNameExtra: {"gotest-1"}}),
		token("stray-pod", "system:serviceaccount:default:default", map[string][]string{podNameExtra: {"gotest-2"}}),
		token("team-pod", "system:serviceaccount:team:default", map[string][]string{podNameExtra: {"gotest-1"}}),
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
		f.triggered = append(f.triggered, kube.Triggered[gitk8s.GitRepository](rec)...)
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
		{name: "a check that the repository doesn't list", path: fetch, token: "other", want: http.StatusNotFound, body: "no GitRepository default/app that check-other/check-other may fetch"},
		{name: "a listed check fetches", path: fetch, token: "approval", want: http.StatusOK, body: "001e# service=git-upload-pack\n0000"},
		{name: "a check that may push", path: push, token: "gofmt", want: http.StatusOK, body: "001f# service=git-receive-pack\n0000"},
		{name: "a check that may not push", path: push, token: "approval", want: http.StatusForbidden, body: "check-approval/check-approval may not push to default/app"},
		{name: "a controller with a prefix", path: push, token: "deps", want: http.StatusOK},
		{name: "a test Pod fetches", path: fetch, token: "pod", want: http.StatusOK},
		{name: "a test Pod pushes", path: push, token: "pod", want: http.StatusForbidden},
		{name: "a Pod that no check runs", path: fetch, token: "stray-pod", want: http.StatusNotFound},
		{name: "a Pod in another namespace", path: fetch, token: "team-pod", want: http.StatusNotFound},
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
	for _, token := range []string{"stray-pod", "team-pod"} {
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

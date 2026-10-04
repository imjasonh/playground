package credentials

import (
	"context"
	"fmt"
	"net/http"
	"slices"
	"strings"
	"sync"
	"testing"
	"time"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/git-k8s/internal/git"
	"github.com/imjasonh/playground/git-k8s/internal/gittest"
	"github.com/imjasonh/playground/kube"
)

// clock makes now return the time that the result points to.
func clock(t *testing.T) *time.Time {
	at := time.Unix(1_000_000, 0)
	old := now
	now = func() time.Time { return at }
	t.Cleanup(func() { now = old })
	return &at
}

// newGitHub starts a fake GitHub whose repository acme/app has the trust
// policy git, which grants contents: write, on main.
func newGitHub(t *testing.T) (*gittest.GitHub, *gittest.Work, string) {
	gh := gittest.NewGitHub(t)
	w := gh.NewWork(t, "app")
	w.Write(".github/chainguard/git.sts.yaml", gittest.TrustPolicy(map[string]string{"contents": "write"}))
	main := w.Commit("main")
	w.Push("main")
	return gh, w, main
}

func remote(ctx context.Context, repo *gitk8s.GitRepository) (git.Remote, error) {
	return Remote(ctx, &gitk8s.Repository{Object: repo.Object, Spec: repo.Spec})
}

func TestOctoSTSRemote(t *testing.T) {
	gh, _, main := newGitHub(t)
	repo := gh.Repository("app", gitk8s.OctoSTS{GitIdentity: "git"})
	ctx, _ := kube.Fake(t.Context(), repo)
	r, err := remote(ctx, repo)
	if err != nil {
		t.Fatal(err)
	}
	ex := gh.Fake.Exchanges()
	if len(ex) != 1 || ex[0].Scope != "acme/app" || ex[0].Identity != "git" {
		t.Fatalf("exchanges = %+v", ex)
	}
	if r.URL != repo.Spec.URL || r.Auth == nil || *r.Auth != (git.Auth{Username: "x-access-token", Password: ex[0].Token}) {
		t.Errorf("remote = %+v", r)
	}
	if heads, err := (&git.Git{}).LsRemote(ctx, r); err != nil || heads["main"] != main {
		t.Errorf("listing with the GitHub token: heads = %v, err = %v", heads, err)
	}

	t.Log("The service account token's audience names the GitRepository's namespace.")
	for aud, want := range map[string]bool{"octo-sts.dev/default": true, "octo-sts.dev/other": false, "octo-sts.dev": false} {
		if tr, err := kube.ReviewToken(ctx, "fake-token-1", aud); err != nil || tr.Authenticated != want {
			t.Errorf("review for audience %s = %+v, %v; want authenticated %v", aud, tr, err, want)
		}
	}
	repo.Namespace = "other"
	ctx, _ = kube.Fake(t.Context(), repo)
	if _, err := remote(ctx, repo); err != nil {
		t.Fatal(err)
	}
	if tr, err := kube.ReviewToken(ctx, "fake-token-1", "octo-sts.dev/other"); err != nil || !tr.Authenticated {
		t.Errorf("a GitRepository in namespace other asked for a token for another audience: %+v, %v", tr, err)
	}
}

func TestRefreshesTokens(t *testing.T) {
	at := clock(t)
	gh, w, _ := newGitHub(t)
	repo := gh.Repository("app", gitk8s.OctoSTS{GitIdentity: "git"})
	token := func() (string, error) {
		t.Helper()
		ctx, _ := kube.Fake(t.Context(), repo)
		r, err := remote(ctx, repo)
		if err != nil {
			return "", err
		}
		return r.Auth.Password, nil
	}
	exchanges := func() int { return len(gh.Fake.Exchanges()) }
	first, err := token()
	if err != nil {
		t.Fatal(err)
	}
	*at = at.Add(49 * time.Minute)
	if got, err := token(); got != first || err != nil || exchanges() != 1 {
		t.Fatalf("after 49m: token %q, err %v, %d exchanges; want the first token from one exchange", got, err, exchanges())
	}

	t.Log("Ten minutes before a token expires, the next use exchanges a new one.")
	*at = at.Add(time.Minute)
	second, err := token()
	if err != nil || second == first || exchanges() != 2 {
		t.Fatalf("after 50m: token %q, err %v, %d exchanges; want a second token", second, err, exchanges())
	}

	t.Log("Without the trust policy, the exchange fails, and the old token serves until a minute before it expires.")
	w.Git("rm", "--quiet", ".github/chainguard/git.sts.yaml")
	w.Commit("remove the trust policy")
	w.Push("main")
	*at = at.Add(50 * time.Minute)
	if got, err := token(); got != second || err != nil {
		t.Fatalf("with a failed refresh: token %q, err %v; want the second token", got, err)
	}

	t.Log("The exchange runs again only after 30s, even though the trust policy is back.")
	w.Write(".github/chainguard/git.sts.yaml", gittest.TrustPolicy(map[string]string{"contents": "write"}))
	w.Commit("restore the trust policy")
	w.Push("main")
	*at = at.Add(29 * time.Second)
	if got, err := token(); got != second || err != nil || exchanges() != 2 {
		t.Fatalf("29s after the failure: token %q, err %v, %d exchanges; want the second token without an exchange", got, err, exchanges())
	}
	*at = at.Add(time.Second)
	third, err := token()
	if err != nil || third == second || exchanges() != 3 {
		t.Fatalf("30s after the failure: token %q, err %v, %d exchanges; want a third token", third, err, exchanges())
	}

	t.Log("A minute before the token expires, a failed exchange is an error.")
	w.Git("rm", "--quiet", ".github/chainguard/git.sts.yaml")
	w.Commit("remove the trust policy")
	w.Push("main")
	*at = at.Add(59 * time.Minute)
	_, err = token()
	if want := `getting a GitHub token for Octo STS identity git in acme/app: Octo STS answered 404 Not Found: unable to find trust policy for "git"`; err == nil || err.Error() != want {
		t.Errorf("err = %v, want %s", err, want)
	}
}

func TestCanceledExchangeIsNotRemembered(t *testing.T) {
	gh, _, _ := newGitHub(t)
	repo := gh.Repository("app", gitk8s.OctoSTS{GitIdentity: "git"})
	canceled, cancel := context.WithCancel(t.Context())
	cancel()
	ctx, _ := kube.Fake(canceled, repo)
	if _, err := remote(ctx, repo); err == nil {
		t.Fatal("exchanged a token with a canceled context")
	}
	ctx, _ = kube.Fake(t.Context(), repo)
	if _, err := remote(ctx, repo); err != nil {
		t.Errorf("the next reconcile waited for a retry after a canceled one: %v", err)
	}
}

// exchangeServer answers the token exchange with status and body, and
// records each request as "METHOD PATH?QUERY AUTHORIZATION USER-AGENT".
type exchangeServer struct {
	status int
	body   func(n int) string

	mu   sync.Mutex
	reqs []string
}

func (s *exchangeServer) ServeHTTP(w http.ResponseWriter, r *http.Request) {
	s.mu.Lock()
	s.reqs = append(s.reqs, fmt.Sprintf("%s %s %s %s", r.Method, r.URL.RequestURI(), r.Header.Get("Authorization"), r.Header.Get("User-Agent")))
	n := len(s.reqs)
	s.mu.Unlock()
	w.WriteHeader(s.status)
	fmt.Fprint(w, s.body(n))
}

func (s *exchangeServer) requests() []string {
	s.mu.Lock()
	defer s.mu.Unlock()
	return s.reqs
}

// serve points the -fake-github flag at s until the test ends, and returns
// a GitRepository for acme/app on it.
func serve(t *testing.T, s *exchangeServer) *gitk8s.GitRepository {
	base := gittest.Serve(t, s)
	repo := &gitk8s.GitRepository{
		Object: kube.Meta("app", nil),
		Spec:   gitk8s.GitRepositorySpec{URL: base + "/acme/app.git", OctoSTS: &gitk8s.OctoSTS{GitIdentity: "git"}},
	}
	repo.Namespace = "default"
	return repo
}

func TestExchangeRequest(t *testing.T) {
	at := clock(t)
	expiry := at.Add(15 * time.Minute).UTC().Format(time.RFC3339)
	s := &exchangeServer{status: http.StatusOK, body: func(n int) string {
		return fmt.Sprintf(`{"token": "ghs_%d", "expiry": %q}`, n, expiry)
	}}
	repo := serve(t, s)
	token := func() string {
		t.Helper()
		ctx, _ := kube.Fake(t.Context(), repo)
		r, err := remote(ctx, repo)
		if err != nil {
			t.Fatal(err)
		}
		return r.Auth.Password
	}
	if got := token(); got != "ghs_1" {
		t.Errorf("token = %q, want ghs_1", got)
	}
	if got, want := s.requests(), []string{"GET /sts/exchange?identity=git&scopes=acme%2Fapp Bearer fake-token-1 git-k8s"}; !slices.Equal(got, want) {
		t.Errorf("requests = %q, want %q", got, want)
	}

	t.Log("A token that Octo STS says expires in 15m is replaced after 5m.")
	*at = at.Add(4 * time.Minute)
	if got := token(); got != "ghs_1" {
		t.Errorf("after 4m: token = %q, want ghs_1", got)
	}
	*at = at.Add(time.Minute)
	if got := token(); got != "ghs_2" {
		t.Errorf("after 5m: token = %q, want ghs_2", got)
	}
}

func TestExchangeErrors(t *testing.T) {
	for _, tc := range []struct {
		status    int
		body, err string
	}{{
		status: http.StatusForbidden,
		body:   `{"code": 7, "message": "trust policy: subject \"x\" did not match \"y\"", "details": []}`,
		err:    `Octo STS answered 403 Forbidden: trust policy: subject "x" did not match "y"`,
	}, {
		status: http.StatusBadGateway,
		body:   "<html>bad gateway</html>\n",
		err:    "Octo STS answered 502 Bad Gateway: <html>bad gateway</html>",
	}, {
		status: http.StatusOK,
		body:   `{}`,
		err:    "Octo STS answered without a token",
	}} {
		repo := serve(t, &exchangeServer{status: tc.status, body: func(int) string { return tc.body }})
		ctx, _ := kube.Fake(t.Context(), repo)
		_, err := remote(ctx, repo)
		if want := "getting a GitHub token for Octo STS identity git in acme/app: " + tc.err; err == nil || err.Error() != want || kube.IsPermanent(err) {
			t.Errorf("err = %v, want %s", err, want)
		}
	}
}

func TestMisconfiguredOctoSTSIsPermanent(t *testing.T) {
	gh, _, _ := newGitHub(t)
	both := gh.Repository("app", gitk8s.OctoSTS{GitIdentity: "git"})
	both.Spec.SecretRef = &gitk8s.SecretRef{Name: "app-creds"}
	elsewhere := gh.Repository("app", gitk8s.OctoSTS{GitIdentity: "git"})
	elsewhere.Spec.URL = "https://gitlab.com/acme/app.git"
	for _, repo := range []*gitk8s.GitRepository{both, elsewhere} {
		ctx, _ := kube.Fake(t.Context(), repo)
		if _, err := remote(ctx, repo); !kube.IsPermanent(err) {
			t.Errorf("url %s, secretRef %v: err = %v, want a permanent error", repo.Spec.URL, repo.Spec.SecretRef, err)
		}
	}
	if n := len(gh.Fake.Exchanges()); n != 0 {
		t.Errorf("%d exchanges, want none", n)
	}
}

func TestScope(t *testing.T) {
	gh := github{web: "https://github.com"}
	for url, want := range map[string]string{
		"https://github.com/acme/app.git":              "acme/app",
		"https://github.com/acme/app":                  "acme/app",
		"https://github.com/acme/app.git/":             "acme/app",
		"https://github.com/acme/my.app_1":             "acme/my.app_1",
		"https://github.com/acme/.github":              "acme/.github",
		"https://github.com/acme/..":                   "",
		"http://github.com/acme/app.git":               "",
		"https://github.com.evil.example/acme/app.git": "",
		"https://user@github.com/acme/app.git":         "",
		"git@github.com:acme/app.git":                  "",
		"https://github.com/acme":                      "",
		"https://github.com/acme/app/tree/main":        "",
		"https://github.com/acme/../app.git":           "",
		"https://github.com/acme/app.git?x=y":          "",
	} {
		got, err := gh.scope(url)
		if got != want || (err == nil) != (want != "") {
			t.Errorf("scope(%s) = %q, %v; want %q", url, got, err, want)
		}
	}
	if _, err := gh.scope("https://gitlab.com/acme/app.git"); err == nil || !strings.Contains(err.Error(), "https://github.com/OWNER/REPO") {
		t.Errorf("err = %v, want one that names the URL form", err)
	}
}

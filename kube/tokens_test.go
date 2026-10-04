package kube

import (
	"encoding/base64"
	"encoding/json"
	"fmt"
	"net/http"
	"net/http/httptest"
	"os"
	"path/filepath"
	"reflect"
	"slices"
	"strings"
	"sync"
	"testing"
	"time"

	"github.com/imjasonh/playground/kube/internal/client"
)

func TestUserInfoServiceAccount(t *testing.T) {
	for _, tc := range []struct {
		username, namespace, name string
		ok                        bool
	}{
		{"system:serviceaccount:git-k8s:check-gofmt", "git-k8s", "check-gofmt", true},
		{"system:serviceaccount:ns", "", "", false},
		{"system:serviceaccount::name", "", "", false},
		{"system:serviceaccount:ns:", "", "", false},
		{"system:serviceaccount:ns:a:b", "", "", false},
		{"system:serviceaccounts:ns", "", "", false},
		{"kubernetes-admin", "", "", false},
	} {
		ns, name, ok := UserInfo{Username: tc.username}.ServiceAccount()
		if ns != tc.namespace || name != tc.name || ok != tc.ok {
			t.Errorf("ServiceAccount() of %q = %q, %q, %v, want %q, %q, %v", tc.username, ns, name, ok, tc.namespace, tc.name, tc.ok)
		}
	}
}

// authAPI answers TokenReviews, SelfSubjectReviews, and TokenRequests the
// way the API server does, and records the requests.
type authAPI struct {
	self UserInfo

	mu       sync.Mutex
	requests []authRequest
}

type authRequest struct {
	path string
	body map[string]any
}

// reviewer is the user that the token "valid" belongs to. Its audience is
// "git-k8s".
var reviewer = UserInfo{Username: "system:serviceaccount:checks:gofmt", UID: "uid-1", Groups: []string{"system:serviceaccounts"}}

func newAuthAPI(t *testing.T, self UserInfo) (*authAPI, *Manager) {
	t.Helper()
	a := &authAPI{self: self}
	srv := httptest.NewServer(a)
	t.Cleanup(srv.Close)
	c, err := client.New(&client.Config{Host: srv.URL}, "test")
	if err != nil {
		t.Fatal(err)
	}
	m := testManager()
	m.client = c
	return a, m
}

func (a *authAPI) sent() []authRequest {
	a.mu.Lock()
	defer a.mu.Unlock()
	return slices.Clone(a.requests)
}

func (a *authAPI) ServeHTTP(w http.ResponseWriter, r *http.Request) {
	var body map[string]any
	_ = json.NewDecoder(r.Body).Decode(&body)
	a.mu.Lock()
	a.requests = append(a.requests, authRequest{path: r.Method + " " + r.URL.Path, body: body})
	a.mu.Unlock()
	spec, _ := body["spec"].(map[string]any)
	reply := func(status any) {
		w.Header().Set("Content-Type", "application/json")
		_ = json.NewEncoder(w).Encode(map[string]any{"status": status})
	}
	forbidden := func(message string) {
		w.Header().Set("Content-Type", "application/json")
		w.WriteHeader(http.StatusForbidden)
		_ = json.NewEncoder(w).Encode(map[string]any{"kind": "Status", "apiVersion": "v1", "status": "Failure", "reason": "Forbidden", "code": 403, "message": message})
	}
	switch r.URL.Path {
	case "/apis/authentication.k8s.io/v1/tokenreviews":
		var want []string
		audiences, _ := spec["audiences"].([]any)
		for _, a := range audiences {
			want = append(want, a.(string))
		}
		switch spec["token"] {
		case "valid":
			if !slices.Contains(want, "git-k8s") {
				reply(map[string]any{"error": "token audiences [\"git-k8s\"] is invalid for the target audiences " + strings.Join(want, ",")})
				return
			}
			reply(map[string]any{"authenticated": true, "user": reviewer, "audiences": []string{"git-k8s"}})
		case "unaware":
			reply(map[string]any{"authenticated": true, "user": reviewer})
		case "denied":
			forbidden("tokenreviews.authentication.k8s.io is forbidden")
		default:
			reply(map[string]any{"error": "invalid bearer token"})
		}
	case "/apis/authentication.k8s.io/v1/selfsubjectreviews":
		reply(map[string]any{"userInfo": a.self})
	case "/api/v1/namespaces/prog/serviceaccounts/prog/token":
		reply(map[string]any{"token": "requested", "expirationTimestamp": "2030-01-02T03:04:05Z"})
	case "/api/v1/namespaces/prog/serviceaccounts/denied/token":
		forbidden(`serviceaccounts "denied" is forbidden: User "system:serviceaccount:prog:denied" cannot create resource "serviceaccounts/token" in API group "" in the namespace "prog"`)
	default:
		http.NotFound(w, r)
	}
}

func TestReviewToken(t *testing.T) {
	a, m := newAuthAPI(t, UserInfo{})
	ctx, _ := newWebhookScope(t.Context(), m)

	r, err := ReviewToken(ctx, "valid", "git-k8s", "other")
	if err != nil || !r.Authenticated || !reflect.DeepEqual(r.User, reviewer) || !slices.Equal(r.Audiences, []string{"git-k8s"}) {
		t.Errorf("ReviewToken(valid, git-k8s, other) = %+v, %v", r, err)
	}
	sent := a.sent()
	if len(sent) != 1 || sent[0].path != "POST /apis/authentication.k8s.io/v1/tokenreviews" {
		t.Fatalf("requests = %+v", sent)
	}
	if b, _ := json.Marshal(sent[0].body); string(b) != `{"apiVersion":"authentication.k8s.io/v1","kind":"TokenReview","spec":{"audiences":["git-k8s","other"],"token":"valid"}}` {
		t.Errorf("TokenReview = %s", b)
	}

	for _, tc := range []struct {
		name, token, audience string
		want                  string
	}{
		{"a token for another audience", "valid", "other", "is invalid for the target audiences"},
		{"a token from an authenticator that ignores audiences", "unaware", "git-k8s", `the token isn't valid for the audiences ["git-k8s"]`},
		{"an invalid token", "garbage", "git-k8s", "invalid bearer token"},
		{"no token", "", "git-k8s", "no token"},
	} {
		r, err := ReviewToken(ctx, tc.token, tc.audience)
		if err != nil || r.Authenticated || r.User.Username != "" || !strings.Contains(r.Error, tc.want) {
			t.Errorf("%s: ReviewToken = %+v, %v, want an error containing %q", tc.name, r, err, tc.want)
		}
	}
	for _, audiences := range [][]string{{""}, {"git-k8s", ""}} {
		if r, err := ReviewToken(ctx, "valid", audiences[0], audiences[1:]...); err == nil || r.Authenticated || !strings.Contains(err.Error(), "an audience is empty") {
			t.Errorf("ReviewToken(valid, %q) = %+v, %v, want an error", audiences, r, err)
		}
	}
	if n := len(a.sent()); n != 4 {
		t.Errorf("sent %d requests, want 4: none for an empty token or audience", n)
	}
	if _, err := ReviewToken(ctx, "denied", "git-k8s"); err == nil || !strings.Contains(err.Error(), "kube.ReviewToken") || !strings.Contains(err.Error(), "forbidden") {
		t.Errorf("ReviewToken without permission: err = %v", err)
	}
}

func TestRequestToken(t *testing.T) {
	self := UserInfo{
		Username: "system:serviceaccount:prog:prog",
		Extra:    map[string][]string{podNameExtra: {"prog-abc"}, podUIDExtra: {"uid-2"}},
	}
	a, m := newAuthAPI(t, self)
	ctx, _ := newWebhookScope(t.Context(), m)

	token, expires, err := RequestToken(ctx, "octo-sts.dev")
	if err != nil || token != "requested" || !expires.Equal(time.Date(2030, 1, 2, 3, 4, 5, 0, time.UTC)) {
		t.Fatalf("RequestToken = %q, %v, %v", token, expires, err)
	}
	if _, _, err := RequestToken(ctx, "octo-sts.dev"); err != nil {
		t.Fatal(err)
	}
	var paths []string
	var bodies []string
	for _, r := range a.sent() {
		paths = append(paths, r.path)
		b, _ := json.Marshal(r.body)
		bodies = append(bodies, string(b))
	}
	want := []string{
		"POST /apis/authentication.k8s.io/v1/selfsubjectreviews",
		"POST /api/v1/namespaces/prog/serviceaccounts/prog/token",
		"POST /api/v1/namespaces/prog/serviceaccounts/prog/token",
	}
	if !slices.Equal(paths, want) {
		t.Fatalf("requests = %q, want %q: one SelfSubjectReview, then the TokenRequests", paths, want)
	}
	if want := `{"apiVersion":"authentication.k8s.io/v1","kind":"TokenRequest","spec":{"audiences":["octo-sts.dev"],"boundObjectRef":{"apiVersion":"v1","kind":"Pod","name":"prog-abc","uid":"uid-2"}}}`; bodies[1] != want {
		t.Errorf("TokenRequest =\n%s\nwant\n%s", bodies[1], want)
	}

	if _, _, err := RequestToken(ctx, ""); err == nil || !strings.Contains(err.Error(), "needs an audience") {
		t.Errorf("RequestToken without an audience: err = %v", err)
	}
	if n := len(a.sent()); n != 3 {
		t.Errorf("sent %d requests, want 3: none without an audience", n)
	}
}

// unsignedToken returns a JSON Web Token with claims and a fake signature.
func unsignedToken(claims string) string {
	enc := base64.RawURLEncoding.EncodeToString
	return enc([]byte(`{"alg":"RS256"}`)) + "." + enc([]byte(claims)) + "." + enc([]byte("signature"))
}

func TestRequestTokenFromDir(t *testing.T) {
	a, m := newAuthAPI(t, UserInfo{Username: "system:serviceaccount:prog:prog"})
	m.TokenDir = t.TempDir()
	ctx, _ := newWebhookScope(t.Context(), m)
	mount := func(audience, token string) {
		t.Helper()
		if err := os.WriteFile(filepath.Join(m.TokenDir, tokenFile(audience)), []byte(token), 0o600); err != nil {
			t.Fatal(err)
		}
	}
	exp := time.Now().Add(time.Hour).Truncate(time.Second)
	mounted := unsignedToken(fmt.Sprintf(`{"aud":["octo-sts.dev"],"exp":%d}`, exp.Unix()))
	mount("octo-sts.dev", mounted+"\n")
	token, expires, err := RequestToken(ctx, "octo-sts.dev")
	if err != nil || token != mounted || !expires.Equal(exp) {
		t.Errorf("RequestToken(octo-sts.dev) = %q, %v, %v, want the mounted token, which expires at %v", token, expires, err, exp)
	}
	renewed := unsignedToken(fmt.Sprintf(`{"aud":["octo-sts.dev"],"exp":%d}`, exp.Add(time.Hour).Unix()))
	mount("octo-sts.dev", renewed)
	if token, _, err := RequestToken(ctx, "octo-sts.dev"); err != nil || token != renewed {
		t.Errorf("RequestToken after the kubelet renewed the token = %q, %v, want the new token", token, err)
	}
	for audience, aud := range map[string]string{"one": `"one"`, "two": `["other.example","two"]`} {
		token := unsignedToken(fmt.Sprintf(`{"aud":%s,"exp":%d}`, aud, exp.Unix()))
		mount(audience, token)
		if got, _, err := RequestToken(ctx, audience); err != nil || got != token {
			t.Errorf("RequestToken(%q) with the aud claim %s = %q, %v, want the mounted token", audience, aud, got, err)
		}
	}
	if n := len(a.sent()); n != 0 {
		t.Errorf("sent %d requests for a mounted token, want none", n)
	}

	if token, _, err := RequestToken(ctx, "other"); err != nil || token != "requested" {
		t.Errorf("RequestToken(other) = %q, %v, want a token from a TokenRequest", token, err)
	}
	if n := len(a.sent()); n != 2 {
		t.Errorf("sent %d requests for an audience without a mounted token, want 2", n)
	}

	for _, tc := range []struct {
		audience, token, want string
	}{
		{"expired", unsignedToken(fmt.Sprintf(`{"aud":["expired"],"exp":%d}`, time.Now().Add(-time.Minute).Unix())), "expired at"},
		{"garbage", "garbage", "not a JSON Web Token"},
		{"empty", "", "not a JSON Web Token"},
		{"no expiry", unsignedToken(`{"aud":["no expiry"]}`), "no exp claim"},
		{"bad claims", "a.%%%.c", "decoding the claims"},
		{"no audience", unsignedToken(fmt.Sprintf(`{"exp":%d}`, exp.Unix())), "no aud claim"},
		{"another audience", unsignedToken(fmt.Sprintf(`{"aud":["sts.example"],"exp":%d}`, exp.Unix())), `the aud claim is ["sts.example"]`},
		{"another single audience", unsignedToken(fmt.Sprintf(`{"aud":"sts.example","exp":%d}`, exp.Unix())), `the aud claim is "sts.example"`},
	} {
		mount(tc.audience, tc.token)
		file := filepath.Join(m.TokenDir, tokenFile(tc.audience))
		if token, _, err := RequestToken(ctx, tc.audience); err == nil || token != "" || !strings.Contains(err.Error(), tc.want) || !strings.Contains(err.Error(), file) {
			t.Errorf("RequestToken(%q) = %q, %v, want an error that names %s and contains %q", tc.audience, token, err, file, tc.want)
		}
	}
	if n := len(a.sent()) - 2; n != 0 {
		t.Errorf("sent %d requests for unusable mounted tokens, want none", n)
	}
}

func TestRequestTokenWithoutAPod(t *testing.T) {
	a, m := newAuthAPI(t, UserInfo{Username: "system:serviceaccount:prog:prog"})
	ctx, _ := newWebhookScope(t.Context(), m)
	if _, _, err := RequestToken(ctx, "octo-sts.dev"); err != nil {
		t.Fatal(err)
	}
	if b, _ := json.Marshal(a.sent()[1].body); strings.Contains(string(b), "boundObjectRef") {
		t.Errorf("TokenRequest = %s, want no Pod binding for a token without one", b)
	}

	_, m = newAuthAPI(t, UserInfo{Username: "kubernetes-admin"})
	ctx, _ = newWebhookScope(t.Context(), m)
	if _, _, err := RequestToken(ctx, "octo-sts.dev"); err == nil || !strings.Contains(err.Error(), `runs as "kubernetes-admin", not as a service account`) {
		t.Errorf("RequestToken as a person: err = %v", err)
	}
}

// TestRequestTokenForbidden checks that when a program has neither a mounted
// token nor permission to request one, the error names the missing token
// and points to generate, not to the permission.
func TestRequestTokenForbidden(t *testing.T) {
	_, m := newAuthAPI(t, UserInfo{Username: "system:serviceaccount:prog:denied"})
	ctx, _ := newWebhookScope(t.Context(), m)
	for _, dir := range []string{"", t.TempDir()} {
		m.TokenDir = dir
		missing := `-token-dir isn't set, so there's no mounted token for "octo-sts.dev"`
		if dir != "" {
			missing = `there's no token for "octo-sts.dev" in ` + filepath.Join(dir, tokenFile("octo-sts.dev"))
		}
		token, _, err := RequestToken(ctx, "octo-sts.dev")
		if err == nil || token != "" {
			t.Fatalf("RequestToken with -token-dir=%q = %q, %v, want an error", dir, token, err)
		}
		for _, want := range []string{missing, "rerun the generate command", `cannot create resource "serviceaccounts/token"`} {
			if !strings.Contains(err.Error(), want) {
				t.Errorf("RequestToken with -token-dir=%q: err = %v, want it to contain %q", dir, err, want)
			}
		}
		if !client.IsForbidden(err) {
			t.Errorf("RequestToken with -token-dir=%q: err = %v, want it to wrap the 403", dir, err)
		}
	}
}

func TestFakeTokens(t *testing.T) {
	parent := &widget{}
	parent.Namespace, parent.Name = "shop", "w1"
	user := UserInfo{Username: "system:serviceaccount:checks:gofmt", Groups: []string{"system:serviceaccounts"}}
	ctx, _ := Fake(t.Context(), parent,
		FakeToken{Token: "check", User: user, Audiences: []string{"git-k8s"}},
		&FakeToken{Token: "api", User: user},
	)
	for _, tc := range []struct {
		token     string
		audiences []string
		want      []string
	}{
		{"check", []string{"git-k8s"}, []string{"git-k8s"}},
		{"check", []string{"other", "git-k8s"}, []string{"git-k8s"}},
		{"check", []string{"other"}, nil},
		{"check", []string{"https://kubernetes.default.svc"}, nil},
		{"api", []string{"https://kubernetes.default.svc"}, []string{"https://kubernetes.default.svc"}},
		{"api", []string{"git-k8s"}, nil},
		{"unknown", []string{"git-k8s"}, nil},
	} {
		r, err := ReviewToken(ctx, tc.token, tc.audiences[0], tc.audiences[1:]...)
		if err != nil {
			t.Fatal(err)
		}
		if r.Authenticated != (tc.want != nil) || !slices.Equal(r.Audiences, tc.want) || r.Authenticated && r.User.Username != user.Username || !r.Authenticated && r.Error == "" {
			t.Errorf("ReviewToken(%q, %q) = %+v, want audiences %q", tc.token, tc.audiences, r, tc.want)
		}
	}
	r, _ := ReviewToken(ctx, "check", "git-k8s")
	r.User.Groups[0] = "changed"
	if r, _ := ReviewToken(ctx, "check", "git-k8s"); r.User.Groups[0] != "system:serviceaccounts" {
		t.Error("changing a review changed the world")
	}

	token, expires, err := RequestToken(ctx, "octo-sts.dev")
	if err != nil || token != "fake-token-1" || time.Until(expires) < 59*time.Minute {
		t.Errorf("RequestToken = %q, %v, %v", token, expires, err)
	}
	r, _ = ReviewToken(ctx, token, "octo-sts.dev")
	if ns, name, ok := r.User.ServiceAccount(); !r.Authenticated || ns != "default" || name != "test" || !ok {
		t.Errorf("ReviewToken of the requested token = %+v", r)
	}
	if r, _ := ReviewToken(ctx, token, "git-k8s"); r.Authenticated {
		t.Errorf("the requested token passed for another audience: %+v", r)
	}
	if token, _, _ := RequestToken(ctx, "git-k8s"); token != "fake-token-2" {
		t.Errorf("the second token = %q", token)
	}
}

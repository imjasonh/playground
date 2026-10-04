package kube

import (
	"encoding/json"
	"net/http"
	"net/http/httptest"
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
			w.Header().Set("Content-Type", "application/json")
			w.WriteHeader(http.StatusForbidden)
			_, _ = w.Write([]byte(`{"kind":"Status","apiVersion":"v1","status":"Failure","reason":"Forbidden","code":403,"message":"tokenreviews.authentication.k8s.io is forbidden"}`))
		default:
			reply(map[string]any{"error": "invalid bearer token"})
		}
	case "/apis/authentication.k8s.io/v1/selfsubjectreviews":
		reply(map[string]any{"userInfo": a.self})
	case "/api/v1/namespaces/prog/serviceaccounts/prog/token":
		reply(map[string]any{"token": "requested", "expirationTimestamp": "2030-01-02T03:04:05Z"})
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

	token, expires, err := RequestToken(ctx, "octo-sts.dev", 20*time.Minute)
	if err != nil || token != "requested" || !expires.Equal(time.Date(2030, 1, 2, 3, 4, 5, 0, time.UTC)) {
		t.Fatalf("RequestToken = %q, %v, %v", token, expires, err)
	}
	if _, _, err := RequestToken(ctx, "octo-sts.dev", 0); err != nil {
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
	if want := `{"apiVersion":"authentication.k8s.io/v1","kind":"TokenRequest","spec":{"audiences":["octo-sts.dev"],"boundObjectRef":{"apiVersion":"v1","kind":"Pod","name":"prog-abc","uid":"uid-2"},"expirationSeconds":1200}}`; bodies[1] != want {
		t.Errorf("TokenRequest =\n%s\nwant\n%s", bodies[1], want)
	}
	if strings.Contains(bodies[2], "expirationSeconds") {
		t.Errorf("TokenRequest without a lifetime = %s, want the API server's default", bodies[2])
	}

	for _, tc := range []struct {
		audience string
		lifetime time.Duration
		want     string
	}{
		{"", time.Hour, "needs an audience"},
		{"octo-sts.dev", time.Minute, "minimum of 10 minutes"},
	} {
		if _, _, err := RequestToken(ctx, tc.audience, tc.lifetime); err == nil || !strings.Contains(err.Error(), tc.want) {
			t.Errorf("RequestToken(%q, %v): err = %v, want %q", tc.audience, tc.lifetime, err, tc.want)
		}
	}
	if n := len(a.sent()); n != 3 {
		t.Errorf("sent %d requests, want 3: none for invalid arguments", n)
	}
}

func TestRequestTokenWithoutAPod(t *testing.T) {
	a, m := newAuthAPI(t, UserInfo{Username: "system:serviceaccount:prog:prog"})
	ctx, _ := newWebhookScope(t.Context(), m)
	if _, _, err := RequestToken(ctx, "octo-sts.dev", 0); err != nil {
		t.Fatal(err)
	}
	if b, _ := json.Marshal(a.sent()[1].body); strings.Contains(string(b), "boundObjectRef") {
		t.Errorf("TokenRequest = %s, want no Pod binding for a token without one", b)
	}

	_, m = newAuthAPI(t, UserInfo{Username: "kubernetes-admin"})
	ctx, _ = newWebhookScope(t.Context(), m)
	if _, _, err := RequestToken(ctx, "octo-sts.dev", 0); err == nil || !strings.Contains(err.Error(), `runs as "kubernetes-admin", not as a service account`) {
		t.Errorf("RequestToken as a person: err = %v", err)
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

	token, expires, err := RequestToken(ctx, "octo-sts.dev", 0)
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
	if token, _, _ := RequestToken(ctx, "git-k8s", 0); token != "fake-token-2" {
		t.Errorf("the second token = %q", token)
	}
}

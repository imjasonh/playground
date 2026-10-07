package main

import (
	"context"
	"encoding/json"
	"errors"
	"maps"
	"net/http"
	"net/http/httptest"
	"slices"
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

var branchKey = kube.Key{Namespace: "default", Name: "app-c-x"}

// listedBranch returns c/x at generation 3, whose merge policy lists the
// base and gofmt checks.
func listedBranch() *resultsBranch {
	b := &resultsBranch{Object: kube.Meta("app-c-x", nil)}
	b.Namespace, b.Generation = "default", 3
	b.Spec = gitk8s.GitBranchSpec{Repository: "app", Branch: "c/x", Head: "h1", Parent: "main", ParentHead: "p1", Merge: policy}
	return b
}

// checkToken returns a token for the results endpoint from the service
// account that generate installs the check's program with.
func checkToken(check string) kube.FakeToken {
	sa := "check-" + check
	return kube.FakeToken{Token: check, User: kube.UserInfo{Username: "system:serviceaccount:" + sa + ":" + sa}, Audiences: []string{gitk8s.ResultsAudience}}
}

// checksEntries returns the git-k8s-checks ConfigMap with entries.
func checksEntries(entries map[string]string) *k8s.ConfigMap {
	cm := &k8s.ConfigMap{Object: kube.Meta(caller.ChecksConfigMap, nil), Data: entries}
	cm.Namespace = caller.ChecksNamespace
	return cm
}

// sendResult sends body, a result or raw JSON, to the results endpoint
// with token, in a request context from kube.FakeRequest. A token with a
// space in it is the whole Authorization header.
func sendResult(ctx context.Context, rs *results, path, token string, body any) *httptest.ResponseRecorder {
	raw, ok := body.(string)
	if !ok {
		b, _ := json.Marshal(body)
		raw = string(b)
	}
	req := httptest.NewRequest(http.MethodPut, path, strings.NewReader(raw)).WithContext(ctx)
	if token != "" {
		if !strings.Contains(token, " ") {
			token = "Bearer " + token
		}
		req.Header.Set("Authorization", token)
	}
	w := httptest.NewRecorder()
	rs.handler().ServeHTTP(w, req)
	return w
}

func entry(b *resultsBranch, check string) *gitk8s.CheckResult {
	if r, ok := b.Status.Checks[check]; ok {
		return &r
	}
	return nil
}

func TestResultsEndpointRejects(t *testing.T) {
	b := listedBranch()
	base := gitk8s.CheckResult{Commit: "h1", Scope: gitk8s.ScopeParent, ParentCommit: "p1", State: gitk8s.Passed}
	b.Status.Checks = map[string]gitk8s.CheckResult{"base": base}
	gofmtUser := checkToken("gofmt").User
	main := &resultsBranch{Object: kube.Meta("app-main", nil)}
	main.Namespace, main.Spec = "default", gitk8s.GitBranchSpec{Repository: "app", Branch: "main", Head: "p1"}
	world := []any{
		b, main, checkToken("base"), checkToken("gofmt"), checkToken("risk"), checkToken("lint"),
		kube.FakeToken{Token: "api", User: gofmtUser},
		kube.FakeToken{Token: "ci", User: kube.UserInfo{Username: "system:serviceaccount:default:ci"}, Audiences: []string{gitk8s.ResultsAudience}},
		kube.FakeToken{Token: "elsewhere", User: kube.UserInfo{Username: "system:serviceaccount:default:check-gofmt"}, Audiences: []string{gitk8s.ResultsAudience}},
		kube.FakeToken{Token: "admin", User: kube.UserInfo{Username: "kubernetes-admin"}, Audiences: []string{gitk8s.ResultsAudience}},
		kube.FakeToken{Token: "bot", User: kube.UserInfo{Username: "system:serviceaccount:ci:base-bot"}, Audiences: []string{gitk8s.ResultsAudience}},
		kube.FakeToken{Token: "approval", User: kube.UserInfo{Username: "system:serviceaccount:checks:check-approval"}, Audiences: []string{gitk8s.ResultsAudience}},
		kube.FakeToken{Token: "core", User: kube.UserInfo{Username: "system:serviceaccount:git-k8s:git-k8s"}, Audiences: []string{gitk8s.ResultsAudience}},
		checksEntries(map[string]string{"ci.base-bot": "base", "checks.check-approval": "approval", "check-lint.check-lint": "", "git-k8s.git-k8s": "gofmt"}),
	}
	rs := &results{timeout: time.Minute, poll: time.Millisecond}
	fresh := &gitk8s.CheckResult{Commit: "h1", Scope: gitk8s.ScopeHead, State: gitk8s.Passed}
	const gofmt = "/results/default/app-c-x/gofmt?generation=3"
	for _, tc := range []struct {
		name, path, token string
		body              any
		code              int
		msg               string
	}{
		{"no Authorization header", gofmt, "", fresh, http.StatusUnauthorized, "the request has no Bearer token"},
		{"another scheme", gofmt, "Basic Z29mbXQ6", fresh, http.StatusUnauthorized, "the request has no Bearer token"},
		{"no token", gofmt, "Bearer ", fresh, http.StatusUnauthorized, "no token"},
		{"a lowercase scheme", "/results/default/app-main/gofmt", "bearer gofmt", fresh, http.StatusConflict, "main has no parent, so it takes no check results"},
		{"a token for the API server", gofmt, "api", fresh, http.StatusUnauthorized, "is invalid for the target audiences"},
		{"a service account that isn't a check", gofmt, "ci", fresh, http.StatusForbidden, "system:serviceaccount:default:ci isn't a check's service account"},
		{"a check's account name in another namespace", gofmt, "elsewhere", fresh, http.StatusForbidden, "isn't a check's service account"},
		{"a person", gofmt, "admin", fresh, http.StatusForbidden, "kubernetes-admin isn't a check's service account"},
		{"another check's entry", gofmt, "base", fresh, http.StatusForbidden, "system:serviceaccount:check-base:check-base is the base check, so it can't write the gofmt check's result"},
		{"a check through its ConfigMap entry", "/results/default/app-c-x/base?generation=3", "bot", &base, http.StatusNoContent, ""},
		{"another check's entry through a ConfigMap entry", gofmt, "approval", fresh, http.StatusForbidden, "system:serviceaccount:checks:check-approval is the approval check, so it can't write the gofmt check's result"},
		{"a ConfigMap entry that says the account isn't a check", "/results/default/app-c-x/lint?generation=3", "lint", fresh, http.StatusForbidden, "system:serviceaccount:check-lint:check-lint isn't a check's service account"},
		{"the core program, despite its ConfigMap entry", gofmt, "core", fresh, http.StatusForbidden, "system:serviceaccount:git-k8s:git-k8s isn't a check's service account"},
		{"invalid JSON", gofmt, "gofmt", `{"commit":`, http.StatusBadRequest, "decoding the result"},
		{"another value after the result", gofmt, "gofmt", `{"commit":"h1","scope":"Head","state":"Passed"} {}`, http.StatusBadRequest, "the request has data after the result"},
		{"a brace after the result", gofmt, "gofmt", `{"commit":"h1","scope":"Head","state":"Passed"}}`, http.StatusBadRequest, "the request has data after the result"},
		{"a newline after the result", "/results/default/app-c-x/base?generation=3", "base", `{"commit":"h1","scope":"Parent","parentCommit":"p1","state":"Passed"}` + "\n", http.StatusNoContent, ""},
		{"a field that the core program doesn't know", "/results/default/app-c-x/base?generation=3", "base", `{"commit":"h1","scope":"Parent","parentCommit":"p1","state":"Passed","approved":true}`, http.StatusBadRequest, `unknown field "approved"`},
		{"a body that's too large", gofmt, "gofmt", `{"commit":"h1","scope":"Head","state":"Passed","message":"` + strings.Repeat("x", maxResultSize) + `"}`, http.StatusBadRequest, "too large"},
		{"a state that checks can't send", gofmt, "gofmt", &gitk8s.CheckResult{Commit: "h1", Scope: gitk8s.ScopeHead, State: gitk8s.Pending}, http.StatusBadRequest, `state "Pending" isn't`},
		{"no scope", gofmt, "gofmt", `{"commit":"h1","state":"Passed"}`, http.StatusBadRequest, "the result has no scope"},
		{"a scope that the core program doesn't know", gofmt, "gofmt", `{"commit":"h1","scope":"Tree","state":"Passed"}`, http.StatusBadRequest, `scope "Tree" isn't Head, Parent, or Change`},
		{"a scope without the field that it needs", "/results/default/app-c-x/base?generation=3", "base", `{"commit":"h1","scope":"Parent","state":"Passed"}`, http.StatusBadRequest, "a result with the scope Parent has parentCommit"},
		{"an invalid generation", "/results/default/app-c-x/gofmt?generation=new", "gofmt", fresh, http.StatusBadRequest, "generation"},
		{"a check that the policy doesn't list", "/results/default/app-c-x/risk?generation=3", "risk", fresh, http.StatusConflict, "the merge policy for c/x doesn't list the risk check"},
		{"a branch without a parent", "/results/default/app-main/gofmt", "gofmt", fresh, http.StatusConflict, "main has no parent, so it takes no check results"},
		{"another head", gofmt, "gofmt", &gitk8s.CheckResult{Commit: "h0", Scope: gitk8s.ScopeHead, State: gitk8s.Passed}, http.StatusConflict, "the result isn't for c/x at h1 and main at p1"},
		{"another parent head", "/results/default/app-c-x/base?generation=3", "base", &gitk8s.CheckResult{Commit: "h1", Scope: gitk8s.ScopeParent, ParentCommit: "p0", State: gitk8s.Passed}, http.StatusConflict, "the result isn't for c/x"},
		{"a result that's already written", "/results/default/app-c-x/base?generation=3", "base", &base, http.StatusNoContent, ""},
	} {
		t.Run(tc.name, func(t *testing.T) {
			ctx, rec := kube.FakeRequest(t.Context(), world...)
			w := sendResult(ctx, rs, tc.path, tc.token, tc.body)
			if w.Code != tc.code || !strings.Contains(w.Body.String(), tc.msg) {
				t.Errorf("got %d %q, want %d %q", w.Code, w.Body, tc.code, tc.msg)
			}
			if tc.code == http.StatusUnauthorized && w.Header().Get("WWW-Authenticate") != "Bearer" {
				t.Errorf("WWW-Authenticate = %q, want Bearer", w.Header().Get("WWW-Authenticate"))
			}
			if got := kube.Triggered[resultsBranch](rec); len(got) != 0 {
				t.Errorf("triggered %v without a new result to write", got)
			}
			if err := rec.Err(); err != nil {
				t.Error(err)
			}
		})
	}
	if len(rs.held) != 0 {
		t.Errorf("holds %v after the requests ended", rs.held)
	}
}

// Without the git-k8s-checks ConfigMap, only generate's convention maps
// service accounts to checks.
func TestResultsEndpointWithoutChecksConfigMap(t *testing.T) {
	b := listedBranch()
	base := gitk8s.CheckResult{Commit: "h1", Scope: gitk8s.ScopeParent, ParentCommit: "p1", State: gitk8s.Passed}
	b.Status.Checks = map[string]gitk8s.CheckResult{"base": base}
	bot := kube.FakeToken{Token: "bot", User: kube.UserInfo{Username: "system:serviceaccount:ci:base-bot"}, Audiences: []string{gitk8s.ResultsAudience}}
	rs := &results{timeout: time.Minute, poll: time.Millisecond}
	const path = "/results/default/app-c-x/base?generation=3"
	for token, code := range map[string]int{"base": http.StatusNoContent, "bot": http.StatusForbidden} {
		ctx, rec := kube.FakeRequest(t.Context(), b, checkToken("base"), bot)
		if w := sendResult(ctx, rs, path, token, &base); w.Code != code {
			t.Errorf("with the %s token, got %d %q, want %d", token, w.Code, w.Body, code)
		}
		if err := rec.Err(); err != nil {
			t.Error(err)
		}
	}
}

func TestResultsEndpointTimesOut(t *testing.T) {
	ctx, rec := kube.FakeRequest(t.Context(), listedBranch(), checkToken("gofmt"))
	rs := &results{timeout: 20 * time.Millisecond, poll: time.Millisecond, fetch: func(context.Context, string, string) (*resultsBranch, error) {
		t.Error("read the branch from the API server, although the cache has it")
		return nil, nil
	}}
	w := sendResult(ctx, rs, "/results/default/app-c-x/gofmt?generation=3", "gofmt", &gitk8s.CheckResult{Commit: "h1", Scope: gitk8s.ScopeHead, State: gitk8s.Passed})
	if w.Code != http.StatusServiceUnavailable || !strings.Contains(w.Body.String(), "wasn't written in time") {
		t.Errorf("got %d %q, want 503 because nothing wrote the result", w.Code, w.Body)
	}
	if w.Header().Get("Connection") != "close" {
		t.Error("a 503 must close the connection, so that the next try can reach another replica")
	}
	if got, want := kube.Triggered[resultsBranch](rec), []kube.Key{branchKey}; !slices.Equal(got, want) {
		t.Errorf("Triggered = %v, want %v", got, want)
	}
	if len(rs.held) != 0 {
		t.Errorf("holds %v after answering", rs.held)
	}
	if err := rec.Err(); err != nil {
		t.Error(err)
	}
}

// A replica that doesn't reconcile the branch, such as one that doesn't
// hold the branch's shard, answers 503 at once and closes the connection,
// so that the check's next try can reach the replica that does.
func TestResultsEndpointOnStandby(t *testing.T) {
	ctx, rec := kube.FakeRequest(t.Context(), listedBranch(), checkToken("gofmt"), kube.FakeStandby{})
	rs := &results{timeout: time.Minute, poll: time.Millisecond}
	w := sendResult(ctx, rs, "/results/default/app-c-x/gofmt?generation=3", "gofmt", &gitk8s.CheckResult{Commit: "h1", Scope: gitk8s.ScopeHead, State: gitk8s.Passed})
	if w.Code != http.StatusServiceUnavailable || !strings.Contains(w.Body.String(), "this replica doesn't write the branch's results") {
		t.Errorf("got %d %q, want 503 from a replica that doesn't write the branch's results", w.Code, w.Body)
	}
	if w.Header().Get("Connection") != "close" {
		t.Error("a 503 must close the connection, so that the next try can reach another replica")
	}
	if len(rs.held) != 0 {
		t.Errorf("holds %v after answering", rs.held)
	}
	if err := rec.Err(); err != nil {
		t.Error(err)
	}
}

// A Get that can't read returns nil and cancels the request's context. The
// branch may exist, so the endpoint answers 503 rather than 410. The fake
// can't fail a read, so the test cancels the context and leaves the branch
// out of the world.
func TestResultsEndpointCantRead(t *testing.T) {
	ctx, cancel := context.WithCancelCause(t.Context())
	cancel(errors.New("reading GitBranches: forbidden"))
	ctx, _ = kube.FakeRequest(ctx, checkToken("gofmt"))
	rs := &results{timeout: time.Minute, poll: time.Millisecond}
	w := sendResult(ctx, rs, "/results/default/app-c-x/gofmt?generation=3", "gofmt", &gitk8s.CheckResult{Commit: "h1", Scope: gitk8s.ScopeHead, State: gitk8s.Passed})
	if w.Code != http.StatusServiceUnavailable || w.Header().Get("Connection") != "close" {
		t.Errorf("got %d %q, want 503 and a closed connection", w.Code, w.Body)
	}
}

// A check that read a newer spec than this replica's cache has waits for
// the cache, so that its result isn't checked against an older spec. The
// API server shows the newer spec, so the request keeps waiting, and it
// reads the API server at most once every refetch.
func TestResultsEndpointWaitsForGeneration(t *testing.T) {
	ctx, rec := kube.FakeRequest(t.Context(), listedBranch(), checkToken("gofmt"))
	reads := 0
	rs := &results{timeout: 20 * time.Millisecond, poll: time.Millisecond, refetch: time.Hour, fetch: func(context.Context, string, string) (*resultsBranch, error) {
		reads++
		b := listedBranch()
		b.Generation = 4
		return b, nil
	}}
	w := sendResult(ctx, rs, "/results/default/app-c-x/gofmt?generation=4", "gofmt", &gitk8s.CheckResult{Commit: "h2", Scope: gitk8s.ScopeHead, State: gitk8s.Passed})
	if w.Code != http.StatusServiceUnavailable {
		t.Errorf("got %d %q, want 503 while the cache has generation 3", w.Code, w.Body)
	}
	if reads != 1 {
		t.Errorf("read the branch from the API server %d times, want once", reads)
	}
	if got := kube.Triggered[resultsBranch](rec); len(got) != 0 {
		t.Errorf("triggered %v before the cache had the spec that the check read", got)
	}
	if err := rec.Err(); err != nil {
		t.Error(err)
	}
}

// A check can send a result for a branch that's gone, as when the merge
// controller deletes a branch that landed while a check ran on it. The
// cache doesn't show the branch at the generation that the check read, so
// the request reads the API server, and answers at once rather than after
// the wait for the cache.
func TestResultsEndpointBranchGone(t *testing.T) {
	recreated := listedBranch()
	recreated.Generation = 1
	for _, tc := range []struct {
		name  string
		world []any
		path  string
		// fetch, if set, is the API server's view of the branch, which
		// is otherwise the cache's.
		fetch func(context.Context, string, string) (*resultsBranch, error)
		code  int
		msg   string
	}{
		{"deleted", nil, "/results/default/app-c-x/gofmt?generation=3", nil, http.StatusGone, "GitBranch default/app-c-x doesn't exist"},
		{
			"deleted after the cache's generation", []any{listedBranch()}, "/results/default/app-c-x/gofmt?generation=4",
			func(context.Context, string, string) (*resultsBranch, error) { return nil, nil },
			http.StatusGone, "GitBranch default/app-c-x doesn't exist",
		},
		{
			"deleted and created again", []any{recreated}, "/results/default/app-c-x/gofmt?generation=3", nil,
			http.StatusConflict, "the check read generation 3 of GitBranch default/app-c-x, which is at generation 1, so it was deleted and created again",
		},
	} {
		t.Run(tc.name, func(t *testing.T) {
			ctx, rec := kube.FakeRequest(t.Context(), append(tc.world, checkToken("gofmt"))...)
			rs := &results{timeout: time.Minute, poll: time.Millisecond, refetch: time.Second, fetch: tc.fetch}
			start := time.Now()
			w := sendResult(ctx, rs, tc.path, "gofmt", &gitk8s.CheckResult{Commit: "h1", Scope: gitk8s.ScopeHead, State: gitk8s.Passed})
			if w.Code != tc.code || !strings.Contains(w.Body.String(), tc.msg) {
				t.Errorf("got %d %q, want %d %q", w.Code, w.Body, tc.code, tc.msg)
			}
			if elapsed := time.Since(start); elapsed > time.Second {
				t.Errorf("answered after %v, want an answer well under a second", elapsed)
			}
			if got := kube.Triggered[resultsBranch](rec); len(got) != 0 {
				t.Errorf("triggered %v for a branch that's gone", got)
			}
			if len(rs.held) != 0 {
				t.Errorf("holds %v after answering", rs.held)
			}
			if err := rec.Err(); err != nil {
				t.Error(err)
			}
		})
	}
}

// A check can read a branch before this replica's cache has it. The API
// server shows the branch, so the request waits for the cache, and once the
// cache has the branch, the request hands its result off as usual.
func TestResultsEndpointWaitsForBranch(t *testing.T) {
	res := &gitk8s.CheckResult{Commit: "h1", Scope: gitk8s.ScopeHead, State: gitk8s.Passed}
	missing, _ := kube.FakeRequest(t.Context(), checkToken("gofmt"))
	ctx := &changingCache{Context: t.Context(), world: missing}
	var reads atomic.Int32
	rs := &results{timeout: time.Minute, poll: time.Millisecond, refetch: time.Hour, fetch: func(context.Context, string, string) (*resultsBranch, error) {
		reads.Add(1)
		return listedBranch(), nil
	}}
	answered := make(chan *httptest.ResponseRecorder, 1)
	go func() { answered <- sendResult(ctx, rs, "/results/default/app-c-x/gofmt?generation=3", "gofmt", res) }()
	waitFor := func(what string, cond func() bool) {
		t.Helper()
		for !cond() {
			select {
			case w := <-answered:
				t.Fatalf("got %d %q before the request %s", w.Code, w.Body, what)
			case <-time.After(time.Millisecond):
			}
		}
	}
	waitFor("read the API server", func() bool { return reads.Load() > 0 })

	t.Log("The cache gets the branch, so the request holds its result and triggers a reconcile, which writes it.")
	cached, rec := kube.FakeRequest(t.Context(), listedBranch(), checkToken("gofmt"))
	ctx.set(cached)
	waitFor("held its result", func() bool { return rs.heldFor(branchKey)["gofmt"] != nil })
	b := listedBranch()
	rctx, _ := kube.Fake(t.Context(), b)
	if err := rs.Reconcile(rctx, b); err != nil {
		t.Fatal(err)
	}
	written, _ := kube.FakeRequest(t.Context(), b, checkToken("gofmt"))
	ctx.set(written)
	if w := <-answered; w.Code != http.StatusNoContent {
		t.Errorf("got %d %q, want 204 once the cache shows the result", w.Code, w.Body)
	}
	if n := reads.Load(); n != 1 {
		t.Errorf("read the branch from the API server %d times, want once", n)
	}
	if got, want := kube.Triggered[resultsBranch](rec), []kube.Key{branchKey}; !slices.Equal(got, want) {
		t.Errorf("Triggered = %v, want %v", got, want)
	}
	if len(rs.held) != 0 {
		t.Errorf("holds %v after answering", rs.held)
	}
}

// changingCache is the context of a request that reads the world of a
// FakeRequest context, which a test replaces while the request waits, as
// if this replica's cache changed.
type changingCache struct {
	context.Context
	mu    sync.Mutex
	world context.Context
}

func (c *changingCache) Value(key any) any {
	c.mu.Lock()
	world := c.world
	c.mu.Unlock()
	return world.Value(key)
}

func (c *changingCache) set(world context.Context) {
	c.mu.Lock()
	defer c.mu.Unlock()
	c.world = world
}

// A request that can't read the branch from the API server keeps waiting
// for the cache, and then answers 503 rather than 410, because the branch
// may exist, so that the check tries again. A read that gets no answer
// ends when the request stops waiting.
func TestResultsEndpointCantFetch(t *testing.T) {
	for _, tc := range []struct {
		name string
		err  func(context.Context) error
	}{
		{"an error", func(context.Context) error { return errors.New("the API server is unavailable") }},
		{"no answer", func(ctx context.Context) error {
			select {
			case <-ctx.Done():
				return ctx.Err()
			case <-time.After(time.Minute):
				return errors.New("the API server didn't answer")
			}
		}},
	} {
		t.Run(tc.name, func(t *testing.T) {
			ctx, rec := kube.FakeRequest(t.Context(), checkToken("gofmt"))
			reads := 0
			rs := &results{timeout: 20 * time.Millisecond, poll: time.Millisecond, refetch: time.Hour, fetch: func(ctx context.Context, _, _ string) (*resultsBranch, error) {
				reads++
				return nil, tc.err(ctx)
			}}
			start := time.Now()
			w := sendResult(ctx, rs, "/results/default/app-c-x/gofmt?generation=3", "gofmt", &gitk8s.CheckResult{Commit: "h1", Scope: gitk8s.ScopeHead, State: gitk8s.Passed})
			elapsed := time.Since(start)
			if w.Code != http.StatusServiceUnavailable || w.Header().Get("Connection") != "close" {
				t.Errorf("got %d %q, want 503 and a closed connection", w.Code, w.Body)
			}
			if elapsed < rs.timeout || elapsed > rs.timeout+5*time.Second {
				t.Errorf("answered after %v, want a wait of %v for the cache", elapsed, rs.timeout)
			}
			if reads != 1 {
				t.Errorf("read the branch from the API server %d times, want once", reads)
			}
			if got := kube.Triggered[resultsBranch](rec); len(got) != 0 {
				t.Errorf("triggered %v for a branch that the cache doesn't have", got)
			}
			if err := rec.Err(); err != nil {
				t.Error(err)
			}
		})
	}
}

// A request holds its result and triggers a reconcile of the branch, which
// writes the result. The reconcile leaves the result held, so that a retry
// after a failed write still writes it, and the request stops holding it
// when it gives up. A request whose result the cache shows answers 204.
func TestResultsHandOff(t *testing.T) {
	res := &gitk8s.CheckResult{Commit: "h1", Scope: gitk8s.ScopeHead, State: gitk8s.Failed, Message: "x.go isn't formatted"}
	const path = "/results/default/app-c-x/gofmt?generation=3"
	rs := &results{timeout: time.Minute, poll: time.Millisecond}
	ctx, cancel := context.WithCancel(t.Context())
	ctx, rec := kube.FakeRequest(ctx, listedBranch(), checkToken("gofmt"))
	done := make(chan struct{})
	go func() {
		defer close(done)
		sendResult(ctx, rs, path, "gofmt", res)
	}()
	for rs.heldFor(branchKey)["gofmt"] == nil {
		select {
		case <-done:
			t.Fatal("the request ended without holding its result")
		case <-time.After(time.Millisecond):
		}
	}

	base := gitk8s.CheckResult{Commit: "h1", Scope: gitk8s.ScopeParent, ParentCommit: "p1", State: gitk8s.Passed}
	var b *resultsBranch
	for _, attempt := range []string{"the reconcile", "a retry after the write failed"} {
		b = listedBranch()
		b.Status.Checks = map[string]gitk8s.CheckResult{"base": base}
		rctx, _ := kube.Fake(t.Context(), b)
		if err := rs.Reconcile(rctx, b); err != nil {
			t.Fatal(err)
		}
		if !entry(b, "gofmt").Equal(res) || !entry(b, "base").Equal(&base) {
			t.Errorf("after %s, status.checks = %+v, want the held gofmt result and the base result", attempt, b.Status.Checks)
		}
	}

	cancel()
	<-done
	if got, want := kube.Triggered[resultsBranch](rec), []kube.Key{branchKey}; !slices.Equal(got, want) {
		t.Errorf("Triggered = %v, want %v", got, want)
	}
	if len(rs.held) != 0 {
		t.Errorf("holds %v after the request ended", rs.held)
	}
	if err := rec.Err(); err != nil {
		t.Error(err)
	}

	ctx, rec = kube.FakeRequest(t.Context(), b, checkToken("gofmt"))
	if w := sendResult(ctx, rs, path, "gofmt", res); w.Code != http.StatusNoContent {
		t.Errorf("with the result written, got %d %q, want 204", w.Code, w.Body)
	}
	if got := kube.Triggered[resultsBranch](rec); len(got) != 0 {
		t.Errorf("triggered %v for a result that's already written", got)
	}
	if len(rs.held) != 0 {
		t.Errorf("holds %v for a result that's already written", rs.held)
	}
}

// A request that ends stops holding its result, but not a newer result from
// the same check that replaced it.
func TestReleaseKeepsNewerResult(t *testing.T) {
	rs := &results{}
	older, newer := &gitk8s.CheckResult{Commit: "h0"}, &gitk8s.CheckResult{Commit: "h1"}
	rs.hold(branchKey, "gofmt", older)
	rs.hold(branchKey, "gofmt", newer)
	rs.release(branchKey, "gofmt", older)
	if got := rs.heldFor(branchKey)["gofmt"]; got != newer {
		t.Errorf("holds %+v, want the newer result", got)
	}
	rs.release(branchKey, "gofmt", newer)
	if len(rs.held) != 0 {
		t.Errorf("holds %v after every request ended", rs.held)
	}
}

func TestResultsReconcile(t *testing.T) {
	fresh := gitk8s.CheckResult{Commit: "h1", Scope: gitk8s.ScopeHead, State: gitk8s.Passed}
	stale := gitk8s.CheckResult{Commit: "h0", Scope: gitk8s.ScopeHead, State: gitk8s.Failed}
	base := gitk8s.CheckResult{Commit: "h1", Scope: gitk8s.ScopeParent, ParentCommit: "p1", State: gitk8s.Passed}
	for _, tc := range []struct {
		name   string
		parent string
		status map[string]gitk8s.CheckResult
		held   map[string]*gitk8s.CheckResult
		want   map[string]gitk8s.CheckResult
	}{{
		name:   "writes a held result and keeps the other entries",
		status: map[string]gitk8s.CheckResult{"base": base},
		held:   map[string]*gitk8s.CheckResult{"gofmt": &fresh},
		want:   map[string]gitk8s.CheckResult{"base": base, "gofmt": fresh},
	}, {
		name:   "replaces a check's earlier result",
		status: map[string]gitk8s.CheckResult{"gofmt": stale},
		held:   map[string]*gitk8s.CheckResult{"gofmt": &fresh},
		want:   map[string]gitk8s.CheckResult{"gofmt": fresh},
	}, {
		name:   "keeps a stale result until the check sends a new one",
		status: map[string]gitk8s.CheckResult{"gofmt": stale},
		want:   map[string]gitk8s.CheckResult{"gofmt": stale},
	}, {
		name:   "removes the results of checks that the policy doesn't list",
		status: map[string]gitk8s.CheckResult{"base": base, "risk": fresh},
		want:   map[string]gitk8s.CheckResult{"base": base},
	}, {
		name: "ignores a held result for a head that moved",
		held: map[string]*gitk8s.CheckResult{"gofmt": &stale},
	}, {
		name: "ignores a held result for a check that the policy doesn't list",
		held: map[string]*gitk8s.CheckResult{"risk": &fresh},
	}, {
		name:   "writes an empty map to remove the last entry",
		status: map[string]gitk8s.CheckResult{"risk": fresh},
		want:   map[string]gitk8s.CheckResult{},
	}, {
		name:   "removes every result from a branch without a parent",
		parent: "-",
		status: map[string]gitk8s.CheckResult{"gofmt": fresh},
		held:   map[string]*gitk8s.CheckResult{"base": &base},
		want:   map[string]gitk8s.CheckResult{},
	}} {
		t.Run(tc.name, func(t *testing.T) {
			b := listedBranch()
			if tc.parent == "-" {
				b.Spec.Parent, b.Spec.ParentHead = "", ""
			}
			b.Status.Checks = tc.status
			rs := &results{}
			for check, r := range tc.held {
				rs.hold(branchKey, check, r)
			}
			ctx, _ := kube.Fake(t.Context(), b)
			if err := rs.Reconcile(ctx, b); err != nil {
				t.Fatal(err)
			}
			equal := func(a, b gitk8s.CheckResult) bool { return a.Equal(&b) }
			if got := b.Status.Checks; !maps.EqualFunc(got, tc.want, equal) || (got == nil) != (tc.want == nil) {
				t.Errorf("status.checks = %#v, want %#v", got, tc.want)
			}
		})
	}
}

// The reconcile writes the entries that the cache shows rather than those
// of the object that it was called with, which can be older: a request
// stops holding its result once the cache shows it written.
func TestResultsReconcileRereadsTheCache(t *testing.T) {
	old, cur := listedBranch(), listedBranch()
	fresh := gitk8s.CheckResult{Commit: "h1", Scope: gitk8s.ScopeHead, State: gitk8s.Passed}
	cur.Status.Checks = map[string]gitk8s.CheckResult{"gofmt": fresh}
	ctx, _ := kube.Fake(t.Context(), old, cur)
	if err := (&results{}).Reconcile(ctx, old); err != nil {
		t.Fatal(err)
	}
	if !entry(old, "gofmt").Equal(&fresh) {
		t.Errorf("status.checks = %+v, want the gofmt result that the cache shows", old.Status.Checks)
	}
}

func TestCheckFor(t *testing.T) {
	entries := map[string]string{
		"checks.check-approval": "approval",
		"ci.gofmt-bot":          "gofmt",
		"check-risk.check-risk": "",
		"git-k8s.git-k8s":       "gofmt",
	}
	for _, tc := range []struct {
		user    string
		entries map[string]string
		want    string
	}{
		{"system:serviceaccount:check-gofmt:check-gofmt", nil, "gofmt"},
		{"system:serviceaccount:check-my-lint:check-my-lint", nil, "my-lint"},
		{"system:serviceaccount:default:check-gofmt", nil, ""},
		{"system:serviceaccount:check-gofmt:default", nil, ""},
		{"system:serviceaccount:check-:check-", nil, ""},
		{"system:serviceaccount:git-k8s:git-k8s", nil, ""},
		{"system:serviceaccount:checks:check-approval", nil, ""},
		{"check-gofmt", nil, ""},
		{"kubernetes-admin", nil, ""},
		{"system:serviceaccount:check-gofmt:check-gofmt", entries, "gofmt"},
		{"system:serviceaccount:checks:check-approval", entries, "approval"},
		{"system:serviceaccount:ci:gofmt-bot", entries, "gofmt"},
		{"system:serviceaccount:check-risk:check-risk", entries, ""},
		{"system:serviceaccount:git-k8s:git-k8s", entries, ""},
		{"system:serviceaccount:ci:other-bot", entries, ""},
	} {
		got, ok := checkFor(kube.UserInfo{Username: tc.user}, tc.entries)
		if got != tc.want || ok != (tc.want != "") {
			t.Errorf("checkFor(%s, %v) = %q, %v; want %q", tc.user, tc.entries, got, ok, tc.want)
		}
	}
}

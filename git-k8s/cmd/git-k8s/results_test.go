package main

import (
	"context"
	"encoding/json"
	"maps"
	"net/http"
	"net/http/httptest"
	"slices"
	"strings"
	"testing"
	"time"

	gitk8s "github.com/imjasonh/playground/git-k8s"
	"github.com/imjasonh/playground/kube"
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

// sendResult sends body, a result or raw JSON, to the results endpoint
// with token, in a context from kube.Fake.
func sendResult(ctx context.Context, rs *results, path, token string, body any) *httptest.ResponseRecorder {
	raw, ok := body.(string)
	if !ok {
		b, _ := json.Marshal(body)
		raw = string(b)
	}
	req := httptest.NewRequest(http.MethodPut, path, strings.NewReader(raw)).WithContext(ctx)
	if token != "" {
		req.Header.Set("Authorization", "Bearer "+token)
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
	base := gitk8s.CheckResult{Commit: "h1", ParentCommit: "p1", State: gitk8s.Passed}
	b.Status.Checks = map[string]gitk8s.CheckResult{"base": base}
	gofmtUser := checkToken("gofmt").User
	main := &resultsBranch{Object: kube.Meta("app-main", nil)}
	main.Namespace, main.Spec = "default", gitk8s.GitBranchSpec{Repository: "app", Branch: "main", Head: "p1"}
	ctx, rec := kube.Fake(t.Context(), b,
		main, checkToken("base"), checkToken("gofmt"), checkToken("risk"),
		kube.FakeToken{Token: "api", User: gofmtUser},
		kube.FakeToken{Token: "ci", User: kube.UserInfo{Username: "system:serviceaccount:default:ci"}, Audiences: []string{gitk8s.ResultsAudience}},
		kube.FakeToken{Token: "elsewhere", User: kube.UserInfo{Username: "system:serviceaccount:default:check-gofmt"}, Audiences: []string{gitk8s.ResultsAudience}},
		kube.FakeToken{Token: "admin", User: kube.UserInfo{Username: "kubernetes-admin"}, Audiences: []string{gitk8s.ResultsAudience}},
	)
	rs := &results{timeout: time.Minute, poll: time.Millisecond}
	fresh := &gitk8s.CheckResult{Commit: "h1", State: gitk8s.Passed}
	const gofmt = "/results/default/app-c-x/gofmt?generation=3"
	for _, tc := range []struct {
		name, path, token string
		body              any
		code              int
		msg               string
	}{
		{"no token", gofmt, "", fresh, http.StatusUnauthorized, "no token"},
		{"a token for the API server", gofmt, "api", fresh, http.StatusUnauthorized, "is invalid for the target audiences"},
		{"a service account that isn't a check", gofmt, "ci", fresh, http.StatusForbidden, "system:serviceaccount:default:ci isn't a check's service account"},
		{"a check's account name in another namespace", gofmt, "elsewhere", fresh, http.StatusForbidden, "isn't a check's service account"},
		{"a person", gofmt, "admin", fresh, http.StatusForbidden, "kubernetes-admin isn't a check's service account"},
		{"another check's entry", gofmt, "base", fresh, http.StatusForbidden, "system:serviceaccount:check-base:check-base is the base check, so it can't write the gofmt check's result"},
		{"invalid JSON", gofmt, "gofmt", `{"commit":`, http.StatusBadRequest, "decoding the result"},
		{"an unknown field", gofmt, "gofmt", `{"commit":"h1","state":"Passed","approved":true}`, http.StatusBadRequest, `unknown field "approved"`},
		{"a body that's too large", gofmt, "gofmt", `{"commit":"h1","state":"Passed","message":"` + strings.Repeat("x", maxResultSize) + `"}`, http.StatusBadRequest, "too large"},
		{"a state that checks can't send", gofmt, "gofmt", &gitk8s.CheckResult{Commit: "h1", State: gitk8s.Pending}, http.StatusBadRequest, `state "Pending" isn't`},
		{"an invalid generation", "/results/default/app-c-x/gofmt?generation=new", "gofmt", fresh, http.StatusBadRequest, "generation"},
		{"a branch that doesn't exist", "/results/default/app-c-y/gofmt?generation=1", "gofmt", fresh, http.StatusNotFound, "GitBranch default/app-c-y doesn't exist"},
		{"a check that the policy doesn't list", "/results/default/app-c-x/risk?generation=3", "risk", fresh, http.StatusConflict, "the merge policy for c/x doesn't list the risk check"},
		{"a branch without a parent", "/results/default/app-main/gofmt", "gofmt", fresh, http.StatusConflict, "main has no parent, so it takes no check results"},
		{"another head", gofmt, "gofmt", &gitk8s.CheckResult{Commit: "h0", State: gitk8s.Passed}, http.StatusConflict, "the result isn't for c/x at h1 and main at p1"},
		{"another parent head", "/results/default/app-c-x/base?generation=3", "base", &gitk8s.CheckResult{Commit: "h1", ParentCommit: "p0", State: gitk8s.Passed}, http.StatusConflict, "the result isn't for c/x"},
		{"a result that's already written", "/results/default/app-c-x/base?generation=3", "base", &base, http.StatusNoContent, ""},
	} {
		t.Run(tc.name, func(t *testing.T) {
			w := sendResult(ctx, rs, tc.path, tc.token, tc.body)
			if w.Code != tc.code || !strings.Contains(w.Body.String(), tc.msg) {
				t.Errorf("got %d %q, want %d %q", w.Code, w.Body, tc.code, tc.msg)
			}
			if tc.code == http.StatusUnauthorized && w.Header().Get("WWW-Authenticate") != "Bearer" {
				t.Errorf("WWW-Authenticate = %q, want Bearer", w.Header().Get("WWW-Authenticate"))
			}
		})
	}
	if got := kube.Triggered[resultsBranch](rec); len(got) != 0 {
		t.Errorf("triggered %v without a new result to write", got)
	}
	if len(rs.held) != 0 {
		t.Errorf("holds %v after the requests ended", rs.held)
	}
}

func TestResultsEndpointTimesOut(t *testing.T) {
	ctx, rec := kube.Fake(t.Context(), listedBranch(), checkToken("gofmt"))
	rs := &results{timeout: 20 * time.Millisecond, poll: time.Millisecond}
	w := sendResult(ctx, rs, "/results/default/app-c-x/gofmt?generation=3", "gofmt", &gitk8s.CheckResult{Commit: "h1", State: gitk8s.Passed})
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
}

// A check that read a newer spec than this replica's cache has waits for
// the cache, so that its result isn't checked against an older spec.
func TestResultsEndpointWaitsForGeneration(t *testing.T) {
	ctx, rec := kube.Fake(t.Context(), listedBranch(), checkToken("gofmt"))
	rs := &results{timeout: 20 * time.Millisecond, poll: time.Millisecond}
	w := sendResult(ctx, rs, "/results/default/app-c-x/gofmt?generation=4", "gofmt", &gitk8s.CheckResult{Commit: "h2", State: gitk8s.Passed})
	if w.Code != http.StatusServiceUnavailable {
		t.Errorf("got %d %q, want 503 while the cache has generation 3", w.Code, w.Body)
	}
	if got := kube.Triggered[resultsBranch](rec); len(got) != 0 {
		t.Errorf("triggered %v before the cache had the spec that the check read", got)
	}
}

// A request holds its result and triggers a reconcile of the branch, which
// writes the result. A request whose result the cache shows answers 204.
func TestResultsHandOff(t *testing.T) {
	res := &gitk8s.CheckResult{Commit: "h1", State: gitk8s.Failed, Message: "x.go isn't formatted"}
	const path = "/results/default/app-c-x/gofmt?generation=3"
	rs := &results{timeout: time.Minute, poll: time.Millisecond}
	ctx, rec := kube.Fake(t.Context(), listedBranch(), checkToken("gofmt"))
	ctx, cancel := context.WithCancel(ctx)
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

	b := listedBranch()
	base := gitk8s.CheckResult{Commit: "h1", ParentCommit: "p1", State: gitk8s.Passed}
	b.Status.Checks = map[string]gitk8s.CheckResult{"base": base}
	rctx, _ := kube.Fake(t.Context(), b)
	if err := rs.Reconcile(rctx, b); err != nil {
		t.Fatal(err)
	}
	if !entry(b, "gofmt").Equal(res) || !entry(b, "base").Equal(&base) {
		t.Errorf("status.checks = %+v, want the held gofmt result and the base result", b.Status.Checks)
	}

	cancel()
	<-done
	if got, want := kube.Triggered[resultsBranch](rec), []kube.Key{branchKey}; !slices.Equal(got, want) {
		t.Errorf("Triggered = %v, want %v", got, want)
	}
	if len(rs.held) != 0 {
		t.Errorf("holds %v after the request ended", rs.held)
	}

	ctx, rec = kube.Fake(t.Context(), b, checkToken("gofmt"))
	if w := sendResult(ctx, rs, path, "gofmt", res); w.Code != http.StatusNoContent {
		t.Errorf("with the result written, got %d %q, want 204", w.Code, w.Body)
	}
	if got := kube.Triggered[resultsBranch](rec); len(got) != 0 {
		t.Errorf("triggered %v for a result that's already written", got)
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
	fresh := gitk8s.CheckResult{Commit: "h1", State: gitk8s.Passed}
	stale := gitk8s.CheckResult{Commit: "h0", State: gitk8s.Failed}
	base := gitk8s.CheckResult{Commit: "h1", ParentCommit: "p1", State: gitk8s.Passed}
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
	fresh := gitk8s.CheckResult{Commit: "h1", State: gitk8s.Passed}
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
	for user, want := range map[string]string{
		"system:serviceaccount:check-gofmt:check-gofmt":     "gofmt",
		"system:serviceaccount:check-my-lint:check-my-lint": "my-lint",
		"system:serviceaccount:default:check-gofmt":         "",
		"system:serviceaccount:check-gofmt:default":         "",
		"system:serviceaccount:check-:check-":               "",
		"system:serviceaccount:git-k8s:git-k8s":             "",
		"check-gofmt":                                       "",
		"kubernetes-admin":                                  "",
	} {
		got, ok := checkFor(kube.UserInfo{Username: user})
		if got != want || ok != (want != "") {
			t.Errorf("checkFor(%s) = %q, %v; want %q", user, got, ok, want)
		}
	}
}

func TestValidate(t *testing.T) {
	outputs := func(n, nameLen, valueLen int) map[string]string {
		m := map[string]string{}
		for i := range n {
			name := strings.Repeat("n", nameLen-1) + string(rune('a'+i))
			m[name] = strings.Repeat("v", valueLen)
		}
		return m
	}
	for _, tc := range []struct {
		name string
		edit func(*gitk8s.CheckResult)
		err  string
	}{
		{"passed", func(*gitk8s.CheckResult) {}, ""},
		{"running", func(r *gitk8s.CheckResult) { r.State = gitk8s.Running }, ""},
		{"failed", func(r *gitk8s.CheckResult) { r.State = gitk8s.Failed }, ""},
		{"fixed", func(r *gitk8s.CheckResult) { r.State = gitk8s.Fixed }, ""},
		{"error", func(r *gitk8s.CheckResult) { r.State = gitk8s.Error }, ""},
		{"pending", func(r *gitk8s.CheckResult) { r.State = gitk8s.Pending }, `state "Pending" isn't`},
		{"no state", func(r *gitk8s.CheckResult) { r.State = "" }, `state "" isn't`},
		{"no commit", func(r *gitk8s.CheckResult) { r.Commit = "" }, "no commit"},
		{"the longest message", func(r *gitk8s.CheckResult) { r.Message = strings.Repeat("x", gitk8s.MaxMessageLength) }, ""},
		{"a longer message", func(r *gitk8s.CheckResult) { r.Message = strings.Repeat("x", gitk8s.MaxMessageLength+1) }, "message is longer than 1024 bytes"},
		{"the most outputs", func(r *gitk8s.CheckResult) { r.Outputs = outputs(gitk8s.MaxOutputs, 2, 1) }, ""},
		{"more outputs", func(r *gitk8s.CheckResult) { r.Outputs = outputs(gitk8s.MaxOutputs+1, 2, 1) }, "more than 16 outputs"},
		{"the longest output name", func(r *gitk8s.CheckResult) { r.Outputs = outputs(1, gitk8s.MaxOutputNameLength, 1) }, ""},
		{"a longer output name", func(r *gitk8s.CheckResult) { r.Outputs = outputs(1, gitk8s.MaxOutputNameLength+1, 1) }, "output name isn't 1 to 63 bytes"},
		{"an empty output name", func(r *gitk8s.CheckResult) { r.Outputs = map[string]string{"": "v"} }, "output name isn't 1 to 63 bytes"},
		{"the longest output value", func(r *gitk8s.CheckResult) { r.Outputs = outputs(1, 1, gitk8s.MaxOutputValueLength) }, ""},
		{"a longer output value", func(r *gitk8s.CheckResult) {
			r.Outputs = map[string]string{"files": strings.Repeat("v", gitk8s.MaxOutputValueLength+1)}
		}, "output files is longer than 1024 bytes"},
	} {
		t.Run(tc.name, func(t *testing.T) {
			r := &gitk8s.CheckResult{Commit: "h1", State: gitk8s.Passed}
			tc.edit(r)
			err := validate(r)
			if tc.err == "" && err != nil || tc.err != "" && (err == nil || !strings.Contains(err.Error(), tc.err)) {
				t.Errorf("validate = %v, want %q", err, tc.err)
			}
		})
	}
}

package main

import (
	"io"
	"net/http"
	"net/http/httptest"
	"slices"
	"strings"
	"testing"
	"time"

	"github.com/imjasonh/playground/kube"
)

func newProbe(namespace, name, url string) *Probe {
	p := &Probe{Object: kube.Meta(name, nil)}
	p.Namespace = namespace
	p.Spec.URL = url
	return p
}

func TestReconcileSendsAToken(t *testing.T) {
	var auth string
	srv := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		auth = r.Header.Get("Authorization")
		_, _ = io.WriteString(w, "ok\nmore")
	}))
	defer srv.Close()
	interval := time.Minute
	r := &reconciler{client: srv.Client(), interval: &interval}
	p := newProbe("team", "api", srv.URL)
	ctx, rec := kube.Fake(t.Context(), p)
	if err := r.Reconcile(ctx, p); err != nil {
		t.Fatal(err)
	}
	if auth != "Bearer fake-token-1" {
		t.Errorf("Authorization = %q", auth)
	}
	if review, _ := kube.ReviewToken(ctx, "fake-token-1", "probe"); !review.Authenticated {
		t.Errorf("the token isn't for the audience probe: %+v", review)
	}
	if p.Status.Code != http.StatusOK || p.Status.Message != "ok" || p.Status.CheckedAt.IsZero() {
		t.Errorf("status = %+v", p.Status)
	}
	if rec.RequeueAfter() != time.Minute {
		t.Errorf("RequeueAfter = %v", rec.RequeueAfter())
	}

	srv.Close()
	if err := r.Reconcile(ctx, p); err != nil {
		t.Fatal(err)
	}
	if p.Status.Code != 0 || !strings.Contains(p.Status.Message, "connection refused") {
		t.Errorf("status of a probe that gets no response = %+v", p.Status)
	}
}

func TestAPI(t *testing.T) {
	ci := kube.UserInfo{Username: "system:serviceaccount:team:ci"}
	inPod := kube.UserInfo{Username: ci.Username, Extra: map[string][]string{"authentication.kubernetes.io/pod-name": {"ci-1"}}}
	p := newProbe("team", "api", "http://api.team.svc/healthz")
	ctx, rec := kube.Fake(t.Context(), p,
		kube.FakeToken{Token: "ci", User: ci, Audiences: []string{"probe"}},
		kube.FakeToken{Token: "ci-elsewhere", User: ci, Audiences: []string{"other"}},
		kube.FakeToken{Token: "pod", User: inPod, Audiences: []string{"probe"}},
		kube.FakeToken{Token: "admin", User: kube.UserInfo{Username: "kubernetes-admin"}, Audiences: []string{"probe"}},
	)
	audience := "probe"
	h := (&api{audience: &audience}).handler()
	for _, tc := range []struct {
		method, path, token string
		code                int
		body                string
	}{
		{http.MethodGet, "/whoami", "", http.StatusUnauthorized, "no token"},
		{http.MethodGet, "/whoami", "ci-elsewhere", http.StatusUnauthorized, "is invalid for the target audiences"},
		{http.MethodGet, "/whoami", "ci", http.StatusOK, "system:serviceaccount:team:ci\n"},
		{http.MethodGet, "/whoami", "pod", http.StatusOK, "system:serviceaccount:team:ci in Pod ci-1\n"},
		{http.MethodPost, "/probes/team/api", "ci", http.StatusAccepted, ""},
		{http.MethodPost, "/probes/team/missing", "ci", http.StatusNotFound, ""},
		{http.MethodPost, "/probes/other/api", "ci", http.StatusForbidden, "can't run probes in other"},
		{http.MethodPost, "/probes/team/api", "admin", http.StatusForbidden, "kubernetes-admin can't run probes"},
	} {
		req := httptest.NewRequest(tc.method, tc.path, nil).WithContext(ctx)
		if tc.token != "" {
			req.Header.Set("Authorization", "Bearer "+tc.token)
		}
		w := httptest.NewRecorder()
		h.ServeHTTP(w, req)
		if w.Code != tc.code || !strings.Contains(w.Body.String(), tc.body) {
			t.Errorf("%s %s with %q = %d %q, want %d %q", tc.method, tc.path, tc.token, w.Code, w.Body, tc.code, tc.body)
		}
	}
	if got, want := kube.Triggered[Probe](rec), []kube.Key{{Namespace: "team", Name: "api"}}; !slices.Equal(got, want) {
		t.Errorf("Triggered = %v, want %v", got, want)
	}

	empty := ""
	req := httptest.NewRequest(http.MethodGet, "/whoami", nil).WithContext(ctx)
	req.Header.Set("Authorization", "Bearer ci")
	w := httptest.NewRecorder()
	(&api{audience: &empty}).handler().ServeHTTP(w, req)
	if w.Code != http.StatusInternalServerError || strings.Contains(w.Body.String(), "kube.ReviewToken") {
		t.Errorf("GET /whoami when the review fails = %d %q, want 500 without the error", w.Code, w.Body)
	}
}

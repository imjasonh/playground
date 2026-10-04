package kube

import (
	"context"
	"io"
	"net"
	"net/http"
	"net/http/httptest"
	"strings"
	"testing"
	"time"
)

func TestServePrepare(t *testing.T) {
	m := testManager()
	if err := Serve(nil).prepare(t.Context(), m); err == nil || !strings.Contains(err.Error(), "the handler is nil") {
		t.Errorf("Serve(nil): err = %v", err)
	}
	a, b := Serve(http.NotFoundHandler()), Serve(http.NotFoundHandler())
	m.controllers = []Controller{a, b}
	if err := a.prepare(t.Context(), m); err == nil || !strings.Contains(err.Error(), "more than one handler") {
		t.Errorf("two Serves: err = %v", err)
	}
	m.controllers = []Controller{a}
	if err := a.prepare(t.Context(), m); err != nil {
		t.Error(err)
	}
	if d, err := a.describe(); err != nil || !d.serves || d.reconciles || d.webhooks || d.ti != nil {
		t.Errorf("describe = %+v, %v", d, err)
	}
}

func TestServeHandlerCanOnlyRead(t *testing.T) {
	_, m := newAuthAPI(t, UserInfo{})
	var review TokenReview
	var reviewErr, cause error
	s := Serve(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		token, _ := strings.CutPrefix(r.Header.Get("Authorization"), "Bearer ")
		review, reviewErr = ReviewToken(r.Context(), token, "git-k8s")
		Own(r.Context(), &widget{Object: Meta("w", nil)})
		cause = context.Cause(r.Context())
		w.WriteHeader(http.StatusAccepted)
	})).(*server)
	m.controllers = []Controller{s}
	if err := s.prepare(t.Context(), m); err != nil {
		t.Fatal(err)
	}
	req := httptest.NewRequest(http.MethodPost, "/", nil)
	req.Header.Set("Authorization", "Bearer valid")
	rec := httptest.NewRecorder()
	s.serveHTTP(rec, req)
	if rec.Code != http.StatusAccepted {
		t.Errorf("status = %d", rec.Code)
	}
	if reviewErr != nil || !review.Authenticated {
		t.Errorf("ReviewToken = %+v, %v", review, reviewErr)
	}
	if cause == nil || !strings.Contains(cause.Error(), "kube.Own can't be called in a webhook or a kube.Serve handler") {
		t.Errorf("after Own, the request's context has cause %v", cause)
	}
}

func TestServeRun(t *testing.T) {
	m := testManager()
	m.Addr = "127.0.0.1:0"
	m.ServeAddr = freeAddr(t)
	waiting := make(chan struct{})
	s := Serve(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		if r.URL.Path == "/wait" {
			close(waiting)
			<-r.Context().Done()
			return
		}
		_, _ = io.WriteString(w, "served")
	})).(*server)
	m.controllers = []Controller{s}
	if err := s.prepare(t.Context(), m); err != nil {
		t.Fatal(err)
	}
	health, err := m.serve()
	if err != nil {
		t.Fatal(err)
	}
	defer health.Close()
	readyz := func() int {
		rec := httptest.NewRecorder()
		health.Handler.ServeHTTP(rec, httptest.NewRequest(http.MethodGet, "/readyz", nil))
		return rec.Code
	}
	if code := readyz(); code != http.StatusServiceUnavailable {
		t.Errorf("/readyz before Serve serves = %d, want 503", code)
	}

	ctx, cancel := context.WithCancel(t.Context())
	defer cancel()
	done := make(chan error, 1)
	go func() { done <- s.run(ctx) }()
	for deadline := time.Now().Add(10 * time.Second); !s.synced(); time.Sleep(10 * time.Millisecond) {
		if time.Now().After(deadline) {
			t.Fatal("Serve didn't start serving")
		}
	}
	if code := readyz(); code != http.StatusOK {
		t.Errorf("/readyz while Serve serves = %d, want 200", code)
	}
	resp, err := http.Get("http://" + m.ServeAddr + "/")
	if err != nil {
		t.Fatal(err)
	}
	body, _ := io.ReadAll(resp.Body)
	resp.Body.Close()
	if string(body) != "served" {
		t.Errorf("body = %q", body)
	}

	other := Serve(http.NotFoundHandler()).(*server)
	other.m = m
	if err := other.run(t.Context()); err == nil {
		t.Error("serving on an address that's in use succeeded")
	}

	answered := make(chan struct{})
	go func() {
		defer close(answered)
		if resp, err := http.Get("http://" + m.ServeAddr + "/wait"); err == nil {
			resp.Body.Close()
		}
	}()
	<-waiting
	stopped := time.Now()
	cancel()
	select {
	case err := <-done:
		if err != nil {
			t.Errorf("run = %v, want nil once its context is done", err)
		}
	case <-time.After(30 * time.Second):
		t.Fatal("run didn't return")
	}
	if d := time.Since(stopped); d > 5*time.Second {
		t.Errorf("run took %v to return, want the request in progress canceled", d)
	}
	<-answered
	if code := readyz(); code != http.StatusServiceUnavailable {
		t.Errorf("/readyz after Serve stopped = %d, want 503", code)
	}
}

func freeAddr(t *testing.T) string {
	t.Helper()
	ln, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	defer ln.Close()
	return ln.Addr().String()
}

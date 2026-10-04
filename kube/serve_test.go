package kube

import (
	"context"
	"errors"
	"io"
	"net"
	"net/http"
	"net/http/httptest"
	"strings"
	"syscall"
	"testing"
	"time"
)

func TestServePrepare(t *testing.T) {
	m := testManager()
	m.ServeAddr = "127.0.0.1:0"
	if err := Serve(nil).prepare(t.Context(), m); err == nil || !strings.Contains(err.Error(), "the handler is nil") {
		t.Errorf("Serve(nil): err = %v", err)
	}
	a, b := Serve(http.NotFoundHandler()), Serve(http.NotFoundHandler())
	for name, cs := range map[string][]Controller{"two Serves": {a, b}, "one Serve twice": {a, a}} {
		m.controllers = cs
		if err := a.prepare(t.Context(), m); err == nil || !strings.Contains(err.Error(), "more than one handler") {
			t.Errorf("%s: err = %v", name, err)
		}
	}
	m.controllers = []Controller{a}
	ctx, cancel := context.WithCancel(t.Context())
	if err := a.prepare(ctx, m); err != nil {
		t.Fatal(err)
	}
	if d, err := a.describe(); err != nil || !d.serves || d.reconciles || d.webhooks || d.ti != nil {
		t.Errorf("describe = %+v, %v", d, err)
	}

	addr := a.(*server).ln.Addr().String()
	other := testManager()
	other.ServeAddr = addr
	if err := Serve(http.NotFoundHandler()).prepare(t.Context(), other); !errors.Is(err, syscall.EADDRINUSE) || !strings.Contains(err.Error(), "kube.Serve") {
		t.Errorf("preparing to serve on an address that's in use: err = %v", err)
	}
	cancel()
	waitFor(t, "the listener to close once the manager stops", func() bool {
		ln, err := net.Listen("tcp", addr)
		if err == nil {
			ln.Close()
		}
		return err == nil
	})
	if err := a.run(ctx); err != nil {
		t.Errorf("run after the manager stopped = %v, want nil", err)
	}
}

// stub is a controller that does nothing until its context is done, or
// fails to run with err.
type stub struct {
	reconciler bool
	err        error
}

func (s *stub) prepare(context.Context, *Manager) error { return nil }
func (s *stub) setup(ctx context.Context, _ *Manager) error {
	<-ctx.Done()
	return ctx.Err()
}
func (s *stub) run(ctx context.Context) error {
	if s.err != nil {
		return s.err
	}
	<-ctx.Done()
	return nil
}
func (s *stub) reconciles() bool            { return s.reconciler }
func (s *stub) controllerName() string      { return "stub" }
func (s *stub) synced() bool                { return true }
func (s *stub) describe() (declared, error) { return declared{reconciles: s.reconciler}, nil }

func TestRunReportsFailedServers(t *testing.T) {
	ln, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	defer ln.Close()
	_, m := newAuthAPI(t, UserInfo{})
	m.ServeAddr = ln.Addr().String()
	if err := m.Run(t.Context(), &stub{reconciler: true}, Serve(http.NotFoundHandler())); !errors.Is(err, syscall.EADDRINUSE) {
		t.Errorf("Run with a Serve address that's in use = %v, want the listen error", err)
	}

	boom := errors.New("boom")
	_, m = newAuthAPI(t, UserInfo{})
	if err := m.Run(t.Context(), &stub{err: boom}, &stub{reconciler: true}); !errors.Is(err, boom) || !strings.Contains(err.Error(), "stub") {
		t.Errorf("Run with a server that fails while the controllers set up = %v, want the server's error", err)
	}
}

func TestServeHandlerCanOnlyRead(t *testing.T) {
	_, m := newAuthAPI(t, UserInfo{})
	m.ServeAddr = "127.0.0.1:0"
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
	m.ServeAddr = "127.0.0.1:0"
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
	addr := s.ln.Addr().String()
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
	resp, err := http.Get("http://" + addr + "/")
	if err != nil {
		t.Fatal(err)
	}
	body, _ := io.ReadAll(resp.Body)
	resp.Body.Close()
	if string(body) != "served" {
		t.Errorf("body = %q", body)
	}

	answered := make(chan struct{})
	go func() {
		defer close(answered)
		if resp, err := http.Get("http://" + addr + "/wait"); err == nil {
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

package kube

import (
	"context"
	"errors"
	"fmt"
	"net"
	"net/http"
	"sync/atomic"
	"time"
)

// Serve returns a Controller that serves HTTP requests with h, for endpoints
// that other programs call. Every replica serves, whether or not it holds a
// lease, from when it starts until it stops. The manager serves plain HTTP
// at Manager.ServeAddr, ":8081" by default, and /readyz reports ready once
// it does. Run returns an error if it can't listen there. The generate
// command routes port 80 of the program's Service to it.
//
// The server doesn't authenticate requests. Check each caller's bearer
// token with ReviewToken.
//
// A request's context lets h call Get, List, Fetch, ReviewToken,
// RequestToken, and Trigger. As in a webhook, h can only read. Calling Own,
// Apply, Delete, or RequeueAfter cancels the request's context, with the
// error as its cause. So does a Get or List that can't read, for example
// because the program may not list a type. To change the cluster in response
// to a request, call Trigger, and make the change in the reconcile. When the
// program stops, the contexts of requests in progress are canceled too.
//
// A program can have one Serve. To serve several paths, use one handler,
// such as an http.ServeMux.
func Serve(h http.Handler) Controller { return &server{h: h} }

type server struct {
	h  http.Handler
	m  *Manager
	ln net.Listener
	// keep stops prepare's closing of ln when the manager stops, and
	// reports whether ln is still open.
	keep  func() bool
	ready atomic.Bool
}

func (s *server) prepare(ctx context.Context, m *Manager) error {
	if s.h == nil {
		return errors.New("kube.Serve: the handler is nil")
	}
	n := 0
	for _, c := range m.controllers {
		if _, ok := c.(*server); ok {
			n++
		}
	}
	if n > 1 {
		return errors.New("kube.Serve: the program serves more than one handler; serve every path from one handler, such as an http.ServeMux")
	}
	addr := m.ServeAddr
	if addr == "" {
		addr = ":8081"
	}
	ln, err := net.Listen("tcp", addr)
	if err != nil {
		return fmt.Errorf("kube.Serve: %w", err)
	}
	s.m, s.ln = m, ln
	// Run doesn't call run if a later step of starting fails.
	s.keep = context.AfterFunc(ctx, func() { ln.Close() })
	return nil
}

func (s *server) describe() (declared, error)           { return declared{serves: true}, nil }
func (s *server) setup(context.Context, *Manager) error { return nil }
func (s *server) reconciles() bool                      { return false }
func (s *server) controllerName() string                { return "serve" }
func (s *server) synced() bool                          { return s.ready.Load() }

func (s *server) run(ctx context.Context) error {
	if !s.keep() {
		return nil
	}
	ln := s.ln
	srv := &http.Server{
		Handler:           http.HandlerFunc(s.serveHTTP),
		ReadHeaderTimeout: 10 * time.Second,
		BaseContext:       func(net.Listener) context.Context { return ctx },
	}
	served := make(chan error, 1)
	go func() { served <- srv.Serve(ln) }()
	s.ready.Store(true)
	s.m.log.Info("serving HTTP", "addr", ln.Addr().String())
	select {
	case err := <-served:
		s.ready.Store(false)
		return err
	case <-ctx.Done():
	}
	s.ready.Store(false)
	sctx, cancel := context.WithTimeout(context.WithoutCancel(ctx), 10*time.Second)
	defer cancel()
	if err := srv.Shutdown(sctx); err != nil {
		srv.Close()
	}
	return nil
}

func (s *server) serveHTTP(w http.ResponseWriter, r *http.Request) {
	ctx, sc := newWebhookScope(r.Context(), s.m)
	defer sc.cancel(nil)
	s.h.ServeHTTP(w, r.WithContext(ctx))
	if sc.err != nil {
		s.m.log.Warn("a call in a kube.Serve handler failed", "method", r.Method, "path", r.URL.Path, "err", sc.err)
	}
}

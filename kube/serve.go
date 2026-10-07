package kube

import (
	"bufio"
	"context"
	"errors"
	"fmt"
	"io"
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
// error as its cause. A Get or List that can't read, for example because the
// program may not list a type, stops h, and the server answers 503 Service
// Unavailable and closes the connection. If h has already started its
// response, the server aborts the response instead. To change the cluster in
// response to a request, call Trigger, and make the change in the reconcile.
//
// When the program stops, the server stops accepting connections, and
// requests in progress have 10 seconds to finish before their contexts are
// canceled. Trigger returns false during that time. The generate command
// has the kubelet wait 5 seconds before it stops the program, so that the
// program's Service stops sending it connections first. A program with a
// Volume doesn't wait, because it runs one Pod, and no other Pod takes the
// connections while it stops.
//
// A program can have one Serve. To serve several paths, use one handler,
// such as an http.ServeMux.
func Serve(h http.Handler) Controller { return &server{h: h} }

// serveGrace is how long requests in progress have to finish once the
// program stops. The Pod's termination grace period, 30 seconds by default,
// must cover it and any preStop sleep that generate adds.
var serveGrace = 10 * time.Second

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
	reqs, cancelReqs := context.WithCancel(context.WithoutCancel(ctx))
	defer cancelReqs()
	srv := &http.Server{
		Handler:           http.HandlerFunc(s.serveHTTP),
		ReadHeaderTimeout: 10 * time.Second,
		BaseContext:       func(net.Listener) context.Context { return reqs },
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
	sctx, cancel := context.WithTimeout(context.Background(), serveGrace)
	defer cancel()
	if err := srv.Shutdown(sctx); err != nil {
		cancelReqs()
		srv.Close()
	}
	return nil
}

func (s *server) serveHTTP(w http.ResponseWriter, r *http.Request) {
	ctx, sc := newWebhookScope(r.Context(), s.m)
	defer sc.cancel(nil)
	rw := &responseWriter{ResponseWriter: w}
	defer func() {
		p := recover()
		err := readError(p)
		if p != nil && err == nil {
			panic(p)
		}
		if err == nil {
			err = sc.err
		}
		if err == nil {
			return
		}
		s.m.log.Warn("a call in a kube.Serve handler failed", "method", r.Method, "path", r.URL.Path, "err", err)
		switch {
		case p == nil:
		case rw.started:
			// The client has received part of a response, so it can't get
			// a 503 anymore.
			panic(http.ErrAbortHandler)
		default:
			clear(w.Header())
			w.Header().Set("Connection", "close")
			http.Error(w, "the server couldn't read from the cluster; try again", http.StatusServiceUnavailable)
		}
	}()
	s.h.ServeHTTP(rw, r.WithContext(ctx))
}

// responseWriter records whether a handler has started its response. Its
// Flush, Hijack, ReadFrom, and Unwrap methods give the handler what the
// server's ResponseWriter supports, through type assertions or
// http.ResponseController.
type responseWriter struct {
	http.ResponseWriter
	started bool
}

func (w *responseWriter) WriteHeader(code int) {
	// An informational response, other than 101 Switching Protocols, comes
	// before the response.
	if code >= 200 || code == http.StatusSwitchingProtocols {
		w.started = true
	}
	w.ResponseWriter.WriteHeader(code)
}

func (w *responseWriter) Write(b []byte) (int, error) {
	w.started = true
	return w.ResponseWriter.Write(b)
}

func (w *responseWriter) ReadFrom(r io.Reader) (int64, error) {
	w.started = true
	return io.Copy(w.ResponseWriter, r)
}

func (w *responseWriter) Flush() { _ = w.FlushError() }

func (w *responseWriter) FlushError() error {
	w.started = true
	return http.NewResponseController(w.ResponseWriter).Flush()
}

func (w *responseWriter) Hijack() (net.Conn, *bufio.ReadWriter, error) {
	w.started = true
	return http.NewResponseController(w.ResponseWriter).Hijack()
}

func (w *responseWriter) Unwrap() http.ResponseWriter { return w.ResponseWriter }

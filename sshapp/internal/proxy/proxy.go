// Package proxy holds accepted TCP connections until a backend is ready, then
// splices bytes both ways. That is the SSH equivalent of Knative's activator:
// the client completes TCP connect immediately; the SSH banner arrives only
// after the backend dial succeeds.
package proxy

import (
	"context"
	"errors"
	"io"
	"net"
	"sync"
	"sync/atomic"
	"time"
)

// Backend resolves a dialable address for an active app instance.
type Backend interface {
	// EnsureReady scales the app up if needed and returns host:port of a ready
	// backend. It must block until the address is dialable or ctx ends.
	EnsureReady(ctx context.Context) (addr string, err error)
	// SetActiveConnections reports how many proxied sessions are open so the
	// backend can scale to zero after idle.
	SetActiveConnections(n int)
}

// Server accepts connections on ln and proxies them through Backend.
type Server struct {
	Backend     Backend
	DialTimeout time.Duration
	WarmTimeout time.Duration

	active atomic.Int64
}

// Serve accepts connections until ln closes or ctx is cancelled.
func (s *Server) Serve(ctx context.Context, ln net.Listener) error {
	if s.DialTimeout <= 0 {
		s.DialTimeout = 5 * time.Second
	}
	if s.WarmTimeout <= 0 {
		s.WarmTimeout = 2 * time.Minute
	}

	go func() {
		<-ctx.Done()
		_ = ln.Close()
	}()

	var wg sync.WaitGroup
	defer wg.Wait()

	for {
		conn, err := ln.Accept()
		if err != nil {
			if ctx.Err() != nil || errors.Is(err, net.ErrClosed) {
				return nil
			}
			return err
		}
		wg.Add(1)
		go func(c net.Conn) {
			defer wg.Done()
			s.handle(ctx, c)
		}(conn)
	}
}

func (s *Server) handle(parent context.Context, client net.Conn) {
	defer client.Close()

	n := s.active.Add(1)
	s.Backend.SetActiveConnections(int(n))
	defer func() {
		n := s.active.Add(-1)
		s.Backend.SetActiveConnections(int(n))
	}()

	warmCtx, cancel := context.WithTimeout(parent, s.WarmTimeout)
	defer cancel()

	addr, err := s.Backend.EnsureReady(warmCtx)
	if err != nil {
		return
	}

	d := net.Dialer{Timeout: s.DialTimeout}
	backend, err := d.DialContext(warmCtx, "tcp", addr)
	if err != nil {
		return
	}
	defer backend.Close()

	// Do not speak SSH here. The Wish backend sends the banner; the client
	// waits. Cold start looks like a slow time-to-banner, not a refused connect.
	errc := make(chan error, 2)
	go func() { errc <- splice(client, backend) }()
	go func() { errc <- splice(backend, client) }()
	<-errc
}

func splice(dst io.Writer, src io.Reader) error {
	_, err := io.Copy(dst, src)
	return err
}

// ActiveConnections returns the number of sessions currently proxied.
func (s *Server) ActiveConnections() int {
	return int(s.active.Load())
}

package gateway_test

import (
	"bytes"
	"context"
	"strings"
	"sync"
	"testing"
	"time"

	"github.com/imjasonh/playground/sshcloud/internal/gateway"
)

func TestDialWithLoadingShowsStarting(t *testing.T) {
	var mu sync.Mutex
	var buf bytes.Buffer
	started := make(chan struct{})
	release := make(chan struct{})

	dial := func(_ context.Context, req gateway.DialRequest) (string, error) {
		if req.User != "alice" || req.App != "fortune" || req.Gen != "g1" {
			t.Fatalf("dial args: %+v", req)
		}
		close(started)
		<-release
		return "10.0.0.2:22", nil
	}

	done := make(chan struct{})
	var addr string
	var err error
	go func() {
		defer close(done)
		addr, err = gateway.DialWithLoading(context.Background(), &lockedWriter{mu: &mu, buf: &buf}, "fortune", dial, gateway.DialRequest{
			User: "alice", App: "fortune", Gen: "g1",
		})
	}()

	select {
	case <-started:
	case <-time.After(2 * time.Second):
		t.Fatal("dial never started")
	}

	// Allow at least one loading tick / initial write.
	deadline := time.Now().Add(2 * time.Second)
	for {
		mu.Lock()
		s := buf.String()
		mu.Unlock()
		if strings.Contains(s, "Starting fortune") {
			break
		}
		if time.Now().After(deadline) {
			t.Fatalf("missing loading text; got %q", s)
		}
		time.Sleep(20 * time.Millisecond)
	}

	close(release)
	select {
	case <-done:
	case <-time.After(2 * time.Second):
		t.Fatal("DialWithLoading did not return")
	}
	if err != nil {
		t.Fatal(err)
	}
	if addr != "10.0.0.2:22" {
		t.Fatalf("addr = %q", addr)
	}
	mu.Lock()
	out := buf.String()
	mu.Unlock()
	if !strings.Contains(out, "Starting fortune") {
		t.Fatalf("output: %q", out)
	}
}

func TestDialWithLoadingError(t *testing.T) {
	dial := func(context.Context, gateway.DialRequest) (string, error) {
		return "", errBackend
	}
	var buf bytes.Buffer
	_, err := gateway.DialWithLoading(context.Background(), &buf, "fortune", dial, gateway.DialRequest{User: "alice", App: "fortune"})
	if err != errBackend {
		t.Fatalf("err = %v", err)
	}
	if !strings.Contains(buf.String(), "Starting fortune") {
		t.Fatalf("output: %q", buf.String())
	}
}

func TestDialWithLoadingCancel(t *testing.T) {
	block := make(chan struct{})
	dial := func(context.Context, gateway.DialRequest) (string, error) {
		<-block
		return "10.0.0.2:22", nil
	}
	ctx, cancel := context.WithCancel(context.Background())
	errCh := make(chan error, 1)
	go func() {
		_, err := gateway.DialWithLoading(ctx, ioDiscard{}, "fortune", dial, gateway.DialRequest{User: "alice", App: "fortune"})
		errCh <- err
	}()
	cancel()
	select {
	case err := <-errCh:
		if err == nil {
			t.Fatal("expected cancel error")
		}
	case <-time.After(2 * time.Second):
		t.Fatal("DialWithLoading did not return on cancel")
	}
	close(block)
}

type lockedWriter struct {
	mu  *sync.Mutex
	buf *bytes.Buffer
}

func (w *lockedWriter) Write(p []byte) (int, error) {
	w.mu.Lock()
	defer w.mu.Unlock()
	return w.buf.Write(p)
}

type ioDiscard struct{}

func (ioDiscard) Write(p []byte) (int, error) { return len(p), nil }

type staticError string

func (e staticError) Error() string { return string(e) }

const errBackend = staticError("wake failed")

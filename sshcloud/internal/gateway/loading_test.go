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

	dial := func(_ context.Context, req gateway.DialRequest) (gateway.DialTarget, error) {
		if req.User != "alice" || req.App != "fortune" || req.Gen != "g1" {
			t.Fatalf("dial args: %+v", req)
		}
		close(started)
		<-release
		return gateway.DialTarget{Addr: "10.0.0.2:22"}, nil
	}

	done := make(chan struct{})
	var target gateway.DialTarget
	var err error
	go func() {
		defer close(done)
		target, err = gateway.DialWithLoading(context.Background(), &lockedWriter{mu: &mu, buf: &buf}, "fortune", dial, gateway.DialRequest{
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
	if target.Addr != "10.0.0.2:22" {
		t.Fatalf("addr = %q", target.Addr)
	}
	mu.Lock()
	out := buf.String()
	mu.Unlock()
	if !strings.Contains(out, "Starting fortune") {
		t.Fatalf("output: %q", out)
	}
}

func TestDialWithLoadingError(t *testing.T) {
	dial := func(context.Context, gateway.DialRequest) (gateway.DialTarget, error) {
		return gateway.DialTarget{}, errBackend
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
	dial := func(context.Context, gateway.DialRequest) (gateway.DialTarget, error) {
		<-block
		return gateway.DialTarget{Addr: "10.0.0.2:22"}, nil
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

func TestDialWithLoadingRetriesTemporaryFailures(t *testing.T) {
	t.Parallel()
	attempts := 0
	dial := func(context.Context, gateway.DialRequest) (gateway.DialTarget, error) {
		attempts++
		if attempts < 3 {
			return gateway.DialTarget{}, temporaryTestError{}
		}
		return gateway.DialTarget{Addr: "10.0.0.2:22"}, nil
	}
	var out bytes.Buffer
	target, err := gateway.DialWithLoading(context.Background(), &out, "fortune", dial, gateway.DialRequest{
		User: "alice", App: "fortune", RetryFor: 2 * time.Second,
	})
	if err != nil || target.Addr == "" || attempts != 3 {
		t.Fatalf("target=%+v attempts=%d err=%v", target, attempts, err)
	}
	if !strings.Contains(out.String(), "retrying") {
		t.Fatalf("missing retry status: %q", out.String())
	}
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

type temporaryTestError struct{}

func (temporaryTestError) Error() string   { return "warming" }
func (temporaryTestError) Temporary() bool { return true }

const errBackend = staticError("wake failed")

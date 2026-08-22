package proxy_test

import (
	"context"
	"io"
	"net"
	"sync"
	"testing"
	"time"

	"github.com/imjasonh/playground/sshapp/internal/proxy"
)

type fakeBackend struct {
	mu      sync.Mutex
	addr    string
	ready   chan struct{}
	active  int
	ensures int
}

func (f *fakeBackend) EnsureReady(ctx context.Context) (string, error) {
	f.mu.Lock()
	f.ensures++
	ready := f.ready
	addr := f.addr
	f.mu.Unlock()

	if ready != nil {
		select {
		case <-ready:
		case <-ctx.Done():
			return "", ctx.Err()
		}
	}
	return addr, nil
}

func (f *fakeBackend) SetActiveConnections(n int) {
	f.mu.Lock()
	f.active = n
	f.mu.Unlock()
}

func TestHoldThenSplice(t *testing.T) {
	t.Parallel()

	backendLn, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	defer backendLn.Close()

	banner := make(chan string, 1)
	go func() {
		c, err := backendLn.Accept()
		if err != nil {
			return
		}
		defer c.Close()
		_, _ = io.WriteString(c, "SSH-2.0-fake\r\n")
		buf := make([]byte, 64)
		n, _ := c.Read(buf)
		banner <- string(buf[:n])
	}()

	ready := make(chan struct{})
	fb := &fakeBackend{addr: backendLn.Addr().String(), ready: ready}

	proxyLn, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	defer proxyLn.Close()

	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()
	srv := &proxy.Server{Backend: fb, WarmTimeout: 5 * time.Second, DialTimeout: time.Second}
	go func() { _ = srv.Serve(ctx, proxyLn) }()

	client, err := net.Dial("tcp", proxyLn.Addr().String())
	if err != nil {
		t.Fatal(err)
	}
	defer client.Close()

	// Connection is held: backend not ready yet, client has no banner.
	time.Sleep(50 * time.Millisecond)
	_ = client.SetReadDeadline(time.Now().Add(30 * time.Millisecond))
	buf := make([]byte, 16)
	if _, err := client.Read(buf); err == nil {
		t.Fatal("expected no data before backend is ready")
	}
	_ = client.SetReadDeadline(time.Time{})

	close(ready)

	_ = client.SetReadDeadline(time.Now().Add(2 * time.Second))
	n, err := client.Read(buf)
	if err != nil {
		t.Fatalf("read banner: %v", err)
	}
	got := string(buf[:n])
	if got != "SSH-2.0-fake\r\n" {
		t.Fatalf("banner = %q", got)
	}

	_, _ = io.WriteString(client, "hello-backend")
	select {
	case msg := <-banner:
		if msg != "hello-backend" {
			t.Fatalf("backend got %q", msg)
		}
	case <-time.After(2 * time.Second):
		t.Fatal("backend did not receive client bytes")
	}
}

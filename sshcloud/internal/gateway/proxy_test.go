package gateway_test

import (
	"bytes"
	"context"
	"io"
	"net"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
	"time"

	"github.com/imjasonh/playground/sshcloud/internal/backend"
	"github.com/imjasonh/playground/sshcloud/internal/gateway"
	"github.com/imjasonh/playground/sshcloud/internal/userca"
)

func TestProxyFortuneWithCert(t *testing.T) {
	ca, err := userca.LoadOrGenerate("")
	if err != nil {
		t.Fatal(err)
	}
	dir := t.TempDir()
	caPub := filepath.Join(dir, "ca.pub")
	if err := os.WriteFile(caPub, ca.PublicAuthorizedKey(), 0o644); err != nil {
		t.Fatal(err)
	}
	bin := filepath.Join(dir, "fortune")
	cmd := exec.Command("go", "build", "-o", bin, "github.com/imjasonh/playground/sshcloud/cmd/fortune")
	cmd.Env = append(os.Environ(), "GOTOOLCHAIN=auto")
	if out, err := cmd.CombinedOutput(); err != nil {
		t.Fatalf("build fortune: %v\n%s", err, out)
	}

	lf := backend.NewLocalFortune(bin, caPub)
	defer lf.Stop()
	addr, err := lf.Ensure()
	if err != nil {
		t.Fatal(err)
	}

	var out bytes.Buffer
	rw := struct {
		io.Reader
		io.Writer
	}{Reader: eofReader{}, Writer: &out}

	if err := gateway.ProxySSH(context.Background(), rw, ca, "alice", addr); err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(out.String(), "hello alice") {
		t.Fatalf("output: %q", out.String())
	}
}

func TestProxyCancelInterruptsStalledSSHHandshake(t *testing.T) {
	t.Parallel()
	ca, err := userca.LoadOrGenerate("")
	if err != nil {
		t.Fatal(err)
	}
	listener, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	defer listener.Close()
	accepted := make(chan net.Conn, 1)
	go func() {
		conn, err := listener.Accept()
		if err == nil {
			accepted <- conn // Intentionally never write an SSH version.
		}
	}()

	ctx, cancel := context.WithCancel(context.Background())
	result := make(chan error, 1)
	go func() {
		result <- gateway.ProxySSH(ctx, struct {
			io.Reader
			io.Writer
		}{Reader: eofReader{}, Writer: io.Discard}, ca, "alice", listener.Addr().String())
	}()
	var stalled net.Conn
	select {
	case stalled = <-accepted:
	case <-time.After(2 * time.Second):
		t.Fatal("proxy did not connect to stalled backend")
	}
	defer stalled.Close()
	cancel()
	select {
	case err := <-result:
		if err == nil {
			t.Fatal("canceled handshake unexpectedly succeeded")
		}
	case <-time.After(2 * time.Second):
		t.Fatal("cancellation did not interrupt backend SSH handshake")
	}
}

type eofReader struct{}

func (eofReader) Read([]byte) (int, error) { return 0, io.EOF }

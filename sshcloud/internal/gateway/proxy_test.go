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

	"golang.org/x/crypto/ssh"

	"github.com/imjasonh/playground/sshcloud/internal/backend"
	"github.com/imjasonh/playground/sshcloud/internal/gateway"
	"github.com/imjasonh/playground/sshcloud/internal/hostkey"
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
	addr, hostPublicKey, err := lf.Target("", "fortune", "", "")
	if err != nil {
		t.Fatal(err)
	}

	var out bytes.Buffer
	rw := struct {
		io.Reader
		io.Writer
	}{Reader: eofReader{}, Writer: &out}

	_, err = gateway.ProxySSHStreams(
		context.Background(), rw, &out, &out, ca, "alice",
		gateway.DialTarget{Addr: addr, SSHHostPublicKey: hostPublicKey}, shellSpec(),
	)
	if err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(out.String(), "hello alice") {
		t.Fatalf("output: %q", out.String())
	}
	_, wrongSigner, err := hostkey.Generate()
	if err != nil {
		t.Fatal(err)
	}
	_, err = gateway.ProxySSHStreams(
		context.Background(), eofReader{}, io.Discard, io.Discard, ca, "alice",
		gateway.DialTarget{
			Addr: addr, SSHHostPublicKey: string(ssh.MarshalAuthorizedKey(wrongSigner.PublicKey())),
		}, shellSpec(),
	)
	if err == nil || !strings.Contains(err.Error(), "handshake") {
		t.Fatalf("wrong host key error = %v", err)
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
	_, signer, err := hostkey.Generate()
	if err != nil {
		t.Fatal(err)
	}
	go func() {
		_, err := gateway.ProxySSHStreams(ctx, struct {
			io.Reader
			io.Writer
		}{Reader: eofReader{}, Writer: io.Discard}, io.Discard, io.Discard, ca, "alice",
			gateway.DialTarget{
				Addr:             listener.Addr().String(),
				SSHHostPublicKey: string(ssh.MarshalAuthorizedKey(signer.PublicKey())),
			}, shellSpec())
		result <- err
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

func shellSpec() *gateway.SessionSpec {
	changes := make(chan gateway.ForwardRequest)
	close(changes)
	return gateway.NewSessionSpec(gateway.SessionShell, nil, "", nil, false, changes, nil)
}

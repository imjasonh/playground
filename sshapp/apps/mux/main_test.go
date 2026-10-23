package main

import (
	"crypto/ed25519"
	"crypto/rand"
	"encoding/pem"
	"fmt"
	"io"
	"net"
	"os"
	"testing"
	"time"

	"charm.land/ssh"
	"charm.land/wish/v2"
	"github.com/imjasonh/playground/sshapp/internal/route"
	gossh "golang.org/x/crypto/ssh"
)

func TestMuxConfigFromAppConfig(t *testing.T) {
	t.Setenv("SSHAPP_APP_CONFIG", `{"hello":{"replicas":2,"scale_to_zero":false},"other":{"replicas":1,"scale_to_zero":true}}`)
	t.Setenv("SSHAPP_IDLE_AFTER", "1m")
	_ = os.Unsetenv("SSHAPP_APPS")
	cfg, err := muxConfigFromEnv()
	if err != nil {
		t.Fatal(err)
	}
	hello, ok := cfg.Apps["hello"]
	if !ok || hello.Replicas != 2 || hello.ScaleToZero {
		t.Fatalf("hello = %+v", hello)
	}
	other, ok := cfg.Apps["other"]
	if !ok || other.Replicas != 1 || !other.ScaleToZero {
		t.Fatalf("other = %+v", other)
	}
	if cfg.IdleAfter.Minutes() != 1 {
		t.Fatalf("idle = %v", cfg.IdleAfter)
	}
}

func TestMuxConfigLegacyAppsCSV(t *testing.T) {
	_ = os.Unsetenv("SSHAPP_APP_CONFIG")
	t.Setenv("SSHAPP_APPS", "hello,other")
	cfg, err := muxConfigFromEnv()
	if err != nil {
		t.Fatal(err)
	}
	if len(cfg.Apps) != 2 || !cfg.Apps["hello"].ScaleToZero {
		t.Fatalf("apps = %#v", cfg.Apps)
	}
}

func TestMuxConfigRequiresApps(t *testing.T) {
	_ = os.Unsetenv("SSHAPP_APP_CONFIG")
	_ = os.Unsetenv("SSHAPP_APPS")
	if _, err := muxConfigFromEnv(); err == nil {
		t.Fatal("expected error")
	}
}

func TestProxySSHSessionHoldsShellOpen(t *testing.T) {
	// Shell returns as soon as the backend accepts the request. The drain
	// used to close the session two seconds later, before a second client
	// could connect. Shorten it so a missing Wait fails this test quickly.
	prev := shellDrain
	shellDrain = 50 * time.Millisecond
	t.Cleanup(func() { shellDrain = prev })

	release := make(chan struct{})
	backend := startProxyBackend(t, func(sess ssh.Session) {
		_, _ = io.WriteString(sess, "ready\n")
		select {
		case <-release:
		case <-sess.Context().Done():
		}
	})
	returned := make(chan error, 1)
	front := startProxyBackend(t, func(sess ssh.Session) {
		signer, err := newEphemeralSigner()
		if err != nil {
			returned <- err
			return
		}
		code, err := proxySSHSession(sess, backend, signer, route.Target{App: "hold"})
		if err != nil {
			returned <- err
			return
		}
		if code != 0 {
			returned <- fmt.Errorf("exit %d", code)
			return
		}
		returned <- nil
	})

	stdout := dialShell(t, front)
	if got := readSome(t, stdout); got != "ready\n" {
		t.Fatalf("stdout = %q", got)
	}
	select {
	case err := <-returned:
		t.Fatalf("proxy returned while the backend session was open: %v", err)
	case <-time.After(300 * time.Millisecond):
	}
	close(release)
	select {
	case err := <-returned:
		if err != nil {
			t.Fatal(err)
		}
	case <-time.After(5 * time.Second):
		t.Fatal("proxy did not return after the backend exited")
	}
}

func TestProxySSHSessionCopiesShortShell(t *testing.T) {
	backend := startProxyBackend(t, func(sess ssh.Session) {
		_, _ = io.WriteString(sess, "hi\n")
	})
	returned := make(chan error, 1)
	front := startProxyBackend(t, func(sess ssh.Session) {
		signer, err := newEphemeralSigner()
		if err != nil {
			returned <- err
			return
		}
		code, err := proxySSHSession(sess, backend, signer, route.Target{App: "hi"})
		if err != nil {
			returned <- err
			return
		}
		if code != 0 {
			returned <- fmt.Errorf("exit %d", code)
			return
		}
		returned <- nil
	})

	stdout := dialShell(t, front)
	if got := readSome(t, stdout); got != "hi\n" {
		t.Fatalf("stdout = %q", got)
	}
	select {
	case err := <-returned:
		if err != nil {
			t.Fatal(err)
		}
	case <-time.After(5 * time.Second):
		t.Fatal("proxy did not return after the backend exited")
	}
}

func startProxyBackend(t *testing.T, handler ssh.Handler) string {
	t.Helper()
	ln, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	srv, err := wish.NewServer(
		wish.WithHostKeyPEM(testHostPEM(t)),
		wish.WithPublicKeyAuth(func(ssh.Context, ssh.PublicKey) bool { return true }),
		wish.WithMiddleware(func(next ssh.Handler) ssh.Handler {
			return func(sess ssh.Session) {
				handler(sess)
				next(sess)
			}
		}),
	)
	if err != nil {
		t.Fatal(err)
	}
	go func() { _ = srv.Serve(ln) }()
	t.Cleanup(func() {
		_ = srv.Close()
		_ = ln.Close()
	})
	return ln.Addr().String()
}

func testHostPEM(t *testing.T) []byte {
	t.Helper()
	_, priv, err := ed25519.GenerateKey(rand.Reader)
	if err != nil {
		t.Fatal(err)
	}
	block, err := gossh.MarshalPrivateKey(priv, "")
	if err != nil {
		t.Fatal(err)
	}
	return pem.EncodeToMemory(block)
}

func dialShell(t *testing.T, addr string) io.Reader {
	t.Helper()
	signer, err := newEphemeralSigner()
	if err != nil {
		t.Fatal(err)
	}
	conn, err := gossh.Dial("tcp", addr, &gossh.ClientConfig{
		User:            "e2e",
		Auth:            []gossh.AuthMethod{gossh.PublicKeys(signer)},
		HostKeyCallback: gossh.InsecureIgnoreHostKey(),
		Timeout:         5 * time.Second,
	})
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { _ = conn.Close() })
	sess, err := conn.NewSession()
	if err != nil {
		t.Fatal(err)
	}
	stdout, err := sess.StdoutPipe()
	if err != nil {
		t.Fatal(err)
	}
	if err := sess.Shell(); err != nil {
		t.Fatal(err)
	}
	return stdout
}

func readSome(t *testing.T, r io.Reader) string {
	t.Helper()
	buf := make([]byte, 32)
	type result struct {
		n   int
		err error
	}
	ch := make(chan result, 1)
	go func() {
		n, err := r.Read(buf)
		ch <- result{n, err}
	}()
	select {
	case res := <-ch:
		if res.err != nil && res.n == 0 {
			t.Fatal(res.err)
		}
		return string(buf[:res.n])
	case <-time.After(5 * time.Second):
		t.Fatal("timed out reading session output")
	}
	return ""
}

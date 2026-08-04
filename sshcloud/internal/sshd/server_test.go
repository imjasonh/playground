package sshd

import (
	"bytes"
	"context"
	"crypto/ed25519"
	"crypto/rand"
	"fmt"
	"io"
	"log"
	"net"
	"strings"
	"testing"
	"time"

	"golang.org/x/crypto/ssh"

	"github.com/imjasonh/playground/sshcloud/internal/gateway"
	"github.com/imjasonh/playground/sshcloud/internal/hostkey"
	"github.com/imjasonh/playground/sshcloud/internal/session"
	"github.com/imjasonh/playground/sshcloud/internal/store"
)

func TestJoinMenuFortuneBusy(t *testing.T) {
	_, signer, err := hostkey.Generate()
	if err != nil {
		t.Fatal(err)
	}
	hub := &gateway.Hub{Store: store.NewMemory(), Sessions: session.NewRegistry()}
	var logBuf bytes.Buffer
	srv := &Server{Hub: hub, HostKey: signer, Addr: "127.0.0.1:0", Logger: log.New(&logBuf, "", 0)}
	if err := srv.Listen(); err != nil {
		t.Fatal(err)
	}
	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()
	go func() { _ = srv.Serve(ctx) }()
	defer func() {
		cancel()
		_ = srv.Close()
	}()
	time.Sleep(50 * time.Millisecond)

	clientKey := mustKey(t)
	addr := srv.Addr

	// Join, select fortune (1), enter to leave stub, quit menu
	out := sshRun(t, addr, signer.PublicKey(), clientKey, "join", "alice\n1\n\nq\n")
	if !strings.Contains(out, "You're alice") {
		t.Fatalf("join output: %q\nserver log:\n%s", out, logBuf.String())
	}
	if !strings.Contains(strings.ToLower(out), "fortune") {
		t.Fatalf("expected fortune in session: %q\nserver log:\n%s", out, logBuf.String())
	}

	// Hold a session via hub, then SSH should be busy
	hold, err := hub.OpenApp(ctx, "alice", "fortune")
	if err != nil || hold.Action != gateway.ActionProxyApp {
		t.Fatalf("hold: %+v %v", hold, err)
	}
	out = sshRun(t, addr, signer.PublicKey(), clientKey, "fortune", "")
	if !strings.Contains(out, "busy") {
		t.Fatalf("expected busy, got %q\nserver log:\n%s", out, logBuf.String())
	}
	hub.ReleaseSession(hold.Session)

	out = sshRun(t, addr, signer.PublicKey(), clientKey, "fortune", "\n")
	if strings.Contains(out, "busy") || !strings.Contains(strings.ToLower(out), "fortune") {
		t.Fatalf("expected fortune after release, got %q\nserver log:\n%s", out, logBuf.String())
	}
}

func mustKey(t *testing.T) ssh.Signer {
	t.Helper()
	_, priv, err := ed25519.GenerateKey(rand.Reader)
	if err != nil {
		t.Fatal(err)
	}
	s, err := ssh.NewSignerFromKey(priv)
	if err != nil {
		t.Fatal(err)
	}
	return s
}

func sshRun(t *testing.T, addr string, hostPub ssh.PublicKey, client ssh.Signer, user, stdin string) string {
	t.Helper()
	cfg := &ssh.ClientConfig{
		User: user,
		Auth: []ssh.AuthMethod{ssh.PublicKeys(client)},
		HostKeyCallback: func(hostname string, remote net.Addr, key ssh.PublicKey) error {
			if !bytes.Equal(key.Marshal(), hostPub.Marshal()) {
				return fmt.Errorf("unexpected host key")
			}
			return nil
		},
		Timeout: 5 * time.Second,
	}
	conn, err := ssh.Dial("tcp", addr, cfg)
	if err != nil {
		t.Fatalf("dial: %v", err)
	}
	defer conn.Close()
	sess, err := conn.NewSession()
	if err != nil {
		t.Fatalf("session: %v", err)
	}
	defer sess.Close()

	stdout, err := sess.StdoutPipe()
	if err != nil {
		t.Fatal(err)
	}
	stderr, err := sess.StderrPipe()
	if err != nil {
		t.Fatal(err)
	}
	stdinPipe, err := sess.StdinPipe()
	if err != nil {
		t.Fatal(err)
	}

	modes := ssh.TerminalModes{ssh.ECHO: 0}
	if err := sess.RequestPty("xterm", 40, 80, modes); err != nil {
		t.Fatalf("pty: %v", err)
	}
	if err := sess.Shell(); err != nil {
		t.Fatalf("shell: %v", err)
	}

	var out bytes.Buffer
	done := make(chan struct{})
	go func() {
		defer close(done)
		_, _ = io.Copy(&out, io.MultiReader(stdout, stderr))
	}()

	if _, err := io.WriteString(stdinPipe, stdin); err != nil {
		t.Fatalf("stdin: %v", err)
	}
	_ = stdinPipe.Close()
	_ = sess.Wait()
	<-done
	return out.String()
}

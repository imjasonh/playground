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
	"sync"
	"testing"
	"time"

	"golang.org/x/crypto/ssh"

	"github.com/imjasonh/playground/sshcloud/internal/gateway"
	"github.com/imjasonh/playground/sshcloud/internal/hostkey"
	"github.com/imjasonh/playground/sshcloud/internal/session"
	"github.com/imjasonh/playground/sshcloud/internal/store"
)

func TestJoinDeployFortuneBusy(t *testing.T) {
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
	digest := "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"

	// Join → deploy fortune → open fortune from menu → quit
	script := strings.Join([]string{
		"alice",
		"1", // deploy
		"fortune",
		"ghcr.io/example/fortune@sha256:" + digest,
		"",  // tiny
		"2", // kick
		"",  // enter after deploy
		"1", // fortune
		"",  // enter after stub
		"q",
	}, "\n") + "\n"
	out := sshRun(t, addr, signer.PublicKey(), clientKey, "join", script)
	if !strings.Contains(out, "You're alice") {
		t.Fatalf("join output: %q\nserver log:\n%s", out, logBuf.String())
	}
	if !strings.Contains(out, "Created fortune") {
		t.Fatalf("expected deploy create: %q\nserver log:\n%s", out, logBuf.String())
	}
	if !strings.Contains(strings.ToLower(out), "fortune") {
		t.Fatalf("expected fortune in session: %q\nserver log:\n%s", out, logBuf.String())
	}

	app, err := hub.Store.GetApp(ctx, "alice", "fortune")
	if err != nil || app == nil || !strings.Contains(app.Image, digest) {
		t.Fatalf("stored app: %+v %v", app, err)
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

func TestJoinDeployExecArgs(t *testing.T) {
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
	digest := "fedcba9876543210fedcba9876543210fedcba9876543210fedcba9876543210"
	img := "ghcr.io/example/fortune@sha256:" + digest

	out, code := sshExec(t, addr, signer.PublicKey(), clientKey, "join", "demo")
	if code != 0 || !strings.Contains(out, "Joined as demo") {
		t.Fatalf("join: code=%d out=%q log=%s", code, out, logBuf.String())
	}

	out, code = sshExec(t, addr, signer.PublicKey(), clientKey, "deploy",
		"fortune --image="+img+" --tier=tiny --strategy=kick --yes")
	if code != 0 || !strings.Contains(out, "fortune") {
		t.Fatalf("deploy: code=%d out=%q log=%s", code, out, logBuf.String())
	}
	app, err := hub.Store.GetApp(ctx, "demo", "fortune")
	if err != nil || app == nil || app.Image != img {
		t.Fatalf("app %+v %v", app, err)
	}

	out, code = sshExec(t, addr, signer.PublicKey(), clientKey, "deploy",
		"fortune --image="+img+" --strategy=kick")
	if code == 0 || !strings.Contains(out, "--yes") {
		t.Fatalf("expected update requires --yes: code=%d out=%q", code, out)
	}

	out, code = sshExec(t, addr, signer.PublicKey(), clientKey, "fortune", "true")
	if code == 0 || !strings.Contains(out, "not configured") {
		t.Fatalf("app exec without backend must fail explicitly: code=%d out=%q", code, out)
	}

	unknownKey := mustKey(t)
	out = sshExecRejected(t, addr, signer.PublicKey(), unknownKey, "fortune", "git-upload-pack owner/repo")
	if !strings.Contains(out, "join@host") {
		t.Fatalf("unknown-key app exec: out=%q", out)
	}
	unknown, err := hub.Store.LookupUserByKey(ctx, ssh.FingerprintSHA256(unknownKey.PublicKey()))
	if err != nil || unknown != nil {
		t.Fatalf("exec attempt created user: %+v, %v", unknown, err)
	}

	out, code = sshExec(t, addr, signer.PublicKey(), unknownKey, "join", "bob extra")
	if code != 2 || !strings.Contains(out, "Usage:") {
		t.Fatalf("join extra args: code=%d out=%q", code, out)
	}
}

func sshExecRejected(t *testing.T, addr string, hostPub ssh.PublicKey, client ssh.Signer, user, command string) string {
	t.Helper()
	conn := sshClient(t, addr, hostPub, client, user)
	defer conn.Close()
	sess, err := conn.NewSession()
	if err != nil {
		t.Fatal(err)
	}
	stderr, err := sess.StderrPipe()
	if err != nil {
		t.Fatal(err)
	}
	if err := sess.Start(command); err == nil {
		t.Fatalf("command %q unexpectedly started", command)
	}
	output, _ := io.ReadAll(stderr)
	return string(output)
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

func sshClient(t *testing.T, addr string, hostPub ssh.PublicKey, client ssh.Signer, user string) *ssh.Client {
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
	return conn
}

func sshRun(t *testing.T, addr string, hostPub ssh.PublicKey, client ssh.Signer, user, stdin string) string {
	t.Helper()
	conn := sshClient(t, addr, hostPub, client, user)
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

func sshExec(t *testing.T, addr string, hostPub ssh.PublicKey, client ssh.Signer, user, cmd string) (string, int) {
	t.Helper()
	conn := sshClient(t, addr, hostPub, client, user)
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
	var out bytes.Buffer
	var mu sync.Mutex
	var wg sync.WaitGroup
	wg.Add(2)
	copyPipe := func(r io.Reader) {
		defer wg.Done()
		b, _ := io.ReadAll(r)
		mu.Lock()
		out.Write(b)
		mu.Unlock()
	}
	go copyPipe(stdout)
	go copyPipe(stderr)
	err = sess.Start(cmd)
	if err != nil {
		t.Fatalf("start %q: %v", cmd, err)
	}
	waitErr := sess.Wait()
	wg.Wait()
	code := 0
	if waitErr != nil {
		if ee, ok := waitErr.(*ssh.ExitError); ok {
			code = ee.ExitStatus()
		} else {
			t.Fatalf("wait %q: %v\n%s", cmd, waitErr, out.String())
		}
	}
	return out.String(), code
}

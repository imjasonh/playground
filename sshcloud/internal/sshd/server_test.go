package sshd

import (
	"bytes"
	"context"
	"crypto/ed25519"
	"crypto/rand"
	"encoding/json"
	"fmt"
	"io"
	"log"
	"net"
	"os"
	"path/filepath"
	"strings"
	"sync"
	"testing"
	"time"

	"golang.org/x/crypto/ssh"

	"github.com/imjasonh/playground/sshcloud/internal/access"
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
	hold, err := hub.OpenApp(ctx, ssh.FingerprintSHA256(clientKey.PublicKey()), "alice", "fortune")
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

func TestSSHAccessPolicyStagesAndMenuHandoff(t *testing.T) {
	_, hostSigner, err := hostkey.Generate()
	if err != nil {
		t.Fatal(err)
	}
	memberKey := mustKey(t)
	deployerKey := mustKey(t)
	otherKey := mustKey(t)
	policyPath := filepath.Join(t.TempDir(), "access-policy.json")
	writeAccessPolicy(t, policyPath, "allowlist", "allowlist", []ssh.Signer{memberKey}, []ssh.Signer{deployerKey})

	st := store.NewMemory()
	hub := &gateway.Hub{
		Store:    st,
		Sessions: session.NewRegistry(),
		Access:   access.FileSource{Path: policyPath},
	}
	srv := &Server{Hub: hub, HostKey: hostSigner, Addr: "127.0.0.1:0"}
	if err := srv.Listen(); err != nil {
		t.Fatal(err)
	}
	ctx, cancel := context.WithCancel(context.Background())
	go func() { _ = srv.Serve(ctx) }()
	defer func() {
		cancel()
		_ = srv.Close()
	}()
	time.Sleep(50 * time.Millisecond)

	addr := srv.Addr
	hostKey := hostSigner.PublicKey()
	digest := strings.Repeat("a", 64)
	deploy := "demoapp --image=ghcr.io/example/app@sha256:" + digest + " --tier=tiny --strategy=kick --yes"

	out, code := sshExec(t, addr, hostKey, memberKey, "join", "alice")
	if code != 0 || !strings.Contains(out, "Joined as alice") {
		t.Fatalf("member join: code=%d out=%q", code, out)
	}
	out, code = sshExec(t, addr, hostKey, memberKey, "deploy", deploy)
	if code == 0 || !strings.Contains(out, "Forbidden:") {
		t.Fatalf("member deploy should be forbidden: code=%d out=%q", code, out)
	}
	out, code = sshRunCode(t, addr, hostKey, memberKey, "menu", "1\n")
	if code == 0 || !strings.Contains(out, "Forbidden:") {
		t.Fatalf("menu deploy handoff should be forbidden: code=%d out=%q", code, out)
	}
	if err := st.UpsertApp(ctx, store.App{
		Owner: "alice", Name: "memberapp",
		Image: "ghcr.io/example/app@sha256:" + digest, Tier: "tiny",
	}); err != nil {
		t.Fatal(err)
	}
	out, code = sshRunCode(t, addr, hostKey, memberKey, "memberapp", "\n")
	if code != 0 || !strings.Contains(out, `app "memberapp"`) {
		t.Fatalf("member app use: code=%d out=%q", code, out)
	}

	out, code = sshExec(t, addr, hostKey, deployerKey, "join", "operator")
	if code != 0 || !strings.Contains(out, "Joined as operator") {
		t.Fatalf("deployer must imply membership: code=%d out=%q", code, out)
	}
	out, code = sshExec(t, addr, hostKey, deployerKey, "deploy", deploy)
	if code != 0 || !strings.Contains(out, "Created demoapp") {
		t.Fatalf("allowlisted deployer: code=%d out=%q", code, out)
	}

	out, code = sshExec(t, addr, hostKey, otherKey, "join", "bob")
	if code == 0 || !strings.Contains(out, "Forbidden:") {
		t.Fatalf("unlisted key should be forbidden: code=%d out=%q", code, out)
	}

	writeAccessPolicy(t, policyPath, "open", "allowlist", nil, []ssh.Signer{deployerKey})
	out, code = sshExec(t, addr, hostKey, otherKey, "join", "bob")
	if code != 0 || !strings.Contains(out, "Joined as bob") {
		t.Fatalf("open join: code=%d out=%q", code, out)
	}
	out, code = sshExec(t, addr, hostKey, otherKey, "deploy", deploy)
	if code == 0 || !strings.Contains(out, "Forbidden:") {
		t.Fatalf("open join must retain deploy allowlist: code=%d out=%q", code, out)
	}

	writeAccessPolicy(t, policyPath, "open", "all-users", nil, nil)
	out, code = sshExec(t, addr, hostKey, otherKey, "deploy", deploy)
	if code != 0 || !strings.Contains(out, "Created demoapp") {
		t.Fatalf("all-users deploy: code=%d out=%q", code, out)
	}

	if err := os.WriteFile(policyPath, []byte("{corrupt"), 0o600); err != nil {
		t.Fatal(err)
	}
	out, code = sshExec(t, addr, hostKey, memberKey, "join", "alice")
	if code == 0 || !strings.Contains(out, "access policy is unavailable") {
		t.Fatalf("corrupt configured policy must fail closed: code=%d out=%q", code, out)
	}
}

func TestSSHAccessPolicyRevokesOpenConnection(t *testing.T) {
	_, hostSigner, err := hostkey.Generate()
	if err != nil {
		t.Fatal(err)
	}
	memberKey := mustKey(t)
	policyPath := filepath.Join(t.TempDir(), "access-policy.json")
	writeAccessPolicy(t, policyPath, "allowlist", "allowlist", []ssh.Signer{memberKey}, nil)

	st := store.NewMemory()
	fingerprint := ssh.FingerprintSHA256(memberKey.PublicKey())
	if err := st.CreateUser(context.Background(), "alice", fingerprint); err != nil {
		t.Fatal(err)
	}
	hub := &gateway.Hub{
		Store: st, Sessions: session.NewRegistry(),
		Access: access.FileSource{Path: policyPath},
	}
	srv := &Server{
		Hub: hub, HostKey: hostSigner, Addr: "127.0.0.1:0",
		AccessRecheckInterval: 10 * time.Millisecond,
	}
	if err := srv.Listen(); err != nil {
		t.Fatal(err)
	}
	ctx, cancel := context.WithCancel(context.Background())
	go func() { _ = srv.Serve(ctx) }()
	defer func() {
		cancel()
		_ = srv.Close()
	}()

	client := sshClient(t, srv.Addr, hostSigner.PublicKey(), memberKey, "menu")
	defer client.Close()
	appSession, err := client.NewSession()
	if err != nil {
		t.Fatal(err)
	}
	stdin, err := appSession.StdinPipe()
	if err != nil {
		t.Fatal(err)
	}
	defer stdin.Close()
	if err := appSession.RequestPty("xterm", 40, 80, ssh.TerminalModes{}); err != nil {
		t.Fatal(err)
	}
	if err := appSession.Shell(); err != nil {
		t.Fatal(err)
	}
	wait := make(chan error, 1)
	go func() { wait <- appSession.Wait() }()

	writeAccessPolicy(t, policyPath, "allowlist", "allowlist", nil, nil)
	select {
	case err := <-wait:
		if err == nil {
			t.Fatal("revoked connection exited successfully")
		}
	case <-time.After(time.Second):
		t.Fatal("revoked connection remained open")
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
	out, _ := sshRunCode(t, addr, hostPub, client, user, stdin)
	return out
}

func sshRunCode(t *testing.T, addr string, hostPub ssh.PublicKey, client ssh.Signer, user, stdin string) (string, int) {
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
	waitErr := sess.Wait()
	<-done
	code := 0
	if waitErr != nil {
		if ee, ok := waitErr.(*ssh.ExitError); ok {
			code = ee.ExitStatus()
		} else {
			t.Fatalf("wait shell: %v\n%s", waitErr, out.String())
		}
	}
	return out.String(), code
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

func writeAccessPolicy(t *testing.T, path, joinMode, deployMode string, members, deployers []ssh.Signer) {
	t.Helper()
	keyLines := func(signers []ssh.Signer) []string {
		lines := make([]string, 0, len(signers))
		for _, signer := range signers {
			lines = append(lines, strings.TrimSpace(string(ssh.MarshalAuthorizedKey(signer.PublicKey()))))
		}
		return lines
	}
	data, err := json.Marshal(map[string]any{
		"version":                  1,
		"join_mode":                joinMode,
		"deploy_mode":              deployMode,
		"member_ssh_public_keys":   keyLines(members),
		"deployer_ssh_public_keys": keyLines(deployers),
	})
	if err != nil {
		t.Fatal(err)
	}
	tmp := path + ".new"
	if err := os.WriteFile(tmp, data, 0o600); err != nil {
		t.Fatal(err)
	}
	if err := os.Rename(tmp, path); err != nil {
		t.Fatal(err)
	}
}

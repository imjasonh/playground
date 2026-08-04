package sshd

import (
	"bufio"
	"bytes"
	"context"
	"fmt"
	"io"
	"net"
	"net/http"
	"net/http/httptest"
	"strings"
	"sync"
	"testing"
	"time"

	"golang.org/x/crypto/ssh"

	"github.com/imjasonh/playground/sshcloud/internal/backend"
	"github.com/imjasonh/playground/sshcloud/internal/cutover"
	"github.com/imjasonh/playground/sshcloud/internal/gateway"
	"github.com/imjasonh/playground/sshcloud/internal/hostkey"
	"github.com/imjasonh/playground/sshcloud/internal/session"
	"github.com/imjasonh/playground/sshcloud/internal/store"
	"github.com/imjasonh/playground/sshcloud/internal/userca"
)

const chaosAppName = "myapp"

type cutoverE2E struct {
	ctx       context.Context
	cancel    context.CancelFunc
	server    *Server
	hub       *gateway.Hub
	store     *store.Memory
	fleet     *chaosFleet
	hostKey   ssh.Signer
	clientKey ssh.Signer
	control   *backend.GatewayClient
}

func newCutoverE2E(t *testing.T) *cutoverE2E {
	t.Helper()
	ca, _, err := userca.Generate()
	if err != nil {
		t.Fatal(err)
	}
	_, gatewayHost, err := hostkey.Generate()
	if err != nil {
		t.Fatal(err)
	}
	clientKey := mustKey(t)
	ctx, cancel := context.WithCancel(context.Background())
	st := store.NewMemory()
	if err := st.CreateUser(ctx, "alice", ssh.FingerprintSHA256(clientKey.PublicKey())); err != nil {
		t.Fatal(err)
	}
	sessions := session.NewRegistry()
	fleet := newChaosFleet(t, ca.PublicKey())
	controller := cutover.New(st, sessions, fleet)
	controller.Timeout = time.Hour
	hub := &gateway.Hub{
		Store:             st,
		Sessions:          sessions,
		UserCA:            ca,
		Dial:              fleet.Dial,
		Cutover:           controller,
		AllowedRegistries: []string{"ghcr.io"},
	}
	controlToken := "0123456789abcdef0123456789abcdef"
	controlMux := http.NewServeMux()
	(&gateway.ControlHandler{Hub: hub, Token: controlToken, MaxFreeze: 5 * time.Second}).Mount(controlMux)
	controlServer := httptest.NewServer(controlMux)
	srv := &Server{
		Hub: hub, HostKey: gatewayHost, Addr: "127.0.0.1:0",
		HandshakeTimeout: 2 * time.Second,
	}
	if err := srv.Listen(); err != nil {
		t.Fatal(err)
	}
	go func() { _ = srv.Serve(ctx) }()

	fx := &cutoverE2E{
		ctx: ctx, cancel: cancel, server: srv, hub: hub, store: st,
		fleet: fleet, hostKey: gatewayHost, clientKey: clientKey,
		control: &backend.GatewayClient{BaseURL: controlServer.URL, Token: controlToken},
	}
	t.Cleanup(func() {
		cancel()
		_ = srv.Close()
		fleet.Close()
		controlServer.Close()
	})
	return fx
}

func (f *cutoverE2E) deploy(t *testing.T, image, strategy string) *store.App {
	t.Helper()
	out, code := sshExec(t, f.server.Addr, f.hostKey.PublicKey(), f.clientKey, "deploy",
		fmt.Sprintf("%s --image=%s --tier=tiny --strategy=%s --yes", chaosAppName, image, strategy))
	if code != 0 {
		t.Fatalf("deploy %s: code=%d output=%q", strategy, code, out)
	}
	app, err := f.store.GetApp(f.ctx, "alice", chaosAppName)
	if err != nil || app == nil {
		t.Fatalf("deployed app: %+v, %v", app, err)
	}
	return app
}

func (f *cutoverE2E) openApp(t *testing.T) *liveSSHSession {
	return f.openSSH(t, chaosAppName)
}

func (f *cutoverE2E) openSSH(t *testing.T, user string) *liveSSHSession {
	t.Helper()
	client := sshClient(t, f.server.Addr, f.hostKey.PublicKey(), f.clientKey, user)
	sess, err := client.NewSession()
	if err != nil {
		client.Close()
		t.Fatal(err)
	}
	stdout, err := sess.StdoutPipe()
	if err != nil {
		client.Close()
		t.Fatal(err)
	}
	stderr, err := sess.StderrPipe()
	if err != nil {
		client.Close()
		t.Fatal(err)
	}
	stdin, err := sess.StdinPipe()
	if err != nil {
		client.Close()
		t.Fatal(err)
	}
	if err := sess.RequestPty("xterm", 40, 80, ssh.TerminalModes{ssh.ECHO: 0}); err != nil {
		client.Close()
		t.Fatal(err)
	}
	if err := sess.Shell(); err != nil {
		client.Close()
		t.Fatal(err)
	}
	live := &liveSSHSession{
		client: client, session: sess, stdin: stdin,
		lines: make(chan string, 64), wait: make(chan error, 1),
	}
	go live.scan(stdout)
	go live.scan(stderr)
	go func() { live.wait <- sess.Wait() }()
	return live
}

func TestMenuInputBrokerSurvivesAppHandoff(t *testing.T) {
	fx := newCutoverE2E(t)
	image := "ghcr.io/example/app@sha256:" + strings.Repeat("f", 64)
	app := fx.deploy(t, image, store.StrategyKick)
	live := fx.openSSH(t, "menu")
	defer live.close()
	live.awaitLine(t, "Apps for alice")
	live.send(t, "1")
	live.awaitLine(t, "READY", app.ActiveGen)
	live.send(t, "quit")
	live.awaitLine(t, "Apps for alice")
	live.send(t, "q")
	if err := live.awaitExit(t); err != nil {
		t.Fatalf("menu exit: %v", err)
	}
}

type liveSSHSession struct {
	client  *ssh.Client
	session *ssh.Session
	stdin   io.WriteCloser
	lines   chan string
	wait    chan error
	once    sync.Once
}

func (s *liveSSHSession) scan(r io.Reader) {
	scanner := bufio.NewScanner(r)
	for scanner.Scan() {
		line := strings.TrimSpace(strings.TrimSuffix(scanner.Text(), "\r"))
		select {
		case s.lines <- line:
		default:
		}
	}
}

func (s *liveSSHSession) send(t *testing.T, line string) {
	t.Helper()
	if _, err := io.WriteString(s.stdin, line+"\n"); err != nil {
		t.Fatalf("send %q: %v", line, err)
	}
}

func (s *liveSSHSession) awaitLine(t *testing.T, contains ...string) string {
	t.Helper()
	timer := time.NewTimer(5 * time.Second)
	defer timer.Stop()
	for {
		select {
		case line := <-s.lines:
			matches := true
			for _, part := range contains {
				if !strings.Contains(line, part) {
					matches = false
					break
				}
			}
			if matches {
				return line
			}
		case err := <-s.wait:
			t.Fatalf("session exited before %v: %v", contains, err)
		case <-timer.C:
			t.Fatalf("timeout waiting for line containing %v", contains)
		}
	}
}

func (s *liveSSHSession) awaitExit(t *testing.T) error {
	t.Helper()
	select {
	case err := <-s.wait:
		return err
	case <-time.After(5 * time.Second):
		t.Fatal("timeout waiting for SSH session exit")
		return nil
	}
}

func (s *liveSSHSession) close() {
	s.once.Do(func() {
		_ = s.stdin.Close()
		_ = s.session.Close()
		_ = s.client.Close()
	})
}

func TestLiveSessionDeployDrainE2E(t *testing.T) {
	fx := newCutoverE2E(t)
	oldImage := "ghcr.io/example/app@sha256:" + strings.Repeat("a", 64)
	newImage := "ghcr.io/example/app@sha256:" + strings.Repeat("b", 64)

	oldApp := fx.deploy(t, oldImage, store.StrategyKick)
	old := fx.openApp(t)
	defer old.close()
	old.awaitLine(t, "READY", oldApp.ActiveGen, oldImage, "alice")

	newApp := fx.deploy(t, newImage, store.StrategyDrain)
	if newApp.DrainingGen != oldApp.ActiveGen || newApp.ActiveGen == oldApp.ActiveGen {
		t.Fatalf("bad drain state: old=%+v new=%+v", oldApp, newApp)
	}
	if fx.fleet.wasStopped(oldApp.ActiveGen) {
		t.Fatal("drain stopped the old generation while its session was live")
	}

	old.send(t, "ping")
	old.awaitLine(t, "PONG", oldApp.ActiveGen)

	fresh := fx.openApp(t)
	defer fresh.close()
	fresh.awaitLine(t, "READY", newApp.ActiveGen, newImage, "alice")
	fresh.send(t, "ping")
	fresh.awaitLine(t, "PONG", newApp.ActiveGen)

	old.send(t, "quit")
	if err := old.awaitExit(t); err != nil {
		t.Fatalf("old session exit: %v", err)
	}
	fx.fleet.awaitStop(t, oldApp.ActiveGen)
	after, err := fx.store.GetApp(fx.ctx, "alice", chaosAppName)
	if err != nil || after == nil || after.DrainingGen != "" {
		t.Fatalf("drain did not finish: %+v, %v", after, err)
	}

	fresh.send(t, "ping")
	fresh.awaitLine(t, "PONG", newApp.ActiveGen)
	fresh.send(t, "quit")
	if err := fresh.awaitExit(t); err != nil {
		t.Fatalf("new session exit: %v", err)
	}
}

func TestLiveSessionDeployKickE2E(t *testing.T) {
	fx := newCutoverE2E(t)
	oldImage := "ghcr.io/example/app@sha256:" + strings.Repeat("c", 64)
	newImage := "ghcr.io/example/app@sha256:" + strings.Repeat("d", 64)

	oldApp := fx.deploy(t, oldImage, store.StrategyKick)
	old := fx.openApp(t)
	defer old.close()
	old.awaitLine(t, "READY", oldApp.ActiveGen, oldImage, "alice")

	newApp := fx.deploy(t, newImage, store.StrategyKick)
	if newApp.DrainingGen != "" || newApp.ActiveGen == oldApp.ActiveGen {
		t.Fatalf("bad kick state: old=%+v new=%+v", oldApp, newApp)
	}
	if err := old.awaitExit(t); err == nil {
		t.Fatal("kicked session unexpectedly exited successfully")
	}
	fx.fleet.awaitStop(t, oldApp.ActiveGen)
	if fx.hub.Sessions.ActiveGen("alice", chaosAppName, oldApp.ActiveGen) {
		t.Fatal("kicked generation retained a session slot")
	}

	fresh := fx.openApp(t)
	defer fresh.close()
	fresh.awaitLine(t, "READY", newApp.ActiveGen, newImage, "alice")
	fresh.send(t, "quit")
	if err := fresh.awaitExit(t); err != nil {
		t.Fatalf("new session exit: %v", err)
	}
}

func TestLiveSessionHostMigrationFreezeThawE2E(t *testing.T) {
	fx := newCutoverE2E(t)
	image := "ghcr.io/example/app@sha256:" + strings.Repeat("e", 64)
	app := fx.deploy(t, image, store.StrategyKick)
	live := fx.openApp(t)
	defer live.close()
	live.awaitLine(t, "READY", app.ActiveGen, image, "alice")

	freezeCtx, cancelFreeze := context.WithTimeout(fx.ctx, 2*time.Second)
	token, count, err := fx.control.Freeze(freezeCtx, "alice", chaosAppName, app.ActiveGen, 5*time.Second)
	cancelFreeze()
	if err != nil || count != 1 {
		t.Fatalf("freeze count=%d err=%v", count, err)
	}
	live.awaitLine(t, "migration in progress")
	// No backend reads the outer channel while frozen. This input remains
	// bounded by the SSH channel window and is replayed after reconnect.
	live.send(t, "ping")
	if err := fx.fleet.replace(app.ActiveGen); err != nil {
		t.Fatal(err)
	}

	thawCtx, cancelThaw := context.WithTimeout(fx.ctx, 2*time.Second)
	err = fx.control.Thaw(thawCtx, token)
	cancelThaw()
	if err != nil {
		t.Fatalf("thaw: %v", err)
	}
	live.awaitLine(t, "migration complete")
	live.awaitLine(t, "READY", app.ActiveGen, image, "alice")
	live.awaitLine(t, "PONG", app.ActiveGen)
	live.send(t, "quit")
	if err := live.awaitExit(t); err != nil {
		t.Fatalf("migrated session exit: %v", err)
	}
}

type chaosFleet struct {
	t     *testing.T
	caPub ssh.PublicKey

	mu      sync.Mutex
	apps    map[string]*chaosApp
	images  map[string]string
	tiers   map[string]string
	stopped map[string]int
	stops   chan string
}

func newChaosFleet(t *testing.T, caPub ssh.PublicKey) *chaosFleet {
	return &chaosFleet{
		t: t, caPub: caPub, apps: make(map[string]*chaosApp),
		images: make(map[string]string), tiers: make(map[string]string),
		stopped: make(map[string]int), stops: make(chan string, 32),
	}
}

func (f *chaosFleet) Ensure(_ context.Context, _, _, gen, image, tier string, _ bool) error {
	f.mu.Lock()
	defer f.mu.Unlock()
	if existing := f.apps[gen]; existing != nil {
		if f.images[gen] != image || f.tiers[gen] != tier {
			return fmt.Errorf("generation %s spec changed from %s/%s to %s/%s", gen, f.images[gen], f.tiers[gen], image, tier)
		}
		return nil
	}
	app, err := newChaosApp(f.caPub, gen, image)
	if err != nil {
		return err
	}
	f.apps[gen], f.images[gen], f.tiers[gen] = app, image, tier
	return nil
}

func (f *chaosFleet) Stop(_ context.Context, _, _, gen string) error {
	f.mu.Lock()
	app := f.apps[gen]
	if app != nil {
		delete(f.apps, gen)
		f.stopped[gen]++
	}
	f.mu.Unlock()
	if app != nil {
		app.Close()
		f.stops <- gen
	}
	return nil
}

func (f *chaosFleet) SetNoIdle(context.Context, string, string, string, bool) error {
	return nil
}

func (f *chaosFleet) Dial(ctx context.Context, req gateway.DialRequest) (string, error) {
	if err := f.Ensure(ctx, req.User, req.App, req.Gen, req.Image, req.Tier, req.NoIdle); err != nil {
		return "", err
	}
	f.mu.Lock()
	defer f.mu.Unlock()
	return f.apps[req.Gen].Addr(), nil
}

func (f *chaosFleet) wasStopped(gen string) bool {
	f.mu.Lock()
	defer f.mu.Unlock()
	return f.stopped[gen] > 0
}

func (f *chaosFleet) awaitStop(t *testing.T, gen string) {
	t.Helper()
	timer := time.NewTimer(5 * time.Second)
	defer timer.Stop()
	for {
		select {
		case got := <-f.stops:
			if got == gen {
				return
			}
		case <-timer.C:
			t.Fatalf("timeout waiting for stop of %s", gen)
		}
	}
}

func (f *chaosFleet) replace(gen string) error {
	f.mu.Lock()
	old := f.apps[gen]
	image, tier := f.images[gen], f.tiers[gen]
	delete(f.apps, gen)
	f.mu.Unlock()
	if old == nil {
		return fmt.Errorf("unknown generation %s", gen)
	}
	old.Close()
	replacement, err := newChaosApp(f.caPub, gen, image)
	if err != nil {
		return err
	}
	f.mu.Lock()
	f.apps[gen], f.images[gen], f.tiers[gen] = replacement, image, tier
	f.mu.Unlock()
	return nil
}

func (f *chaosFleet) Close() {
	f.mu.Lock()
	apps := make([]*chaosApp, 0, len(f.apps))
	for _, app := range f.apps {
		apps = append(apps, app)
	}
	f.apps = make(map[string]*chaosApp)
	f.mu.Unlock()
	for _, app := range apps {
		app.Close()
	}
}

type chaosApp struct {
	listener net.Listener
	config   *ssh.ServerConfig
	gen      string
	image    string

	once  sync.Once
	mu    sync.Mutex
	conns map[net.Conn]struct{}
}

func newChaosApp(caPub ssh.PublicKey, gen, image string) (*chaosApp, error) {
	_, hostSigner, err := hostkey.Generate()
	if err != nil {
		return nil, err
	}
	checker := &ssh.CertChecker{
		IsUserAuthority: func(auth ssh.PublicKey) bool {
			return bytes.Equal(auth.Marshal(), caPub.Marshal())
		},
	}
	config := &ssh.ServerConfig{PublicKeyCallback: checker.Authenticate}
	config.AddHostKey(hostSigner)
	ln, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		return nil, err
	}
	app := &chaosApp{
		listener: ln, config: config, gen: gen, image: image,
		conns: make(map[net.Conn]struct{}),
	}
	go app.serve()
	return app, nil
}

func (a *chaosApp) Addr() string { return a.listener.Addr().String() }

func (a *chaosApp) serve() {
	for {
		conn, err := a.listener.Accept()
		if err != nil {
			return
		}
		a.mu.Lock()
		a.conns[conn] = struct{}{}
		a.mu.Unlock()
		go a.handleConn(conn)
	}
}

func (a *chaosApp) handleConn(conn net.Conn) {
	defer func() {
		_ = conn.Close()
		a.mu.Lock()
		delete(a.conns, conn)
		a.mu.Unlock()
	}()
	serverConn, channels, requests, err := ssh.NewServerConn(conn, a.config)
	if err != nil {
		return
	}
	defer serverConn.Close()
	go ssh.DiscardRequests(requests)
	for newChannel := range channels {
		if newChannel.ChannelType() != "session" {
			_ = newChannel.Reject(ssh.UnknownChannelType, "session only")
			continue
		}
		channel, reqs, err := newChannel.Accept()
		if err != nil {
			continue
		}
		go a.handleSession(serverConn.User(), channel, reqs)
	}
}

func (a *chaosApp) handleSession(user string, channel ssh.Channel, requests <-chan *ssh.Request) {
	defer channel.Close()
	for req := range requests {
		switch req.Type {
		case "pty-req", "env", "window-change":
			if req.WantReply {
				_ = req.Reply(true, nil)
			}
		case "shell":
			if req.WantReply {
				_ = req.Reply(true, nil)
			}
			_, _ = fmt.Fprintf(channel, "READY %s %s %s\r\n", a.gen, a.image, user)
			scanner := bufio.NewScanner(channel)
			for scanner.Scan() {
				switch strings.TrimSpace(scanner.Text()) {
				case "ping":
					_, _ = fmt.Fprintf(channel, "PONG %s\r\n", a.gen)
				case "quit":
					sendExit(channel, 0)
					return
				}
			}
			return
		default:
			if req.WantReply {
				_ = req.Reply(false, nil)
			}
		}
	}
}

func (a *chaosApp) Close() {
	a.once.Do(func() {
		_ = a.listener.Close()
		a.mu.Lock()
		for conn := range a.conns {
			_ = conn.Close()
		}
		a.mu.Unlock()
	})
}

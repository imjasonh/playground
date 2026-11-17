// Command mux is the shared SSH front door for sshapp. One LoadBalancer hits
// this process. Bare SSH sessions get an in-process app registry menu. Named
// apps (command path / subsystem / SSHAPP env) scale from zero and are
// SSH-proxied to the Wish backend.
package main

import (
	"context"
	"crypto/ed25519"
	"crypto/rand"
	"encoding/json/v2"
	"errors"
	"fmt"
	"io"
	"log/slog"
	"net"
	"os"
	"os/signal"
	"sort"
	"strings"
	"syscall"
	"time"

	"charm.land/ssh"
	"charm.land/wish/v2"
	"charm.land/wish/v2/logging"
	"github.com/chainguard-dev/clog"
	_ "github.com/chainguard-dev/clog/gcp/init"
	"github.com/sethvargo/go-envconfig"
	gossh "golang.org/x/crypto/ssh"

	"github.com/imjasonh/playground/sshapp/internal/registry"
	"github.com/imjasonh/playground/sshapp/internal/route"
	"github.com/imjasonh/playground/sshapp/internal/scaler"
	"github.com/imjasonh/playground/sshapp/internal/sshpty"
)

func main() {
	cfg, err := muxConfigFromEnv()
	if err != nil {
		clog.Fatal("config", "error", err)
	}

	names := make([]string, 0, len(cfg.Apps))
	for name := range cfg.Apps {
		names = append(names, name)
	}
	sort.Strings(names)
	catalog := registry.FromNames(names)
	pool := scaler.NewPool(cfg.Apps, func(app string) (*scaler.DeploymentScaler, error) {
		spec := cfg.Apps[app]
		return scaler.NewK8s(scaler.K8sConfig{
			Namespace:    cfg.Namespace,
			Deployment:   app,
			Service:      app,
			Port:         cfg.BackendPort,
			WarmReplicas: spec.Replicas,
			IdleAfter:    cfg.IdleAfter,
			ScaleToZero:  spec.ScaleToZero,
			Kubeconfig:   cfg.Kubeconfig,
		})
	})

	signer, err := newEphemeralSigner()
	if err != nil {
		clog.Fatal("backend client key", "error", err)
	}

	opts := []ssh.Option{
		wish.WithAddress(cfg.Listen),
		wish.WithPublicKeyAuth(func(_ ssh.Context, _ ssh.PublicKey) bool {
			// Placeholder: accept any user key. Wire an allowlist / IdP later.
			return true
		}),
		wish.WithMiddleware(
			muxMiddleware(catalog, pool, signer, cfg.WarmTimeout),
			logging.Middleware(),
		),
	}
	if cfg.HostKeyPEM != "" {
		opts = append(opts, wish.WithHostKeyPEM([]byte(cfg.HostKeyPEM)))
	} else {
		opts = append(opts, wish.WithHostKeyPath(cfg.HostKeyPath))
	}

	srv, err := wish.NewServer(opts...)
	if err != nil {
		clog.Fatal("create server", "error", err)
	}

	ctx, stop := signal.NotifyContext(context.Background(), os.Interrupt, syscall.SIGTERM)
	defer stop()

	slog.Info("mux listening",
		"addr", cfg.Listen,
		"apps", strings.Join(names, ","),
		"idle_after", cfg.IdleAfter.String(),
	)
	go func() {
		if err := srv.ListenAndServe(); err != nil && !errors.Is(err, ssh.ErrServerClosed) {
			slog.Error("listen", "error", err)
			stop()
		}
	}()
	<-ctx.Done()
	shutdownCtx, cancel := context.WithTimeout(context.Background(), 15*time.Second)
	defer cancel()
	_ = srv.Shutdown(shutdownCtx)
}

func muxMiddleware(catalog registry.Catalog, pool *scaler.Pool, signer gossh.Signer, warmTimeout time.Duration) wish.Middleware {
	return func(_ ssh.Handler) ssh.Handler {
		return func(sess ssh.Session) {
			target, ok := route.FromSession(sess)
			if !ok {
				entry, err := catalog.Pick(sess, sess)
				if errors.Is(err, registry.ErrCanceled) {
					_ = sess.Exit(0)
					return
				}
				if err != nil {
					_, _ = fmt.Fprintf(sess.Stderr(), "%v\n", err)
					_ = sess.Exit(2)
					return
				}
				target = route.Target{App: entry.Name}
			}

			if _, known := catalog.Lookup(target.App); !known {
				_, _ = fmt.Fprintf(sess.Stderr(), "unknown app %q\n", target.App)
				_ = catalog.WriteList(sess.Stderr())
				_ = sess.Exit(2)
				return
			}

			pool.Acquire(target.App)
			defer pool.Release(target.App)

			warmCtx, cancel := context.WithTimeout(sess.Context(), warmTimeout)
			defer cancel()
			addr, err := pool.EnsureReady(warmCtx, target.App)
			if err != nil {
				_, _ = fmt.Fprintf(sess.Stderr(), "scale %s: %v\n", target.App, err)
				_ = sess.Exit(1)
				return
			}

			code, err := proxySSHSession(warmCtx, sess, addr, signer, target)
			if err != nil {
				slog.Error("proxy session", "app", target.App, "error", err)
				_ = sess.Exit(1)
				return
			}
			_ = sess.Exit(code)
		}
	}
}

// backendAttempt bounds one try at a backend session, from the TCP dial
// through the shell or exec request. x/crypto/ssh times out only the dial, so
// a backend that accepts the connection and then stalls would otherwise hold
// the client with no output and no error.
var backendAttempt = 5 * time.Second

// proxySSHSession retries the backend session setup until ctx ends. The
// client's input isn't read until a backend session starts, so a retry loses
// nothing.
func proxySSHSession(ctx context.Context, clientSess ssh.Session, addr string, signer gossh.Signer, target route.Target) (int, error) {
	pty, winCh, isPty := clientSess.Pty()
	term := ""
	if isPty {
		term, _, _ = sshpty.Normalize(pty.Term, pty.Window.Width, pty.Window.Height)
	}

	var b *backendSession
	for attempt := 1; ; attempt++ {
		var err error
		b, err = startBackendSession(ctx, clientSess.User(), addr, signer, target, pty, isPty)
		if err == nil {
			break
		}
		if ctx.Err() != nil {
			return 1, err
		}
		slog.Warn("backend session setup failed; retrying",
			"app", target.App, "addr", addr, "attempt", attempt, "error", err)
		select {
		case <-ctx.Done():
			return 1, err
		case <-time.After(250 * time.Millisecond):
		}
	}
	defer b.conn.Close()
	defer b.sess.Close()

	if isPty {
		go func() {
			for win := range winCh {
				_, w, h := sshpty.Normalize(term, win.Width, win.Height)
				_ = b.sess.WindowChange(h, w)
			}
		}()
	}

	copyDone := make(chan struct{}, 2)
	go func() {
		_, _ = io.Copy(clientSess, b.stdout)
		copyDone <- struct{}{}
	}()
	go func() {
		_, _ = io.Copy(clientSess.Stderr(), b.stderr)
		copyDone <- struct{}{}
	}()
	go func() {
		_, _ = io.Copy(b.stdin, clientSess)
		_ = b.stdin.Close()
	}()
	// Close the backend when the client leaves so long-lived apps Release.
	go func() {
		<-clientSess.Context().Done()
		_ = b.sess.Close()
		_ = b.conn.Close()
	}()

	// Wait until the backend session exits so an interactive app stays up
	// for the whole connection.
	err := b.sess.Wait()
	// Copy the last stdout and stderr bytes after the backend exits.
	drain := time.NewTimer(shellDrain)
	defer drain.Stop()
	for remaining := 2; remaining > 0; {
		select {
		case <-copyDone:
			remaining--
		case <-drain.C:
			remaining = 0
		}
	}

	if err == nil {
		return 0, nil
	}
	var exitErr *gossh.ExitError
	if errors.As(err, &exitErr) {
		return exitErr.ExitStatus(), nil
	}
	// The client left, or the backend connection dropped without a status.
	var missing *gossh.ExitMissingError
	if errors.As(err, &missing) || clientSess.Context().Err() != nil {
		return 0, nil
	}
	return 1, err
}

// shellDrain bounds the stdout and stderr copy after the backend session ends.
var shellDrain = 2 * time.Second

// backendSession is a started shell or exec session on a backend.
type backendSession struct {
	conn   *gossh.Client
	sess   *gossh.Session
	stdout io.Reader
	stderr io.Reader
	stdin  io.WriteCloser
}

func startBackendSession(ctx context.Context, user, addr string, signer gossh.Signer, target route.Target, pty ssh.Pty, isPty bool) (*backendSession, error) {
	ctx, cancel := context.WithTimeout(ctx, backendAttempt)
	defer cancel()
	var d net.Dialer
	nc, err := d.DialContext(ctx, "tcp", addr)
	if err != nil {
		return nil, err
	}
	deadline, _ := ctx.Deadline()
	if err := nc.SetDeadline(deadline); err != nil {
		_ = nc.Close()
		return nil, err
	}
	cc, chans, reqs, err := gossh.NewClientConn(nc, addr, &gossh.ClientConfig{
		User:            user,
		Auth:            []gossh.AuthMethod{gossh.PublicKeys(signer)},
		HostKeyCallback: gossh.InsecureIgnoreHostKey(), // backends are cluster-internal
	})
	if err != nil {
		_ = nc.Close()
		return nil, err
	}
	conn := gossh.NewClient(cc, chans, reqs)
	b, err := openBackendSession(conn, target, pty, isPty)
	if err == nil {
		err = nc.SetDeadline(time.Time{})
	}
	if err != nil {
		_ = conn.Close()
		return nil, err
	}
	return b, nil
}

func openBackendSession(conn *gossh.Client, target route.Target, pty ssh.Pty, isPty bool) (*backendSession, error) {
	sess, err := conn.NewSession()
	if err != nil {
		return nil, err
	}
	if isPty {
		term, width, height := sshpty.Normalize(pty.Term, pty.Window.Width, pty.Window.Height)
		if err := sess.RequestPty(term, height, width, nil); err != nil {
			return nil, err
		}
	}
	b := &backendSession{conn: conn, sess: sess}
	if b.stdout, err = sess.StdoutPipe(); err != nil {
		return nil, err
	}
	if b.stderr, err = sess.StderrPipe(); err != nil {
		return nil, err
	}
	if b.stdin, err = sess.StdinPipe(); err != nil {
		return nil, err
	}
	if len(target.Args) > 0 {
		err = sess.Start(strings.Join(target.Args, " "))
	} else {
		err = sess.Shell()
	}
	if err != nil {
		return nil, err
	}
	return b, nil
}

func newEphemeralSigner() (gossh.Signer, error) {
	_, priv, err := ed25519.GenerateKey(rand.Reader)
	if err != nil {
		return nil, err
	}
	return gossh.NewSignerFromKey(priv)
}

type muxConfig struct {
	Listen      string
	Namespace   string
	Apps        map[string]scaler.AppSpec
	BackendPort int32
	IdleAfter   time.Duration
	WarmTimeout time.Duration
	HostKeyPEM  string
	HostKeyPath string
	Kubeconfig  string
}

type appSpecJSON struct {
	Replicas    int  `json:"replicas"`
	ScaleToZero bool `json:"scale_to_zero"`
}

func muxConfigFromEnv() (muxConfig, error) {
	// Process returns the error so tests can set the environment and load
	// again. App JSON and the legacy CSV stay custom.
	var env struct {
		Listen      string        `env:"SSHAPP_LISTEN, default=:2222"`
		Namespace   string        `env:"SSHAPP_NAMESPACE, default=sshapps"`
		IdleAfter   time.Duration `env:"SSHAPP_IDLE_AFTER, default=5m"`
		WarmTimeout time.Duration `env:"SSHAPP_WARM_TIMEOUT, default=2m"`
		HostKeyPEM  string        `env:"SSHAPP_HOST_KEY"`
		HostKeyPath string        `env:"SSHAPP_HOST_KEY_PATH, default=.ssh/mux_ed25519"`
		Kubeconfig  string        `env:"KUBECONFIG"`
		AppConfig   string        `env:"SSHAPP_APP_CONFIG"`
		Apps        string        `env:"SSHAPP_APPS"`
	}
	if err := envconfig.Process(context.Background(), &env); err != nil {
		return muxConfig{}, err
	}
	apps, err := appsFromConfig(env.AppConfig, env.Apps)
	if err != nil {
		return muxConfig{}, err
	}
	return muxConfig{
		Listen:      env.Listen,
		Namespace:   env.Namespace,
		Apps:        apps,
		BackendPort: 2222,
		IdleAfter:   env.IdleAfter,
		WarmTimeout: env.WarmTimeout,
		HostKeyPEM:  env.HostKeyPEM,
		HostKeyPath: env.HostKeyPath,
		Kubeconfig:  env.Kubeconfig,
	}, nil
}

func appsFromConfig(raw, appsCSV string) (map[string]scaler.AppSpec, error) {
	if raw != "" {
		var parsed map[string]appSpecJSON
		if err := json.Unmarshal([]byte(raw), &parsed); err != nil {
			return nil, fmt.Errorf("SSHAPP_APP_CONFIG: %w", err)
		}
		if len(parsed) == 0 {
			return nil, errors.New("SSHAPP_APP_CONFIG is empty")
		}
		out := make(map[string]scaler.AppSpec, len(parsed))
		for name, spec := range parsed {
			replicas := int32(spec.Replicas)
			if replicas <= 0 {
				replicas = 1
			}
			out[name] = scaler.AppSpec{
				Replicas:    replicas,
				ScaleToZero: spec.ScaleToZero,
			}
		}
		return out, nil
	}

	// Legacy: comma-separated names, all scale-to-zero with 1 warm replica.
	if appsCSV == "" {
		return nil, errors.New("SSHAPP_APP_CONFIG or SSHAPP_APPS is required")
	}
	out := make(map[string]scaler.AppSpec)
	for _, a := range strings.Split(appsCSV, ",") {
		a = strings.TrimSpace(a)
		if a == "" {
			continue
		}
		out[a] = scaler.AppSpec{Replicas: 1, ScaleToZero: true}
	}
	if len(out) == 0 {
		return nil, errors.New("SSHAPP_APPS is empty")
	}
	return out, nil
}

// Command mux is the shared SSH front door for sshapp. One LoadBalancer hits
// this process. It authenticates real users, picks an app from the remote
// command path (ssh user@host foo/bar), subsystem, or SSHAPP environ, scales
// that app from zero, then SSH-proxies the session to the Wish backend.
package main

import (
	"context"
	"crypto/ed25519"
	"crypto/rand"
	"errors"
	"fmt"
	"io"
	"os"
	"os/signal"
	"strconv"
	"strings"
	"syscall"
	"time"

	"charm.land/log/v2"
	"charm.land/ssh"
	"charm.land/wish/v2"
	"charm.land/wish/v2/logging"
	gossh "golang.org/x/crypto/ssh"

	"github.com/imjasonh/playground/sshapp/internal/route"
	"github.com/imjasonh/playground/sshapp/internal/scaler"
)

func main() {
	cfg, err := muxConfigFromEnv()
	if err != nil {
		log.Fatal("config", "error", err)
	}

	pool := scaler.NewPool(cfg.Apps, func(app string) (*scaler.DeploymentScaler, error) {
		return scaler.NewK8s(scaler.K8sConfig{
			Namespace:    cfg.Namespace,
			Deployment:   app,
			Service:      app,
			Port:         cfg.BackendPort,
			WarmReplicas: cfg.WarmReplicas,
			IdleAfter:    cfg.IdleAfter,
			Kubeconfig:   cfg.Kubeconfig,
		})
	})

	signer, err := newEphemeralSigner()
	if err != nil {
		log.Fatal("backend client key", "error", err)
	}

	opts := []ssh.Option{
		wish.WithAddress(cfg.Listen),
		wish.WithPublicKeyAuth(func(_ ssh.Context, _ ssh.PublicKey) bool {
			// Placeholder: accept any user key. Wire an allowlist / IdP later.
			return true
		}),
		wish.WithMiddleware(
			muxMiddleware(pool, signer, cfg.WarmTimeout),
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
		log.Fatal("create server", "error", err)
	}

	ctx, stop := signal.NotifyContext(context.Background(), os.Interrupt, syscall.SIGTERM)
	defer stop()

	log.Info("mux listening",
		"addr", cfg.Listen,
		"apps", strings.Join(cfg.Apps, ","),
		"idle_after", cfg.IdleAfter.String(),
	)
	go func() {
		if err := srv.ListenAndServe(); err != nil && !errors.Is(err, ssh.ErrServerClosed) {
			log.Error("listen", "error", err)
			stop()
		}
	}()
	<-ctx.Done()
	shutdownCtx, cancel := context.WithTimeout(context.Background(), 15*time.Second)
	defer cancel()
	_ = srv.Shutdown(shutdownCtx)
}

func muxMiddleware(pool *scaler.Pool, signer gossh.Signer, warmTimeout time.Duration) wish.Middleware {
	return func(next ssh.Handler) ssh.Handler {
		return func(sess ssh.Session) {
			target, ok := route.FromSession(sess)
			if !ok {
				_, _ = fmt.Fprint(sess.Stderr(), "usage: ssh user@host <app>[/<path>]   or SetEnv SSHAPP=<app>\n")
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

			if err := proxySSHSession(sess, addr, signer, target); err != nil {
				log.Error("proxy session", "app", target.App, "error", err)
				_ = sess.Exit(1)
				return
			}
			next(sess)
		}
	}
}

func proxySSHSession(clientSess ssh.Session, addr string, signer gossh.Signer, target route.Target) error {
	cfg := &gossh.ClientConfig{
		User: clientSess.User(),
		Auth: []gossh.AuthMethod{
			gossh.PublicKeys(signer),
		},
		HostKeyCallback: gossh.InsecureIgnoreHostKey(), // backends are cluster-internal
		Timeout:         10 * time.Second,
	}
	conn, err := gossh.Dial("tcp", addr, cfg)
	if err != nil {
		return err
	}
	defer conn.Close()

	bs, err := conn.NewSession()
	if err != nil {
		return err
	}
	defer bs.Close()

	pty, winCh, isPty := clientSess.Pty()
	if isPty {
		if err := bs.RequestPty(pty.Term, pty.Window.Height, pty.Window.Width, nil); err != nil {
			return err
		}
		go func() {
			for win := range winCh {
				_ = bs.WindowChange(win.Height, win.Width)
			}
		}()
	}

	bs.Stdout = clientSess
	bs.Stderr = clientSess.Stderr()
	stdin, err := bs.StdinPipe()
	if err != nil {
		return err
	}
	go func() {
		_, _ = io.Copy(stdin, clientSess)
		_ = stdin.Close()
	}()

	if len(target.Args) > 0 {
		return bs.Run(strings.Join(target.Args, " "))
	}
	return bs.Shell()
}

func newEphemeralSigner() (gossh.Signer, error) {
	_, priv, err := ed25519.GenerateKey(rand.Reader)
	if err != nil {
		return nil, err
	}
	return gossh.NewSignerFromKey(priv)
}

type muxConfig struct {
	Listen       string
	Namespace    string
	Apps         []string
	BackendPort  int32
	WarmReplicas int32
	IdleAfter    time.Duration
	WarmTimeout  time.Duration
	HostKeyPEM   string
	HostKeyPath  string
	Kubeconfig   string
}

func muxConfigFromEnv() (muxConfig, error) {
	appsCSV := os.Getenv("SSHAPP_APPS")
	if appsCSV == "" {
		return muxConfig{}, errors.New("SSHAPP_APPS is required (comma-separated app names)")
	}
	var apps []string
	for _, a := range strings.Split(appsCSV, ",") {
		a = strings.TrimSpace(a)
		if a != "" {
			apps = append(apps, a)
		}
	}
	if len(apps) == 0 {
		return muxConfig{}, errors.New("SSHAPP_APPS is empty")
	}

	warm := int32(1)
	if v := os.Getenv("SSHAPP_WARM_REPLICAS"); v != "" {
		n, err := strconv.Atoi(v)
		if err != nil || n < 1 {
			return muxConfig{}, errors.New("SSHAPP_WARM_REPLICAS must be >= 1")
		}
		warm = int32(n)
	}
	idle := 5 * time.Minute
	warmTimeout := 2 * time.Minute
	if v := os.Getenv("SSHAPP_IDLE_AFTER"); v != "" {
		d, err := time.ParseDuration(v)
		if err != nil {
			return muxConfig{}, err
		}
		idle = d
	}
	if v := os.Getenv("SSHAPP_WARM_TIMEOUT"); v != "" {
		d, err := time.ParseDuration(v)
		if err != nil {
			return muxConfig{}, err
		}
		warmTimeout = d
	}

	return muxConfig{
		Listen:       envOr("SSHAPP_LISTEN", ":2222"),
		Namespace:    envOr("SSHAPP_NAMESPACE", "sshapps"),
		Apps:         apps,
		BackendPort:  2222,
		WarmReplicas: warm,
		IdleAfter:    idle,
		WarmTimeout:  warmTimeout,
		HostKeyPEM:   os.Getenv("SSHAPP_HOST_KEY"),
		HostKeyPath:  envOr("SSHAPP_HOST_KEY_PATH", ".ssh/mux_ed25519"),
		Kubeconfig:   os.Getenv("KUBECONFIG"),
	}, nil
}

func envOr(key, fallback string) string {
	if v := os.Getenv(key); v != "" {
		return v
	}
	return fallback
}

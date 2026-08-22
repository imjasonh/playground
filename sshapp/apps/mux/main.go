// Command mux is the shared SSH front door for sshapp. One LoadBalancer hits
// this process. Bare SSH sessions get an in-process app registry menu. Named
// apps (command path / subsystem / SSHAPP env) scale from zero and are
// SSH-proxied to the Wish backend.
package main

import (
	"context"
	"crypto/ed25519"
	"crypto/rand"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"os"
	"os/signal"
	"sort"
	"strings"
	"syscall"
	"time"

	"charm.land/log/v2"
	"charm.land/ssh"
	"charm.land/wish/v2"
	"charm.land/wish/v2/logging"
	gossh "golang.org/x/crypto/ssh"

	"github.com/imjasonh/playground/sshapp/internal/registry"
	"github.com/imjasonh/playground/sshapp/internal/route"
	"github.com/imjasonh/playground/sshapp/internal/scaler"
)

func main() {
	cfg, err := muxConfigFromEnv()
	if err != nil {
		log.Fatal("config", "error", err)
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
		log.Fatal("backend client key", "error", err)
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
		log.Fatal("create server", "error", err)
	}

	ctx, stop := signal.NotifyContext(context.Background(), os.Interrupt, syscall.SIGTERM)
	defer stop()

	log.Info("mux listening",
		"addr", cfg.Listen,
		"apps", strings.Join(names, ","),
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

func muxMiddleware(catalog registry.Catalog, pool *scaler.Pool, signer gossh.Signer, warmTimeout time.Duration) wish.Middleware {
	return func(next ssh.Handler) ssh.Handler {
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
	apps, err := appsFromEnv()
	if err != nil {
		return muxConfig{}, err
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
		Listen:      envOr("SSHAPP_LISTEN", ":2222"),
		Namespace:   envOr("SSHAPP_NAMESPACE", "sshapps"),
		Apps:        apps,
		BackendPort: 2222,
		IdleAfter:   idle,
		WarmTimeout: warmTimeout,
		HostKeyPEM:  os.Getenv("SSHAPP_HOST_KEY"),
		HostKeyPath: envOr("SSHAPP_HOST_KEY_PATH", ".ssh/mux_ed25519"),
		Kubeconfig:  os.Getenv("KUBECONFIG"),
	}, nil
}

func appsFromEnv() (map[string]scaler.AppSpec, error) {
	if raw := os.Getenv("SSHAPP_APP_CONFIG"); raw != "" {
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
	appsCSV := os.Getenv("SSHAPP_APPS")
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

func envOr(key, fallback string) string {
	if v := os.Getenv(key); v != "" {
		return v
	}
	return fallback
}

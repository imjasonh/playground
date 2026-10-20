// Command activator is a Knative-style TCP front for Wish apps: it accepts SSH
// TCP connections, scales the app Deployment from 0→N, holds the client until
// a backend is ready, then splices bytes. After idle, it scales back to 0.
package main

import (
	"context"
	"errors"
	"log/slog"
	"net"
	"os"
	"os/signal"
	"syscall"
	"time"

	_ "github.com/chainguard-dev/clog/gcp/init"
	"github.com/sethvargo/go-envconfig"

	"github.com/imjasonh/playground/sshapp/internal/proxy"
	"github.com/imjasonh/playground/sshapp/internal/scaler"
)

func main() {
	cfg, err := configFromEnv()
	if err != nil {
		slog.Error("config", "error", err)
		os.Exit(1)
	}

	backend, err := scaler.NewK8s(cfg.K8sConfig)
	if err != nil {
		slog.Error("kubernetes client", "error", err)
		os.Exit(1)
	}

	ln, err := net.Listen("tcp", cfg.Listen)
	if err != nil {
		slog.Error("listen", "error", err)
		os.Exit(1)
	}

	ctx, stop := signal.NotifyContext(context.Background(), os.Interrupt, syscall.SIGTERM)
	defer stop()

	srv := &proxy.Server{
		Backend:     backend,
		WarmTimeout: cfg.WarmTimeout,
		DialTimeout: 5 * time.Second,
	}

	slog.Info("activator listening",
		"addr", ln.Addr().String(),
		"deployment", cfg.Deployment,
		"service", cfg.Service,
		"warm_replicas", cfg.WarmReplicas,
		"idle_after", cfg.IdleAfter.String(),
	)
	if err := srv.Serve(ctx, ln); err != nil && !errors.Is(err, net.ErrClosed) {
		slog.Error("serve", "error", err)
		os.Exit(1)
	}
}

type activatorConfig struct {
	scaler.K8sConfig
	WarmTimeout time.Duration
	Listen      string
}

func configFromEnv() (activatorConfig, error) {
	// Process returns the error so tests can set the environment and load
	// again. An empty SSHAPP_APP is present, so required would not reject it.
	var env struct {
		Listen       string        `env:"SSHAPP_LISTEN, default=:2222"`
		Namespace    string        `env:"SSHAPP_NAMESPACE, default=sshapps"`
		App          string        `env:"SSHAPP_APP"`
		WarmReplicas int32         `env:"SSHAPP_WARM_REPLICAS, default=1"`
		IdleAfter    time.Duration `env:"SSHAPP_IDLE_AFTER, default=5m"`
		WarmTimeout  time.Duration `env:"SSHAPP_WARM_TIMEOUT, default=2m"`
		Port         int32         `env:"SSHAPP_BACKEND_PORT, default=2222"`
		Kubeconfig   string        `env:"KUBECONFIG"`
	}
	if err := envconfig.Process(context.Background(), &env); err != nil {
		return activatorConfig{}, err
	}
	if env.App == "" {
		return activatorConfig{}, errors.New("SSHAPP_APP is required")
	}
	if env.WarmReplicas < 1 {
		return activatorConfig{}, errors.New("SSHAPP_WARM_REPLICAS must be >= 1")
	}
	return activatorConfig{
		K8sConfig: scaler.K8sConfig{
			Namespace:    env.Namespace,
			Deployment:   env.App,
			Service:      env.App,
			Port:         env.Port,
			WarmReplicas: env.WarmReplicas,
			IdleAfter:    env.IdleAfter,
			ScaleToZero:  true,
			Kubeconfig:   env.Kubeconfig,
		},
		WarmTimeout: env.WarmTimeout,
		Listen:      env.Listen,
	}, nil
}

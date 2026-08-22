// Command activator is a Knative-style TCP front for Wish apps: it accepts SSH
// TCP connections, scales the app Deployment from 0→N, holds the client until
// a backend is ready, then splices bytes. After idle, it scales back to 0.
package main

import (
	"context"
	"errors"
	"net"
	"os"
	"os/signal"
	"strconv"
	"syscall"
	"time"

	"charm.land/log/v2"

	"github.com/imjasonh/playground/sshapp/internal/proxy"
	"github.com/imjasonh/playground/sshapp/internal/scaler"
)

func main() {
	cfg, err := configFromEnv()
	if err != nil {
		log.Fatal("config", "error", err)
	}

	backend, err := scaler.NewK8s(cfg.K8sConfig)
	if err != nil {
		log.Fatal("kubernetes client", "error", err)
	}

	ln, err := net.Listen("tcp", envOr("SSHAPP_LISTEN", ":2222"))
	if err != nil {
		log.Fatal("listen", "error", err)
	}

	ctx, stop := signal.NotifyContext(context.Background(), os.Interrupt, syscall.SIGTERM)
	defer stop()

	srv := &proxy.Server{
		Backend:     backend,
		WarmTimeout: cfg.WarmTimeout,
		DialTimeout: 5 * time.Second,
	}

	log.Info("activator listening",
		"addr", ln.Addr().String(),
		"deployment", cfg.Deployment,
		"service", cfg.Service,
		"warm_replicas", cfg.WarmReplicas,
		"idle_after", cfg.IdleAfter.String(),
	)
	if err := srv.Serve(ctx, ln); err != nil && !errors.Is(err, net.ErrClosed) {
		log.Fatal("serve", "error", err)
	}
}

type activatorConfig struct {
	scaler.K8sConfig
	WarmTimeout time.Duration
}

func configFromEnv() (activatorConfig, error) {
	ns := envOr("SSHAPP_NAMESPACE", "sshapps")
	name := os.Getenv("SSHAPP_APP")
	if name == "" {
		return activatorConfig{}, errors.New("SSHAPP_APP is required")
	}
	warm := int32(1)
	if v := os.Getenv("SSHAPP_WARM_REPLICAS"); v != "" {
		n, err := strconv.Atoi(v)
		if err != nil || n < 1 {
			return activatorConfig{}, errors.New("SSHAPP_WARM_REPLICAS must be >= 1")
		}
		warm = int32(n)
	}
	idle := 5 * time.Minute
	if v := os.Getenv("SSHAPP_IDLE_AFTER"); v != "" {
		d, err := time.ParseDuration(v)
		if err != nil {
			return activatorConfig{}, err
		}
		idle = d
	}
	warmTimeout := 2 * time.Minute
	if v := os.Getenv("SSHAPP_WARM_TIMEOUT"); v != "" {
		d, err := time.ParseDuration(v)
		if err != nil {
			return activatorConfig{}, err
		}
		warmTimeout = d
	}
	port := int32(2222)
	if v := os.Getenv("SSHAPP_BACKEND_PORT"); v != "" {
		n, err := strconv.Atoi(v)
		if err != nil {
			return activatorConfig{}, err
		}
		port = int32(n)
	}
	return activatorConfig{
		K8sConfig: scaler.K8sConfig{
			Namespace:    ns,
			Deployment:   name,
			Service:      name,
			Port:         port,
			WarmReplicas: warm,
			IdleAfter:    idle,
			Kubeconfig:   os.Getenv("KUBECONFIG"),
		},
		WarmTimeout: warmTimeout,
	}, nil
}

func envOr(key, fallback string) string {
	if v := os.Getenv(key); v != "" {
		return v
	}
	return fallback
}

package main

import (
	"context"
	"errors"
	"log/slog"
	"net"
	"net/http"
	"os"
	"os/signal"
	"syscall"
	"time"

	"cloud.google.com/go/compute/metadata"
	"github.com/chainguard-dev/clog"
	_ "github.com/chainguard-dev/clog/gcp/init"
	"github.com/imjasonh/playground/xiao-otel/internal/attest"
	"github.com/imjasonh/playground/xiao-otel/internal/otlp"
	"github.com/sethvargo/go-envconfig"
	"golang.org/x/oauth2/google"
)

type config struct {
	Port            string `env:"PORT, default=8080"`
	AppID           string `env:"APP_ID, required"`
	AllowUnattested bool   `env:"ALLOW_UNATTESTED"`
	ProjectID       string `env:"GOOGLE_CLOUD_PROJECT"`
}

func main() {
	if err := run(context.Background()); err != nil {
		clog.Fatal("xiao-otel", "err", err)
	}
}

func run(ctx context.Context) error {
	ctx, stop := signal.NotifyContext(ctx, syscall.SIGTERM, os.Interrupt)
	defer stop()
	ctx = clog.WithLogger(ctx, clog.NewLogger(slog.Default()))

	var env config
	if err := envconfig.Process(ctx, &env); err != nil {
		return err
	}

	verifier, err := attest.NewVerifier(env.AppID, env.AllowUnattested, attest.NewMemoryStore())
	if err != nil {
		return err
	}

	projectID := env.ProjectID
	if projectID == "" && os.Getenv("K_SERVICE") != "" {
		mctx, cancel := context.WithTimeout(ctx, 2*time.Second)
		if detected, err := metadata.ProjectIDWithContext(mctx); err == nil {
			projectID = detected
		}
		cancel()
	}

	var exporter otlp.Exporter
	if projectID != "" {
		if ts, err := google.DefaultTokenSource(ctx, "https://www.googleapis.com/auth/monitoring.write"); err != nil {
			slog.WarnContext(ctx, "Cloud Monitoring token source unavailable; running in dry-run mode", "err", err)
		} else {
			exporter = &otlp.CloudMonitoringExporter{
				ProjectID:   projectID,
				TokenSource: ts,
			}
			slog.InfoContext(ctx, "Cloud Monitoring export enabled", "project", projectID)
		}
	}

	srv := &Server{
		Verifier: verifier,
		Exporter: exporter,
	}
	httpSrv := &http.Server{
		Handler:           srv.Routes(),
		ReadHeaderTimeout: 5 * time.Second,
		ReadTimeout:       15 * time.Second,
		WriteTimeout:      15 * time.Second,
		IdleTimeout:       60 * time.Second,
	}
	ln, err := net.Listen("tcp", ":"+env.Port)
	if err != nil {
		return err
	}
	go func() {
		if err := httpSrv.Serve(ln); !errors.Is(err, http.ErrServerClosed) {
			slog.ErrorContext(ctx, "serve", "err", err)
			stop()
		}
	}()
	slog.InfoContext(ctx, "listening", "port", env.Port, "app_id", env.AppID, "allow_unattested", env.AllowUnattested)

	<-ctx.Done()
	shutdownCtx, cancel := context.WithTimeout(context.Background(), 8*time.Second)
	defer cancel()
	return httpSrv.Shutdown(shutdownCtx)
}

package ok

import (
	"context"
	"flag"
	"fmt"
	"log"
	"log/slog"

	"github.com/chainguard-dev/clog"
)

func ok(ctx context.Context, t interface {
	Errorf(string, ...any)
	Fatalf(string, ...any)
}, name string, err error) {
	clog.Fatal("boom", "name", name)
	clog.InfoContext(ctx, "hello", "name", name)
	clog.WarnContext(ctx, "careful", "name", name)
	clog.FromContext(ctx).Info("hello", "name", name)
	clog.WithLogger(ctx, clog.FromContext(ctx))
	slog.Info("hello", "name", name)
	slog.InfoContext(ctx, "hello", "name", name)
	slog.Error("failed", "error", err)
	_ = fmt.Errorf("failed: %v", err)
	t.Errorf("failed: %v", err)
	t.Fatalf("boom %s", name)
	log.Printf("serving %s", name)
	log.Fatalf("boom %s", name)
	flag.String("addr", ":8080", "listen address")
	flag.String("log.level", "info", "dotted name is not this flag")
	var addr string
	flag.StringVar(&addr, "addr", ":8080", "listen address")
	fs := flag.NewFlagSet("ok", flag.ContinueOnError)
	fs.String("addr", ":8080", "listen address")
	fs.TextVar(&slog.LevelVar{}, "log-level", slog.LevelInfo, "slog level")
}

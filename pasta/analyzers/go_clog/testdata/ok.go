package ok

import (
	"context"
	"fmt"
	"log"
	"log/slog"

	"github.com/chainguard-dev/clog"
)

func ok(ctx context.Context, t interface {
	Errorf(string, ...any)
	Fatalf(string, ...any)
}, name string, err error) {
	clog.Info("hello", "name", name)
	clog.InfoContext(ctx, "hello", "name", name)
	clog.Error("failed", "error", err)
	clog.WarnContext(ctx, "careful", "name", name)
	clog.Debug("n", "n", 1)
	clog.Fatal("boom", "name", name)
	clog.FromContext(ctx).Info("hello", "name", name)
	clog.With("name", name).Error("failed", "error", err)
	slog.Info("hello", "name", name)
	slog.InfoContext(ctx, "hello", "name", name)
	slog.Error("failed", "error", err)
	_ = fmt.Errorf("failed: %v", err)
	t.Errorf("failed: %v", err)
	t.Fatalf("boom %s", name)
	log.Printf("serving %s", name)
	log.Fatalf("boom %s", name)
}

package bad

import (
	"context"
	"flag"
	"log/slog"

	"github.com/chainguard-dev/clog"
	"github.com/chainguard-dev/clog/gcp"
)

func bad(ctx context.Context, name string, err error, n int) {
	clog.Infof("hello %s", name)                                       // want "printf-style clog"
	clog.Errorf("failed: %v", err)                                     // want "printf-style clog"
	clog.Warnf("careful %s", name)                                     // want "printf-style clog"
	clog.Debugf("n=%d", n)                                             // want "printf-style clog"
	clog.Fatalf("boom %s", name)                                       // want "printf-style clog"
	clog.InfoContextf(ctx, "hello %s", name)                           // want "printf-style clog"
	clog.ErrorContextf(ctx, "failed: %v", err)                         // want "printf-style clog"
	clog.WarnContextf(ctx, "careful %s", name)                         // want "printf-style clog"
	clog.DebugContextf(ctx, "n=%d", n)                                 // want "printf-style clog"
	clog.FatalContextf(ctx, "boom %s", name)                           // want "printf-style clog"
	clog.FromContext(ctx).Infof("hello %s", name)                      // want "printf-style clog"
	clog.With("name", name).Warnf("careful %s", name)                  // want "printf-style clog" // want "default logger"
	clog.New(slog.Default().Handler()).Debugf("n=%d", n)               // want "printf-style clog"
	clog.FromContext(ctx).With("name", name).Errorf("failed: %v", err) // want "printf-style clog"

	log := clog.FromContext(ctx)
	log.Infof("hello %s", name)             // want "printf-style clog"
	log.Warnf("careful %s", name)           // want "printf-style clog"
	log.Debugf("n=%d", n)                   // want "printf-style clog"
	log.InfoContextf(ctx, "hello %s", name) // want "printf-style clog"

	clog.Info("hello", "name", name)                      // want "default logger"
	clog.Warn("careful", "name", name)                    // want "default logger"
	clog.Error("failed", "error", err)                    // want "default logger"
	clog.Debug("n", "n", n)                               // want "default logger"
	clog.With("name", name).Error("failed", "error", err) // want "default logger"

	_ = gcp.NewHandler(slog.LevelInfo)            // want "gcp.NewHandler"
	flag.String("log-level", "info", "level")     // want "string flag for a log level"
	flag.String("vfs-log-level", "warn", "level") // want "string flag for a log level"
	var level string
	flag.StringVar(&level, "log_level", "info", "level") // want "string flag for a log level"
	flag.StringVar(&level, "LOGLEVEL", "info", "level")  // want "string flag for a log level"
}

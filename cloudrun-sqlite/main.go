// Command cloudrun-sqlite serves a SQLite database whose only durable copy is
// a Litestream replica in Cloud Storage or S3. See README.md.
package main

import (
	"context"
	"crypto/rand"
	"encoding/hex"
	"errors"
	"flag"
	"fmt"
	"log/slog"
	"net"
	"net/http"
	"os"
	"os/signal"
	"path/filepath"
	"strconv"
	"syscall"
	"time"

	"github.com/chainguard-dev/clog"
	_ "github.com/chainguard-dev/clog/gcp/init"
	"github.com/chainguard-dev/clog/slag"
	"github.com/imjasonh/playground/cloudrun-sqlite/internal/observe"
	"github.com/imjasonh/playground/cloudrun-sqlite/internal/store"
)

func main() {
	if len(os.Args) > 1 && os.Args[1] == "seed" {
		if err := seedMain(os.Args[2:]); err != nil {
			fmt.Fprintln(os.Stderr, "seed:", err)
			os.Exit(1)
		}
		return
	}
	if err := serveMain(os.Args[1:]); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
}

func env(name, def string) string {
	if v := os.Getenv(name); v != "" {
		return v
	}
	return def
}

func envBool(name string, def bool) bool {
	if v, err := strconv.ParseBool(os.Getenv(name)); err == nil {
		return v
	}
	return def
}

func envDuration(name string, def time.Duration) time.Duration {
	if v, err := time.ParseDuration(os.Getenv(name)); err == nil {
		return v
	}
	return def
}

func envInt(name string, def int) int {
	if v, err := strconv.Atoi(os.Getenv(name)); err == nil {
		return v
	}
	return def
}

func serveMain(args []string) error {
	cfg := store.DefaultConfig()
	fs := flag.NewFlagSet("serve", flag.ExitOnError)
	fs.StringVar(&cfg.ReplicaURL, "replica-url", os.Getenv("REPLICA_URL"), "Litestream replica URL (gs://, s3://, or file://)")
	fs.StringVar(&cfg.Dir, "dir", env("DATA_DIR", filepath.Join(os.TempDir(), "cloudrun-sqlite")), "instance-local scratch directory")
	fs.BoolVar(&cfg.Durable, "durable", envBool("DURABLE", cfg.Durable), "acknowledge writes only after they are in object storage")
	fs.BoolVar(&cfg.Hydrate, "hydrate", envBool("HYDRATE", false), "download the whole database in the background")
	fs.IntVar(&cfg.CacheSize, "cache-size", envInt("CACHE_SIZE", cfg.CacheSize), "page cache size in bytes")
	fs.IntVar(&cfg.SnapshotPlanLen, "snapshot-plan-len", envInt("SNAPSHOT_PLAN_LEN", cfg.SnapshotPlanLen), "snapshot when a cold start would read more than this many files (0 disables)")
	fs.DurationVar(&cfg.PollInterval, "poll-interval", envDuration("POLL_INTERVAL", cfg.PollInterval), "how often to list the replica for compacted files or another instance's writes")
	port := fs.String("port", env("PORT", "8080"), "listen port")
	vfsLogLevel := slag.Level(slog.LevelWarn)
	if v := os.Getenv("VFS_LOG_LEVEL"); v != "" {
		if err := vfsLogLevel.Set(v); err != nil {
			return fmt.Errorf("VFS_LOG_LEVEL: %w", err)
		}
	}
	fs.Var(&vfsLogLevel, "vfs-log-level", "Litestream VFS log level")
	fs.Parse(args)
	if cfg.ReplicaURL == "" {
		return errors.New("set REPLICA_URL or -replica-url")
	}

	instance := instanceID()
	// gcp/init installed the process handler from LOG_LEVEL.
	log := slog.Default().With("instance", instance)
	slog.SetDefault(log)
	cfg.Logger = log
	cfg.VFSLogger = slog.New(minLevel{level: vfsLogLevel.Level(), next: log.Handler()})
	stopTel := observe.Start(context.Background(), cfg.Logger)
	defer func() {
		tctx, cancel := context.WithTimeout(context.Background(), 2*time.Second)
		defer cancel()
		if err := stopTel(tctx); err != nil {
			clog.Warn("telemetry shutdown", "error", err)
		}
	}()
	if err := os.MkdirAll(cfg.Dir, 0o755); err != nil {
		return err
	}

	ctx, stop := signal.NotifyContext(context.Background(), syscall.SIGTERM, os.Interrupt)
	defer stop()

	start := time.Now()
	st, err := store.Open(ctx, cfg)
	if err != nil {
		return err
	}
	if err := migrate(ctx, st); err != nil {
		st.Close()
		return err
	}
	clog.Info("database open", "open_ms", ms(time.Since(start)), "durable", cfg.Durable, "hydrate", cfg.Hydrate)

	srv := &http.Server{Handler: newServer(st, instance, start, os.Getenv("ADMIN_TOKEN")).routes()}
	ln, err := net.Listen("tcp", ":"+*port)
	if err != nil {
		st.Close()
		return err
	}
	go func() {
		if err := srv.Serve(ln); !errors.Is(err, http.ErrServerClosed) {
			clog.Error("serve", "error", err)
			stop()
		}
	}()
	clog.Info("listening", "port", *port, "startup_ms", ms(time.Since(start)))

	<-ctx.Done()
	// Cloud Run sends SIGTERM and kills the container 10 seconds later.
	clog.Info("shutting down")
	shutdownCtx, cancel := context.WithTimeout(context.Background(), 8*time.Second)
	defer cancel()
	if err := srv.Shutdown(shutdownCtx); err != nil {
		clog.Warn("http shutdown", "error", err)
	}
	if err := st.Close(); err != nil {
		clog.Error("close database", "error", err)
		return err
	}
	clog.Info("shut down cleanly")
	return nil
}

// minLevel drops records below level and forwards the rest to next.
type minLevel struct {
	level slog.Level
	next  slog.Handler
}

func (h minLevel) Enabled(ctx context.Context, level slog.Level) bool {
	return level >= h.level && h.next.Enabled(ctx, level)
}

func (h minLevel) Handle(ctx context.Context, r slog.Record) error {
	if r.Level < h.level {
		return nil
	}
	return h.next.Handle(ctx, r)
}

func (h minLevel) WithAttrs(attrs []slog.Attr) slog.Handler {
	return minLevel{level: h.level, next: h.next.WithAttrs(attrs)}
}

func (h minLevel) WithGroup(name string) slog.Handler {
	return minLevel{level: h.level, next: h.next.WithGroup(name)}
}

func instanceID() string {
	b := make([]byte, 4)
	rand.Read(b)
	if rev := os.Getenv("K_REVISION"); rev != "" {
		return rev + "-" + hex.EncodeToString(b)
	}
	return hex.EncodeToString(b)
}

func ms(d time.Duration) float64 {
	return float64(d.Microseconds()) / 1000
}

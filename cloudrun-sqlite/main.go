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
	logLevel := fs.String("log-level", env("LOG_LEVEL", "info"), "log level")
	vfsLogLevel := fs.String("vfs-log-level", env("VFS_LOG_LEVEL", "warn"), "Litestream VFS log level")
	fs.Parse(args)
	if cfg.ReplicaURL == "" {
		return errors.New("set REPLICA_URL or -replica-url")
	}

	instance := instanceID()
	cfg.Logger = newLogger(*logLevel).With("instance", instance)
	cfg.VFSLogger = newLogger(*vfsLogLevel).With("instance", instance)
	log := cfg.Logger
	slog.SetDefault(log)
	stopTel := observe.Start(context.Background(), log)
	defer func() {
		tctx, cancel := context.WithTimeout(context.Background(), 2*time.Second)
		defer cancel()
		if err := stopTel(tctx); err != nil {
			log.Warn("telemetry shutdown", "error", err)
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
	log.Info("database open", "open_ms", ms(time.Since(start)), "durable", cfg.Durable, "hydrate", cfg.Hydrate)

	srv := &http.Server{Handler: newServer(st, instance, start, os.Getenv("ADMIN_TOKEN")).routes()}
	ln, err := net.Listen("tcp", ":"+*port)
	if err != nil {
		st.Close()
		return err
	}
	go func() {
		if err := srv.Serve(ln); !errors.Is(err, http.ErrServerClosed) {
			log.Error("serve", "error", err)
			stop()
		}
	}()
	log.Info("listening", "port", *port, "startup_ms", ms(time.Since(start)))

	<-ctx.Done()
	// Cloud Run sends SIGTERM and kills the container 10 seconds later.
	log.Info("shutting down")
	shutdownCtx, cancel := context.WithTimeout(context.Background(), 8*time.Second)
	defer cancel()
	if err := srv.Shutdown(shutdownCtx); err != nil {
		log.Warn("http shutdown", "error", err)
	}
	if err := st.Close(); err != nil {
		log.Error("close database", "error", err)
		return err
	}
	log.Info("shut down cleanly")
	return nil
}

func newLogger(level string) *slog.Logger {
	var l slog.Level
	if err := l.UnmarshalText([]byte(level)); err != nil {
		l = slog.LevelInfo
	}
	opts := &slog.HandlerOptions{Level: l}
	if os.Getenv("K_SERVICE") != "" {
		return slog.New(slog.NewJSONHandler(os.Stderr, opts))
	}
	return slog.New(slog.NewTextHandler(os.Stderr, opts))
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

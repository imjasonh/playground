// Command cloudrun-sqlite serves a SQLite database whose only durable copy is
// a Litestream replica in Cloud Storage or S3. See README.md.
package main

import (
	"context"
	"crypto/rand"
	"encoding/hex"
	"errors"
	"flag"
	"log/slog"
	"net"
	"net/http"
	"os"
	"os/signal"
	"path/filepath"
	"syscall"
	"time"

	"github.com/chainguard-dev/clog"
	_ "github.com/chainguard-dev/clog/gcp/init"
	"github.com/imjasonh/playground/cloudrun-sqlite/internal/observe"
	"github.com/imjasonh/playground/cloudrun-sqlite/internal/store"
	"github.com/sethvargo/go-envconfig"
)

func main() {
	if len(os.Args) > 1 && os.Args[1] == "seed" {
		if err := seedMain(os.Args[2:]); err != nil {
			clog.Fatal("seed", "err", err)
		}
		return
	}
	if err := serveMain(os.Args[1:]); err != nil {
		clog.Fatal("serve", "err", err)
	}
}

// env is the server configuration, loaded once before main. The store
// defaults match store.DefaultConfig: durable writes, a 64 MiB cache, a
// snapshot after 16 files, and a 30s poll. An empty DATA_DIR falls back to
// a temp directory, which a tag cannot name.
var env = envconfig.MustProcess(context.Background(), &struct {
	ReplicaURL      string        `env:"REPLICA_URL"`
	Dir             string        `env:"DATA_DIR"`
	Durable         bool          `env:"DURABLE, default=true"`
	Hydrate         bool          `env:"HYDRATE"`
	CacheSize       int           `env:"CACHE_SIZE, default=67108864"`
	SnapshotPlanLen int           `env:"SNAPSHOT_PLAN_LEN, default=16"`
	PollInterval    time.Duration `env:"POLL_INTERVAL, default=30s"`
	Port            string        `env:"PORT, default=8080"`
	AdminToken      string        `env:"ADMIN_TOKEN"`
}{})

func serveMain(args []string) error {
	cfg := store.DefaultConfig()
	cfg.ReplicaURL = env.ReplicaURL
	cfg.Dir = env.Dir
	if cfg.Dir == "" {
		cfg.Dir = filepath.Join(os.TempDir(), "cloudrun-sqlite")
	}
	cfg.Durable = env.Durable
	cfg.Hydrate = env.Hydrate
	cfg.CacheSize = env.CacheSize
	cfg.SnapshotPlanLen = env.SnapshotPlanLen
	cfg.PollInterval = env.PollInterval

	fs := flag.NewFlagSet("serve", flag.ExitOnError)
	fs.StringVar(&cfg.ReplicaURL, "replica-url", cfg.ReplicaURL, "Litestream replica URL (gcs-grpc://, gs://, s3://, or file://)")
	fs.StringVar(&cfg.Dir, "dir", cfg.Dir, "instance-local scratch directory")
	fs.BoolVar(&cfg.Durable, "durable", cfg.Durable, "acknowledge writes only after they are in object storage")
	fs.BoolVar(&cfg.Hydrate, "hydrate", cfg.Hydrate, "download the whole database in the background")
	fs.IntVar(&cfg.CacheSize, "cache-size", cfg.CacheSize, "page cache size in bytes")
	fs.IntVar(&cfg.SnapshotPlanLen, "snapshot-plan-len", cfg.SnapshotPlanLen, "snapshot when a cold start would read more than this many files (0 disables)")
	fs.DurationVar(&cfg.PollInterval, "poll-interval", cfg.PollInterval, "how often to list the replica for compacted files or another instance's writes")
	port := fs.String("port", env.Port, "listen port")
	fs.Parse(args)
	if cfg.ReplicaURL == "" {
		return errors.New("set REPLICA_URL or -replica-url")
	}

	instance := instanceID()
	// gcp/init installed the process handler from LOG_LEVEL. The instance
	// id rides on the context, and on the default logger for code that
	// has no context.
	log := slog.Default().With("instance", instance)
	slog.SetDefault(log)
	ctx, stop := signal.NotifyContext(context.Background(), syscall.SIGTERM, os.Interrupt)
	defer stop()
	ctx = clog.WithLogger(ctx, clog.NewLogger(log))
	stopTel := observe.Start(ctx)
	defer func() {
		tctx, cancel := context.WithTimeout(context.Background(), 2*time.Second)
		defer cancel()
		if err := stopTel(tctx); err != nil {
			slog.Warn("telemetry shutdown", "error", err)
		}
	}()
	if err := os.MkdirAll(cfg.Dir, 0o755); err != nil {
		return err
	}

	start := time.Now()
	st, err := store.Open(ctx, cfg)
	if err != nil {
		return err
	}
	if err := migrate(ctx, st); err != nil {
		st.Close()
		return err
	}
	slog.Info("database open", "open_ms", ms(time.Since(start)), "durable", cfg.Durable, "hydrate", cfg.Hydrate)

	srv := &http.Server{Handler: newServer(st, instance, start, env.AdminToken).routes()}
	ln, err := net.Listen("tcp", ":"+*port)
	if err != nil {
		st.Close()
		return err
	}
	go func() {
		if err := srv.Serve(ln); !errors.Is(err, http.ErrServerClosed) {
			slog.Error("serve", "error", err)
			stop()
		}
	}()
	slog.Info("listening", "port", *port, "startup_ms", ms(time.Since(start)))

	<-ctx.Done()
	// Cloud Run sends SIGTERM and kills the container 10 seconds later.
	slog.Info("shutting down")
	shutdownCtx, cancel := context.WithTimeout(context.Background(), 8*time.Second)
	defer cancel()
	if err := srv.Shutdown(shutdownCtx); err != nil {
		slog.Warn("http shutdown", "error", err)
	}
	if err := st.Close(); err != nil {
		slog.Error("close database", "error", err)
		return err
	}
	slog.Info("shut down cleanly")
	return nil
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

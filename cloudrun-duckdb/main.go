// Command cloudrun-duckdb serves a DuckDB database whose only durable copy
// is in Cloud Storage. See README.md.
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
	"github.com/imjasonh/playground/cloudrun-duckdb/internal/fanout"
	"github.com/imjasonh/playground/cloudrun-duckdb/internal/store"
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
// defaults match store.DefaultConfig. An empty DATA_DIR falls back to a
// temp directory, which a tag cannot name.
var env = envconfig.MustProcess(context.Background(), &struct {
	ReplicaURL         string        `env:"REPLICA_URL"`
	Dir                string        `env:"DATA_DIR"`
	Durable            bool          `env:"DURABLE, default=true"`
	SnapshotMinEntries int           `env:"SNAPSHOT_MIN_ENTRIES, default=16"`
	SnapshotEntryCost  int64         `env:"SNAPSHOT_ENTRY_COST, default=262144"`
	PollInterval       time.Duration `env:"POLL_INTERVAL, default=30s"`
	MemoryLimit        string        `env:"DUCKDB_MEMORY_LIMIT, default=256MB"`
	Threads            int           `env:"DUCKDB_THREADS, default=2"`
	Port               string        `env:"PORT, default=8080"`
	AdminToken         string        `env:"ADMIN_TOKEN"`
	ReadOnly           bool          `env:"READ_ONLY"`
	WriterURL          string        `env:"WRITER_URL"`
}{})

func serveMain(args []string) error {
	cfg := store.DefaultConfig()
	cfg.ReplicaURL = env.ReplicaURL
	cfg.Dir = env.Dir
	if cfg.Dir == "" {
		cfg.Dir = filepath.Join(os.TempDir(), "cloudrun-duckdb")
	}
	cfg.Durable = env.Durable
	cfg.SnapshotMinEntries = env.SnapshotMinEntries
	cfg.SnapshotEntryCost = env.SnapshotEntryCost
	cfg.PollInterval = env.PollInterval
	cfg.MemoryLimit = env.MemoryLimit
	cfg.Threads = env.Threads
	cfg.ReadOnly = env.ReadOnly

	fs := flag.NewFlagSet("serve", flag.ExitOnError)
	fs.BoolVar(&cfg.ReadOnly, "read-only", cfg.ReadOnly, "serve reads from the replica and never write; open waits until a writer has created the database")
	writerURL := fs.String("writer-url", env.WriterURL, "writer's URL, for the read-only page's link")
	fs.StringVar(&cfg.ReplicaURL, "replica-url", cfg.ReplicaURL, "replica URL (gs:// or file://)")
	fs.StringVar(&cfg.Dir, "dir", cfg.Dir, "instance-local directory for the database file and its WAL")
	fs.BoolVar(&cfg.Durable, "durable", cfg.Durable, "acknowledge writes only after they are in object storage")
	fs.IntVar(&cfg.SnapshotMinEntries, "snapshot-min-entries", cfg.SnapshotMinEntries, "fewest log entries after a base before uploading a new one (0 disables)")
	fs.DurationVar(&cfg.PollInterval, "poll-interval", cfg.PollInterval, "how often a read-only replica lists the replica for new commits")
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

	start := time.Now()
	st, err := store.Open(ctx, cfg)
	if err != nil {
		return err
	}
	if !cfg.ReadOnly {
		if err := migrate(ctx, st); err != nil {
			st.Close()
			return err
		}
	}
	live := fanout.New()
	slog.Info("database open", "open_ms", ms(time.Since(start)), "read_only", cfg.ReadOnly, "durable", cfg.Durable)

	s := newServer(st, live, instance, start, env.AdminToken)
	s.readOnly, s.writerURL, s.pollInterval = cfg.ReadOnly, *writerURL, cfg.PollInterval
	if cfg.ReadOnly {
		go s.followReplica(ctx)
	}
	srv := &http.Server{Handler: s.routes()}
	ln, err := net.Listen("tcp", ":"+*port)
	if err != nil {
		live.Close()
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
	live.Close()
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

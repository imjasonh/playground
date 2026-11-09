package main

import (
	"context"
	"database/sql"
	"errors"
	"flag"
	"fmt"
	"log/slog"
	"os"
	"time"

	"github.com/imjasonh/playground/cloudrun-duckdb/internal/store"
)

// seedMain builds a database of the requested size and uploads it as one
// base, the shape a long-lived replica has right after a snapshot.
func seedMain(args []string) error {
	fs := flag.NewFlagSet("seed", flag.ExitOnError)
	replicaURL := fs.String("replica-url", os.Getenv("REPLICA_URL"), "replica URL")
	rows := fs.Int("rows", 10000, "rows to insert into items")
	rowSize := fs.Int("row-size", 1000, "bytes per row")
	force := fs.Bool("force", false, "delete an existing replica first")
	fs.Parse(args)
	if *replicaURL == "" {
		return errors.New("set REPLICA_URL or -replica-url")
	}
	dir, err := os.MkdirTemp("", "seed-*")
	if err != nil {
		return err
	}
	defer os.RemoveAll(dir)
	cfg := store.DefaultConfig()
	cfg.ReplicaURL, cfg.Dir, cfg.MemoryLimit, cfg.Threads = *replicaURL, dir, "", 0

	start := time.Now()
	res, err := store.Seed(context.Background(), cfg, *force, func(ctx context.Context, db *sql.DB) error {
		return fill(ctx, db, *rows, *rowSize)
	})
	if err != nil {
		return err
	}
	slog.Info("seeded replica", "rows", *rows, "bytes", res.Bytes, "upload_ms", res.Millis, "duration", time.Since(start).Round(time.Millisecond))
	return nil
}

// fill creates the server's tables and inserts rows of random hex, the
// same data cloudrun-sqlite's seed writes. DuckDB compresses hex strings,
// so the same rows take less space than in SQLite.
func fill(ctx context.Context, db *sql.DB, rows, rowSize int) error {
	chunks := (rowSize + 31) / 32
	_, err := db.ExecContext(ctx, fmt.Sprintf(`
		CREATE TABLE counters (name VARCHAR PRIMARY KEY, n BIGINT NOT NULL);
		CREATE SEQUENCE items_id START %d;
		CREATE TABLE items (id BIGINT PRIMARY KEY DEFAULT nextval('items_id'), body VARCHAR NOT NULL);
		INSERT INTO items
			SELECT i, array_to_string(list_transform(range(%d), lambda x: md5(random()::VARCHAR)), '')[1:%d]
			FROM range(1, %d) t(i);
	`, rows+1, chunks, rowSize, rows+1))
	return err
}

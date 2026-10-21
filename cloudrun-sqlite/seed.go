package main

import (
	"context"
	"crypto/rand"
	"database/sql"
	"encoding/hex"
	"errors"
	"flag"
	"fmt"
	"io"
	"log/slog"
	"os"
	"path/filepath"
	"time"

	"github.com/benbjohnson/litestream"
	_ "github.com/benbjohnson/litestream/file"
	_ "github.com/benbjohnson/litestream/gs"
	_ "github.com/benbjohnson/litestream/s3"
	"github.com/superfly/ltx"
)

// seedMain builds a database of the requested size with plain SQLite, then
// uploads it as a single snapshot, the shape a long-lived replica has after
// compaction.
func seedMain(args []string) error {
	fs := flag.NewFlagSet("seed", flag.ExitOnError)
	replicaURL := fs.String("replica-url", os.Getenv("REPLICA_URL"), "Litestream replica URL")
	rows := fs.Int("rows", 10000, "rows to insert into items")
	rowSize := fs.Int("row-size", 1000, "bytes per row")
	force := fs.Bool("force", false, "delete an existing replica first")
	fs.Parse(args)
	if *replicaURL == "" {
		return errors.New("set REPLICA_URL or -replica-url")
	}
	ctx := context.Background()

	client, err := litestream.NewReplicaClientFromURL(*replicaURL)
	if err != nil {
		return err
	}
	if err := client.Init(ctx); err != nil {
		return err
	}
	if plan, err := litestream.CalcRestorePlan(ctx, client, 0, time.Time{}, discardLogger()); err == nil && len(plan) > 0 {
		if !*force {
			return fmt.Errorf("%s already has a database; pass -force to replace it", *replicaURL)
		}
		if err := client.DeleteAll(ctx); err != nil {
			return fmt.Errorf("delete existing replica: %w", err)
		}
	}

	dir, err := os.MkdirTemp("", "seed-*")
	if err != nil {
		return err
	}
	defer os.RemoveAll(dir)
	path := filepath.Join(dir, "seed.db")

	start := time.Now()
	if err := buildDB(path, *rows, *rowSize); err != nil {
		return err
	}
	fi, err := os.Stat(path)
	if err != nil {
		return err
	}
	slog.Info("built database", "rows", *rows, "bytes", fi.Size(), "duration", time.Since(start).Round(time.Millisecond))

	start = time.Now()
	f, err := os.Open(path)
	if err != nil {
		return err
	}
	defer f.Close()
	pr, pw := io.Pipe()
	go func() { pw.CloseWithError(encodeSnapshot(pw, f, fi.Size())) }()
	info, err := client.WriteLTXFile(ctx, litestream.SnapshotLevel, 1, 1, pr)
	pr.CloseWithError(err)
	if err != nil {
		return fmt.Errorf("upload snapshot: %w", err)
	}
	slog.Info("uploaded snapshot", "bytes", info.Size, "duration", time.Since(start).Round(time.Millisecond))
	return nil
}

func buildDB(path string, rows, rowSize int) error {
	db, err := sql.Open("sqlite3", path)
	if err != nil {
		return err
	}
	defer db.Close()
	if _, err := db.Exec(`
		CREATE TABLE counters (name TEXT PRIMARY KEY, n INTEGER NOT NULL);
		CREATE TABLE items (id INTEGER PRIMARY KEY, body TEXT NOT NULL);
	`); err != nil {
		return err
	}
	tx, err := db.Begin()
	if err != nil {
		return err
	}
	stmt, err := tx.Prepare("INSERT INTO items (id, body) VALUES (?, ?)")
	if err != nil {
		return err
	}
	buf := make([]byte, (rowSize+1)/2)
	for i := 1; i <= rows; i++ {
		rand.Read(buf)
		if _, err := stmt.Exec(i, hex.EncodeToString(buf)[:rowSize]); err != nil {
			return err
		}
	}
	if err := stmt.Close(); err != nil {
		return err
	}
	return tx.Commit()
}

func discardLogger() *slog.Logger { return slog.New(slog.DiscardHandler) }

// encodeSnapshot writes a SQLite database file as an LTX snapshot at TXID 1.
func encodeSnapshot(w io.Writer, r io.Reader, size int64) error {
	hdr := make([]byte, 100)
	if _, err := io.ReadFull(r, hdr); err != nil {
		return err
	}
	pageSize := uint32(hdr[16])<<8 | uint32(hdr[17])
	if pageSize == 1 {
		pageSize = 65536
	}
	commit := uint32(size / int64(pageSize))

	enc, err := ltx.NewEncoder(w)
	if err != nil {
		return err
	}
	if err := enc.EncodeHeader(ltx.Header{
		Version:   ltx.Version,
		Flags:     ltx.HeaderFlagNoChecksum,
		PageSize:  pageSize,
		Commit:    commit,
		MinTXID:   1,
		MaxTXID:   1,
		Timestamp: time.Now().UnixMilli(),
	}); err != nil {
		return err
	}
	page := make([]byte, pageSize)
	copy(page, hdr)
	if _, err := io.ReadFull(r, page[len(hdr):]); err != nil {
		return err
	}
	lockPgno := ltx.LockPgno(pageSize)
	for pgno := uint32(1); pgno <= commit; pgno++ {
		if pgno > 1 {
			if _, err := io.ReadFull(r, page); err != nil {
				return err
			}
		}
		if pgno == lockPgno {
			continue
		}
		if err := enc.EncodePage(ltx.PageHeader{Pgno: pgno}, page); err != nil {
			return err
		}
	}
	return enc.Close()
}

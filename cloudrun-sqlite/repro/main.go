//go:build vfs

// Command repro checks a Litestream version for
// https://github.com/benbjohnson/litestream/issues/1018: it writes through
// the write-enabled VFS for a while, then checks the database in the same
// process and from a fresh read-only VFS.
package main

import (
	"context"
	"database/sql"
	"flag"
	"fmt"
	"log/slog"
	"os"
	"sync"
	"sync/atomic"
	"time"

	"github.com/benbjohnson/litestream"
	_ "github.com/benbjohnson/litestream/file"
	_ "github.com/benbjohnson/litestream/gs"
	_ "github.com/benbjohnson/litestream/s3"
	_ "github.com/mattn/go-sqlite3"
	"github.com/psanford/sqlite3vfs"
)

func main() {
	replicaURL := flag.String("replica-url", "", "replica URL (file:///path, s3://bucket/path, gs://bucket/path)")
	duration := flag.Duration("duration", 30*time.Second, "how long to write")
	writers := flag.Int("c", 1, "concurrent writers")
	syncInterval := flag.Duration("sync-interval", time.Second, "VFS WriteSyncInterval")
	pollInterval := flag.Duration("poll-interval", time.Second, "VFS PollInterval")
	compaction := flag.Bool("compaction", false, "enable VFS compaction (L1 every 5s, L2 every 20s)")
	flag.Parse()
	if *replicaURL == "" {
		fmt.Fprintln(os.Stderr, "usage: repro -replica-url URL [flags]")
		os.Exit(2)
	}
	logger := slog.New(slog.NewTextHandler(os.Stderr, &slog.HandlerOptions{Level: slog.LevelWarn}))

	client, err := litestream.NewReplicaClientFromURL(*replicaURL)
	check(err)
	check(client.Init(context.Background()))

	vfs := litestream.NewVFS(client, logger)
	vfs.PollInterval = *pollInterval
	vfs.WriteEnabled = true
	vfs.WriteSyncInterval = *syncInterval
	if *compaction {
		vfs.CompactionEnabled = true
		vfs.CompactionLevels = litestream.CompactionLevels{
			{Level: 0},
			{Level: 1, Interval: 5 * time.Second},
			{Level: 2, Interval: 20 * time.Second},
		}
	}
	check(sqlite3vfs.RegisterVFS("litestream", vfs))
	db, err := sql.Open("sqlite3", "file:db?vfs=litestream&_busy_timeout=5000")
	check(err)
	db.SetMaxOpenConns(1)
	_, err = db.Exec("CREATE TABLE IF NOT EXISTS t (id INTEGER PRIMARY KEY, ms INTEGER, pad TEXT)")
	check(err)
	var initial int
	check(db.QueryRow("SELECT count(*) FROM t").Scan(&initial))

	// Each operation is an insert followed by a count(*), which reads every
	// page while syncs upload.
	var ok, failed atomic.Int64
	var firstErr atomic.Value
	start := time.Now()
	ctx, cancel := context.WithTimeout(context.Background(), *duration)
	defer cancel()
	var wg sync.WaitGroup
	for range *writers {
		wg.Go(func() {
			for ctx.Err() == nil {
				_, err := db.Exec("INSERT INTO t (ms, pad) VALUES (unixepoch('now','subsec')*1000, printf('%.200c', 'x'))")
				if err == nil {
					var n int
					err = db.QueryRow("SELECT count(*) FROM t").Scan(&n)
				}
				if err != nil {
					failed.Add(1)
					firstErr.CompareAndSwap(nil, fmt.Sprintf("after %s: %v", time.Since(start).Round(time.Millisecond), err))
					time.Sleep(10 * time.Millisecond)
					continue
				}
				ok.Add(1)
			}
		})
	}
	wg.Wait()

	integrity := scalar(db, "PRAGMA integrity_check")
	db.Close()
	fmt.Printf("writes: %d ok, %d failed\n", ok.Load(), failed.Load())
	if v := firstErr.Load(); v != nil {
		fmt.Printf("first error %s\n", v)
	}
	fmt.Printf("integrity_check in the writer: %s\n", integrity)

	// What a new instance would see.
	reader := litestream.NewVFS(client, logger)
	check(sqlite3vfs.RegisterVFS("litestream-reader", reader))
	rdb, err := sql.Open("sqlite3", "file:db?vfs=litestream-reader&mode=ro")
	check(err)
	defer rdb.Close()
	fresh := scalar(rdb, "PRAGMA integrity_check")
	var count int
	countErr := rdb.QueryRow("SELECT count(*) FROM t").Scan(&count)
	want := initial + int(ok.Load())
	fmt.Printf("integrity_check from a fresh VFS: %s\n", fresh)
	fmt.Printf("rows from a fresh VFS: %d (error %v); acknowledged: %d\n", count, countErr, want)

	if failed.Load() > 0 || integrity != "ok" || fresh != "ok" || countErr != nil || count < want {
		fmt.Println("FAIL")
		os.Exit(1)
	}
	fmt.Println("PASS")
}

func scalar(db *sql.DB, q string) string {
	var s string
	if err := db.QueryRow(q).Scan(&s); err != nil {
		return "error: " + err.Error()
	}
	return s
}

func check(err error) {
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(2)
	}
}

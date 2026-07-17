//go:build vfs

// Command litestream-tenants runs local experiments for multi-tenant SQLite
// with Litestream (file replica standing in for GCS): cold open (VFS vs
// restore), single-writer + many readers, multi-writer conflicts, on-demand
// tenant fan-out, and sharded writers.
package main

import (
	"context"
	"flag"
	"fmt"
	"os"
	"path/filepath"
	"strconv"
	"time"
)

func main() {
	if len(os.Args) < 2 {
		usage()
		os.Exit(2)
	}
	cmd := os.Args[1]
	args := os.Args[2:]
	ctx := context.Background()

	switch cmd {
	case "cold-open":
		os.Exit(runColdOpen(ctx, args))
	case "rw":
		os.Exit(runRW(ctx, args))
	case "conflict":
		os.Exit(runConflict(ctx, args))
	case "fanout":
		os.Exit(runFanout(ctx, args))
	case "shard":
		os.Exit(runShard(ctx, args))
	case "all":
		os.Exit(runAll(ctx, args))
	case "help", "-h", "--help":
		usage()
	default:
		fmt.Fprintf(os.Stderr, "unknown command %q\n", cmd)
		usage()
		os.Exit(2)
	}
}

func usage() {
	fmt.Fprintf(os.Stderr, `litestream-tenants — local Litestream multi-tenant benches

Requires CGO and: go run -tags vfs .

Commands:
  cold-open   Compare full restore vs VFS open for seeded tenant sizes
  rw          Single writer + N readers RPS/latency on one tenant
  conflict    Two VFS writers on one tenant (expect conflicts)
  fanout      Many tenants via LRU pool (on-demand open, no boot restore)
  shard       Hash tenants onto K exclusive writer shards
  all         Run a small default suite into a temp dir

Common flags (per command):
  -dir DIR          Workspace (default: temp dir)
  -rows N           Rows per tenant when seeding (default varies)
  -payload N        Blob bytes per row (default 256)
  -tenants N        Number of tenants (default varies)
  -duration D       Load duration (default 3s)
`)
}

type commonFlags struct {
	dir      string
	rows     int
	payload  int
	tenants  int
	duration time.Duration
	readers  int
	capacity int
	shards   int
	mode     string
	rounds   int
}

func parseCommon(args []string, defaults commonFlags) *commonFlags {
	fs := flag.NewFlagSet(os.Args[1], flag.ExitOnError)
	cfg := defaults
	fs.StringVar(&cfg.dir, "dir", cfg.dir, "workspace directory")
	fs.IntVar(&cfg.rows, "rows", cfg.rows, "rows per tenant")
	fs.IntVar(&cfg.payload, "payload", cfg.payload, "payload bytes per row")
	fs.IntVar(&cfg.tenants, "tenants", cfg.tenants, "tenant count")
	fs.DurationVar(&cfg.duration, "duration", cfg.duration, "load duration")
	fs.IntVar(&cfg.readers, "readers", cfg.readers, "reader goroutines")
	fs.IntVar(&cfg.capacity, "capacity", cfg.capacity, "LRU pool capacity")
	fs.IntVar(&cfg.shards, "shards", cfg.shards, "writer shard count")
	fs.StringVar(&cfg.mode, "mode", cfg.mode, "open mode: local|vfs-write|vfs-read|restore")
	fs.IntVar(&cfg.rounds, "rounds", cfg.rounds, "fanout rounds")
	_ = fs.Parse(args)
	return &cfg
}

func prepareHarness(cfg *commonFlags) (*Harness, []string, error) {
	dir := cfg.dir
	var err error
	if dir == "" {
		dir, err = os.MkdirTemp("", "litestream-tenants-*")
		if err != nil {
			return nil, nil, err
		}
		fmt.Println("workspace:", dir)
	} else {
		dir, err = filepath.Abs(dir)
		if err != nil {
			return nil, nil, err
		}
		if err := os.MkdirAll(dir, 0o755); err != nil {
			return nil, nil, err
		}
	}
	h, err := NewHarness(dir)
	if err != nil {
		return nil, nil, err
	}
	tenants := make([]string, cfg.tenants)
	ctx := context.Background()
	for i := 0; i < cfg.tenants; i++ {
		name := fmt.Sprintf("t%02d", i)
		tenants[i] = name
		size, err := h.SeedTenant(ctx, name, cfg.rows, cfg.payload)
		if err != nil {
			return nil, nil, fmt.Errorf("seed %s: %w", name, err)
		}
		fmt.Printf("seeded %s rows=%d size=%s\n", name, cfg.rows, humanBytes(size))
	}
	return h, tenants, nil
}

func runColdOpen(ctx context.Context, args []string) int {
	cfg := parseCommon(args, commonFlags{tenants: 3, rows: 2000, payload: 1024})
	dir := cfg.dir
	if dir == "" {
		var err error
		dir, err = os.MkdirTemp("", "litestream-tenants-*")
		if err != nil {
			fmt.Fprintln(os.Stderr, err)
			return 1
		}
		fmt.Println("workspace:", dir)
	}
	h, err := NewHarness(dir)
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		return 1
	}
	sizes := []struct {
		name string
		rows int
		pay  int
	}{
		{"tiny", 100, 64},
		{"medium", cfg.rows, cfg.payload},
		{"large", cfg.rows * 10, cfg.payload},
	}
	var tenants []string
	for _, s := range sizes {
		sz, err := h.SeedTenant(ctx, s.name, s.rows, s.pay)
		if err != nil {
			fmt.Fprintln(os.Stderr, err)
			return 1
		}
		fmt.Printf("seeded %s rows=%d size=%s\n", s.name, s.rows, humanBytes(sz))
		tenants = append(tenants, s.name)
	}
	if _, err := BenchColdOpen(ctx, h, tenants); err != nil {
		fmt.Fprintln(os.Stderr, err)
		return 1
	}
	return 0
}

func runRW(ctx context.Context, args []string) int {
	cfg := parseCommon(args, commonFlags{
		tenants: 1, rows: 1000, payload: 256,
		readers: 32, duration: 3 * time.Second, mode: string(ModeLocal),
	})
	h, tenants, err := prepareHarness(cfg)
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		return 1
	}
	mode := OpenMode(cfg.mode)
	if _, _, err := BenchRW(ctx, h, tenants[0], mode, cfg.readers, cfg.duration); err != nil {
		fmt.Fprintln(os.Stderr, err)
		return 1
	}
	return 0
}

func runConflict(ctx context.Context, args []string) int {
	cfg := parseCommon(args, commonFlags{
		tenants: 1, rows: 500, payload: 128, duration: 2 * time.Second,
	})
	h, tenants, err := prepareHarness(cfg)
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		return 1
	}
	if _, err := BenchConflict(ctx, h, tenants[0], cfg.duration); err != nil {
		fmt.Fprintln(os.Stderr, err)
		return 1
	}
	fmt.Fprintln(os.Stderr, "note: dual-writer races often appear in Litestream logs (conflict detected / LTX rename), not as SQL errors")
	return 0
}

func runFanout(ctx context.Context, args []string) int {
	cfg := parseCommon(args, commonFlags{
		tenants: 20, rows: 200, payload: 256,
		capacity: 4, rounds: 3, mode: string(ModeVFSWrite),
	})
	h, tenants, err := prepareHarness(cfg)
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		return 1
	}
	if _, err := BenchFanout(ctx, h, tenants, OpenMode(cfg.mode), cfg.capacity, cfg.rounds); err != nil {
		fmt.Fprintln(os.Stderr, err)
		return 1
	}
	return 0
}

func runShard(ctx context.Context, args []string) int {
	cfg := parseCommon(args, commonFlags{
		tenants: 12, rows: 200, payload: 128,
		shards: 3, duration: 3 * time.Second, mode: string(ModeLocal),
	})
	h, tenants, err := prepareHarness(cfg)
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		return 1
	}
	if _, err := BenchShard(ctx, h, tenants, cfg.shards, OpenMode(cfg.mode), cfg.duration); err != nil {
		fmt.Fprintln(os.Stderr, err)
		return 1
	}
	return 0
}

func runAll(ctx context.Context, args []string) int {
	cfg := parseCommon(args, commonFlags{})
	dir := cfg.dir
	if dir == "" {
		var err error
		dir, err = os.MkdirTemp("", "litestream-tenants-all-*")
		if err != nil {
			fmt.Fprintln(os.Stderr, err)
			return 1
		}
	}
	fmt.Println("=== cold-open ===")
	if code := runColdOpen(ctx, []string{"-dir", filepath.Join(dir, "cold")}); code != 0 {
		return code
	}
	fmt.Println("=== rw local ===")
	if code := runRW(ctx, []string{"-dir", filepath.Join(dir, "rw-local"), "-mode", "local", "-duration", "2s", "-readers", "16"}); code != 0 {
		return code
	}
	fmt.Println("=== rw vfs-write ===")
	if code := runRW(ctx, []string{"-dir", filepath.Join(dir, "rw-vfs"), "-mode", "vfs-write", "-duration", "2s", "-readers", "8"}); code != 0 {
		return code
	}
	fmt.Println("=== conflict ===")
	if code := runConflict(ctx, []string{"-dir", filepath.Join(dir, "conflict"), "-duration", "2s"}); code != 0 {
		return code
	}
	fmt.Println("=== fanout ===")
	if code := runFanout(ctx, []string{"-dir", filepath.Join(dir, "fanout"), "-tenants", "10", "-capacity", "3", "-rounds", "2"}); code != 0 {
		return code
	}
	fmt.Println("=== shard ===")
	if code := runShard(ctx, []string{"-dir", filepath.Join(dir, "shard"), "-tenants", "9", "-shards", "3", "-duration", "2s"}); code != 0 {
		return code
	}
	fmt.Println("all benches complete in", dir)
	return 0
}

func humanBytes(n int64) string {
	const unit = 1024
	if n < unit {
		return strconv.FormatInt(n, 10) + "B"
	}
	div, exp := int64(unit), 0
	for v := n / unit; v >= unit; v /= unit {
		div *= unit
		exp++
	}
	return fmt.Sprintf("%.1f%ciB", float64(n)/float64(div), "KMGTPE"[exp])
}

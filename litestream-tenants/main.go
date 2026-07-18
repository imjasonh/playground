//go:build vfs

// Command litestream-tenants benchmarks a GitHub-like split:
//   control.db  — tenants/users/orgs/repos/ACL (rarely written)
//   repo-*.db   — PRs/comments/checks per repo
// Every repo API op performs a control-plane AuthorizeRepo lookup first.
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
	case "api":
		os.Exit(runAPI(ctx, args))
	case "cold-open":
		os.Exit(runColdOpen(ctx, args))
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
	fmt.Fprintf(os.Stderr, `litestream-tenants — control.db + per-repo SQLite / Litestream benches

Requires CGO: go run -tags vfs .

Commands:
  api         QPS for control R/W and repo R/W (each repo op does ACL lookup)
  cold-open   Restore vs VFS open for a seeded repo DB
  all         Small default suite

Flags (api / shared):
  -dir DIR           Workspace (default: temp)
  -mode MODE         local|vfs-write|vfs-read (default local)
  -duration D        Load duration (default 3s)
  -tenants N         Tenants / orgs (default 2)
  -users N           Users (default 20)
  -repos-per-tenant N
  -prs N             PRs per repo
  -comments N        Comments per PR
  -checks N          Check runs per PR
  -body N            Body bytes for PR/comment text
  -readers N         Repo-read+ACL goroutines
  -writers N         Repo-write+ACL goroutines
  -control-readers N ACL-only goroutines
  -control-writers N Control-write goroutines
  -repo-lru N        Hot repo DB LRU capacity
`)
}

type flags struct {
	dir            string
	mode           string
	duration       time.Duration
	tenants        int
	users          int
	reposPerTenant int
	prs            int
	comments       int
	checks         int
	body           int
	readers        int
	writers        int
	controlReaders int
	controlWriters int
	repoLRU        int
}

func parseFlags(args []string, def flags) *flags {
	fs := flag.NewFlagSet(os.Args[1], flag.ExitOnError)
	cfg := def
	fs.StringVar(&cfg.dir, "dir", cfg.dir, "workspace")
	fs.StringVar(&cfg.mode, "mode", cfg.mode, "open mode")
	fs.DurationVar(&cfg.duration, "duration", cfg.duration, "duration")
	fs.IntVar(&cfg.tenants, "tenants", cfg.tenants, "tenants")
	fs.IntVar(&cfg.users, "users", cfg.users, "users")
	fs.IntVar(&cfg.reposPerTenant, "repos-per-tenant", cfg.reposPerTenant, "repos per tenant")
	fs.IntVar(&cfg.prs, "prs", cfg.prs, "PRs per repo")
	fs.IntVar(&cfg.comments, "comments", cfg.comments, "comments per PR")
	fs.IntVar(&cfg.checks, "checks", cfg.checks, "checks per PR")
	fs.IntVar(&cfg.body, "body", cfg.body, "body bytes")
	fs.IntVar(&cfg.readers, "readers", cfg.readers, "repo readers")
	fs.IntVar(&cfg.writers, "writers", cfg.writers, "repo writers")
	fs.IntVar(&cfg.controlReaders, "control-readers", cfg.controlReaders, "control readers")
	fs.IntVar(&cfg.controlWriters, "control-writers", cfg.controlWriters, "control writers")
	fs.IntVar(&cfg.repoLRU, "repo-lru", cfg.repoLRU, "repo LRU")
	_ = fs.Parse(args)
	return &cfg
}

func workspace(dir string) (string, error) {
	if dir == "" {
		return os.MkdirTemp("", "litestream-tenants-*")
	}
	abs, err := filepath.Abs(dir)
	if err != nil {
		return "", err
	}
	return abs, os.MkdirAll(abs, 0o755)
}

func worldFromFlags(ctx context.Context, cfg *flags) (*World, error) {
	dir, err := workspace(cfg.dir)
	if err != nil {
		return nil, err
	}
	fmt.Println("workspace:", dir)
	h, err := NewHarness(dir)
	if err != nil {
		return nil, err
	}
	return SeedWorld(ctx, h, WorldConfig{
		Tenants:       cfg.tenants,
		Users:         cfg.users,
		ReposPerTenant: cfg.reposPerTenant,
		PRsPerRepo:    cfg.prs,
		CommentsPerPR: cfg.comments,
		ChecksPerPR:   cfg.checks,
		BodyBytes:     cfg.body,
	})
}

func runAPI(ctx context.Context, args []string) int {
	cfg := parseFlags(args, flags{
		mode: string(ModeLocal), duration: 3 * time.Second,
		tenants: 2, users: 20, reposPerTenant: 3,
		prs: 100, comments: 8, checks: 15, body: 256,
		readers: 16, writers: 4, controlReaders: 8, controlWriters: 1,
		repoLRU: 8,
	})
	w, err := worldFromFlags(ctx, cfg)
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		return 1
	}
	_, err = BenchAPI(ctx, w, APIBenchConfig{
		Mode:     OpenMode(cfg.mode),
		Duration: cfg.duration,
		Readers:  cfg.readers,
		Writers:  cfg.writers,
		ControlR: cfg.controlReaders,
		ControlW: cfg.controlWriters,
		RepoLRU:  cfg.repoLRU,
	})
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		return 1
	}
	return 0
}

func runColdOpen(ctx context.Context, args []string) int {
	cfg := parseFlags(args, flags{
		tenants: 1, users: 5, reposPerTenant: 1,
		prs: 500, comments: 10, checks: 20, body: 512,
	})
	w, err := worldFromFlags(ctx, cfg)
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		return 1
	}
	if err := BenchRepoColdOpen(ctx, w); err != nil {
		fmt.Fprintln(os.Stderr, err)
		return 1
	}
	return 0
}

func runAll(ctx context.Context, args []string) int {
	cfg := parseFlags(args, flags{})
	base, err := workspace(cfg.dir)
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		return 1
	}
	fmt.Println("=== api local ===")
	if code := runAPI(ctx, []string{
		"-dir", filepath.Join(base, "api-local"),
		"-mode", "local", "-duration", "2s",
		"-tenants", "2", "-repos-per-tenant", "2", "-users", "10",
		"-prs", "50", "-readers", "12", "-writers", "3",
		"-control-readers", "6", "-control-writers", "1", "-repo-lru", "4",
	}); code != 0 {
		return code
	}
	fmt.Println("=== api vfs-write ===")
	if code := runAPI(ctx, []string{
		"-dir", filepath.Join(base, "api-vfs"),
		"-mode", "vfs-write", "-duration", "2s",
		"-tenants", "1", "-repos-per-tenant", "2", "-users", "8",
		"-prs", "30", "-readers", "4", "-writers", "1",
		"-control-readers", "2", "-control-writers", "0", "-repo-lru", "2",
	}); code != 0 {
		return code
	}
	fmt.Println("=== cold-open ===")
	if code := runColdOpen(ctx, []string{"-dir", filepath.Join(base, "cold"), "-prs", "200"}); code != 0 {
		return code
	}
	fmt.Println("all benches complete in", base)
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

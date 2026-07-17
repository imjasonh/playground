//go:build vfs

package main

import (
	"context"
	"path/filepath"
	"testing"
	"time"
)

func TestSeedAndVFSRead(t *testing.T) {
	ctx := context.Background()
	h, err := NewHarness(t.TempDir())
	if err != nil {
		t.Fatal(err)
	}
	size, err := h.SeedTenant(ctx, "alpha", 50, 128)
	if err != nil {
		t.Fatal(err)
	}
	if size <= 0 {
		t.Fatalf("expected positive db size, got %d", size)
	}

	tdb, openDur, err := h.OpenTenant(ctx, "alpha", ModeVFSRead)
	if err != nil {
		t.Fatal(err)
	}
	defer tdb.Close()
	n, err := countRows(ctx, tdb.DB)
	if err != nil {
		t.Fatal(err)
	}
	if n != 50 {
		t.Fatalf("got %d rows, want 50", n)
	}
	t.Logf("vfs-read open+count ok in %s", openDur)
}

func TestColdOpenVFSvsRestore(t *testing.T) {
	ctx := context.Background()
	h, err := NewHarness(t.TempDir())
	if err != nil {
		t.Fatal(err)
	}
	if _, err := h.SeedTenant(ctx, "tiny", 200, 256); err != nil {
		t.Fatal(err)
	}
	if _, err := h.SeedTenant(ctx, "big", 5000, 512); err != nil {
		t.Fatal(err)
	}

	reports, err := BenchColdOpen(ctx, h, []string{"tiny", "big"})
	if err != nil {
		t.Fatal(err)
	}
	if len(reports) != 4 {
		t.Fatalf("expected 4 reports, got %d", len(reports))
	}
	for _, r := range reports {
		if r.OK == 0 {
			t.Fatalf("%s: expected success, got %#v", r.Label, r)
		}
	}

	// For the larger DB, VFS open+query should not be much slower than restore
	// in this local file-backed setup; more importantly restore copies bytes
	// while VFS does not grow RestoreDir.
	entries, _ := filepath.Glob(filepath.Join(h.RestoreDir, "*"))
	t.Logf("restore dir entries after bench: %d", len(entries))
}

func TestRWLocal(t *testing.T) {
	ctx := context.Background()
	h, err := NewHarness(t.TempDir())
	if err != nil {
		t.Fatal(err)
	}
	if _, err := h.SeedTenant(ctx, "t0", 100, 64); err != nil {
		t.Fatal(err)
	}
	w, r, err := BenchRW(ctx, h, "t0", ModeLocal, 8, 500*time.Millisecond)
	if err != nil {
		t.Fatal(err)
	}
	if w.OK == 0 {
		t.Fatalf("expected writes: %#v", w)
	}
	if r.OK == 0 {
		t.Fatalf("expected reads: %#v", r)
	}
	t.Log(w)
	t.Log(r)
}

func TestConflictDualWriters(t *testing.T) {
	ctx := context.Background()
	h, err := NewHarness(t.TempDir())
	if err != nil {
		t.Fatal(err)
	}
	if _, err := h.SeedTenant(ctx, "t0", 50, 64); err != nil {
		t.Fatal(err)
	}
	r, err := BenchConflict(ctx, h, "t0", 1500*time.Millisecond)
	if err != nil {
		t.Fatal(err)
	}
	t.Log(r)
	// Timing-dependent: at least one of conflict/error/busy should show up, or
	// some writes succeeded on both — we only assert the bench ran.
	if r.OK+r.Errors == 0 {
		t.Fatal("expected some write attempts")
	}
}

func TestFanoutOnDemand(t *testing.T) {
	ctx := context.Background()
	h, err := NewHarness(t.TempDir())
	if err != nil {
		t.Fatal(err)
	}
	tenants := []string{"a", "b", "c"}
	for _, name := range tenants {
		if _, err := h.SeedTenant(ctx, name, 40, 64); err != nil {
			t.Fatal(err)
		}
	}
	// capacity >= tenants so round 2+ should hit the LRU cache.
	r, err := BenchFanout(ctx, h, tenants, ModeVFSWrite, 3, 3)
	if err != nil {
		t.Fatal(err)
	}
	if r.OK == 0 {
		t.Fatalf("expected fanout successes: %#v", r)
	}
}

func TestShardWriters(t *testing.T) {
	ctx := context.Background()
	h, err := NewHarness(t.TempDir())
	if err != nil {
		t.Fatal(err)
	}
	tenants := []string{"t0", "t1", "t2", "t3", "t4", "t5"}
	for _, name := range tenants {
		if _, err := h.SeedTenant(ctx, name, 30, 32); err != nil {
			t.Fatal(err)
		}
	}
	reports, err := BenchShard(ctx, h, tenants, 3, ModeLocal, 500*time.Millisecond)
	if err != nil {
		t.Fatal(err)
	}
	if len(reports) != 3 {
		t.Fatalf("expected 3 shard reports, got %d", len(reports))
	}
	for _, r := range reports {
		if r.OK == 0 {
			t.Fatalf("expected shard writes: %#v", r)
		}
		if r.Errors > r.OK {
			t.Fatalf("too many shard errors: %#v", r)
		}
	}
}

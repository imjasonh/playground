//go:build vfs

package main

import (
	"context"
	"testing"
	"time"
)

func TestSeedWorldAndAuthorize(t *testing.T) {
	ctx := context.Background()
	h, err := NewHarness(t.TempDir())
	if err != nil {
		t.Fatal(err)
	}
	w, err := SeedWorld(ctx, h, WorldConfig{
		Tenants: 1, Users: 5, ReposPerTenant: 2,
		PRsPerRepo: 10, CommentsPerPR: 3, ChecksPerPR: 4, BodyBytes: 64,
	})
	if err != nil {
		t.Fatal(err)
	}
	ctrl, _, err := h.OpenDB(ctx, controlDBName, ModeLocal)
	if err != nil {
		t.Fatal(err)
	}
	defer ctrl.Close()

	perm, ok, err := AuthorizeRepo(ctx, ctrl.DB, 1, w.RepoIDs[0])
	if err != nil || !ok {
		t.Fatalf("user1 should have access: ok=%v err=%v", ok, err)
	}
	if perm == "" {
		t.Fatal("expected permission")
	}

	repo, _, err := h.OpenDB(ctx, repoDBName(w.RepoIDs[0]), ModeLocal)
	if err != nil {
		t.Fatal(err)
	}
	defer repo.Close()
	title, err := readPR(ctx, repo.DB, 1)
	if err != nil || title == "" {
		t.Fatalf("readPR: %q %v", title, err)
	}
}

func TestAPIBenchLocal(t *testing.T) {
	ctx := context.Background()
	h, err := NewHarness(t.TempDir())
	if err != nil {
		t.Fatal(err)
	}
	w, err := SeedWorld(ctx, h, WorldConfig{
		Tenants: 1, Users: 8, ReposPerTenant: 2,
		PRsPerRepo: 20, CommentsPerPR: 4, ChecksPerPR: 6, BodyBytes: 64,
	})
	if err != nil {
		t.Fatal(err)
	}
	rep, err := BenchAPI(ctx, w, APIBenchConfig{
		Mode: ModeLocal, Duration: 500 * time.Millisecond,
		Readers: 8, Writers: 2, ControlR: 4, ControlW: 1, RepoLRU: 2,
	})
	if err != nil {
		t.Fatal(err)
	}
	if rep.RepoRead.OK == 0 {
		t.Fatalf("expected repo reads: %#v", rep.RepoRead)
	}
	if rep.ControlRead.OK == 0 {
		t.Fatalf("expected control reads: %#v", rep.ControlRead)
	}
	t.Logf("per-repo read QPS≈%.1f write QPS≈%.1f",
		rep.RepoRead.RPS()/float64(len(w.RepoIDs)),
		rep.RepoWrite.RPS()/float64(len(w.RepoIDs)))
}

func TestAPIBenchVFS(t *testing.T) {
	ctx := context.Background()
	h, err := NewHarness(t.TempDir())
	if err != nil {
		t.Fatal(err)
	}
	w, err := SeedWorld(ctx, h, WorldConfig{
		Tenants: 1, Users: 4, ReposPerTenant: 1,
		PRsPerRepo: 15, CommentsPerPR: 3, ChecksPerPR: 4, BodyBytes: 32,
	})
	if err != nil {
		t.Fatal(err)
	}
	rep, err := BenchAPI(ctx, w, APIBenchConfig{
		Mode: ModeVFSWrite, Duration: 500 * time.Millisecond,
		Readers: 2, Writers: 1, ControlR: 1, ControlW: 0, RepoLRU: 1,
	})
	if err != nil {
		t.Fatal(err)
	}
	if rep.RepoRead.OK == 0 && rep.RepoWrite.OK == 0 {
		t.Fatalf("expected some repo traffic: %#v", rep)
	}
}

func TestRepoColdOpen(t *testing.T) {
	ctx := context.Background()
	h, err := NewHarness(t.TempDir())
	if err != nil {
		t.Fatal(err)
	}
	w, err := SeedWorld(ctx, h, WorldConfig{
		Tenants: 1, Users: 3, ReposPerTenant: 1,
		PRsPerRepo: 40, CommentsPerPR: 5, ChecksPerPR: 8, BodyBytes: 128,
	})
	if err != nil {
		t.Fatal(err)
	}
	if err := BenchRepoColdOpen(ctx, w); err != nil {
		t.Fatal(err)
	}
}

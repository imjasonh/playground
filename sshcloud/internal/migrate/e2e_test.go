package migrate_test

import (
	"context"
	"net"
	"net/http"
	"os"
	"path/filepath"
	"testing"
	"time"

	"github.com/imjasonh/playground/sshcloud/internal/agent"
	"github.com/imjasonh/playground/sshcloud/internal/backend"
	"github.com/imjasonh/playground/sshcloud/internal/migrate"
	"github.com/imjasonh/playground/sshcloud/internal/placement"
	"github.com/imjasonh/playground/sshcloud/internal/snapshot"
)

// TestCrossHostMigrateE2E boots an instance on host A (fake runtime), migrates
// it to host B via shared LocalStore, and verifies dial + placement.
func TestCrossHostMigrateE2E(t *testing.T) {
	ctx := context.Background()
	root := t.TempDir()
	sharedSnaps := filepath.Join(root, "snaps")
	store, err := snapshot.NewLocalStore(sharedSnaps)
	if err != nil {
		t.Fatal(err)
	}
	baseRootfs := filepath.Join(root, "base.ext4")
	if err := os.WriteFile(baseRootfs, []byte("base\n"), 0o644); err != nil {
		t.Fatal(err)
	}

	hostA := startFakeAgent(t, filepath.Join(root, "a"), baseRootfs, store)
	hostB := startFakeAgent(t, filepath.Join(root, "b"), baseRootfs, store)

	place := placement.NewMemory()
	if err := place.Set(ctx, "alice", "fortune", "host-a"); err != nil {
		t.Fatal(err)
	}
	agents := migrate.Hosts{
		"host-a": {BaseURL: hostA.URL},
		"host-b": {BaseURL: hostB.URL},
	}
	dial := &backend.PlacedDial{
		Placement:   place,
		Agents:      agents,
		DefaultHost: "host-a",
	}

	// Cold boot on A via placement.
	addr1, err := dial.Addr("alice", "fortune")
	if err != nil {
		t.Fatalf("ensure on A: %v", err)
	}
	if err := dialTCP(addr1); err != nil {
		t.Fatalf("dial A addr %s: %v", addr1, err)
	}
	stA, ok, err := agents["host-a"].Status("alice", "fortune")
	if err != nil || !ok || stA.State != "running" {
		t.Fatalf("host-a status: ok=%v st=%+v err=%v", ok, stA, err)
	}
	if _, ok, _ := agents["host-b"].Status("alice", "fortune"); ok {
		t.Fatal("host-b should not have the instance yet")
	}

	mig := &migrate.Migrator{Placement: place, Hosts: agents}
	res, err := mig.Migrate(ctx, "alice", "fortune", "host-b")
	if err != nil {
		t.Fatalf("migrate: %v", err)
	}
	if res.FromHost != "host-a" || res.ToHost != "host-b" {
		t.Fatalf("result hosts: %+v", res)
	}
	if res.Addr == "" {
		t.Fatal("empty adopt addr")
	}
	if err := dialTCP(res.Addr); err != nil {
		t.Fatalf("dial migrated addr %s: %v", res.Addr, err)
	}

	// Source gone; target running.
	if _, ok, _ := agents["host-a"].Status("alice", "fortune"); ok {
		t.Fatal("host-a still has instance after evict")
	}
	stB, ok, err := agents["host-b"].Status("alice", "fortune")
	if err != nil || !ok || stB.State != "running" {
		t.Fatalf("host-b status: ok=%v st=%+v err=%v", ok, stB, err)
	}

	host, ok, err := place.Get(ctx, "alice", "fortune")
	if err != nil || !ok || host != "host-b" {
		t.Fatalf("placement: host=%q ok=%v err=%v", host, ok, err)
	}

	// Gateway-style dial follows new placement.
	addr2, err := dial.Addr("alice", "fortune")
	if err != nil {
		t.Fatalf("ensure after migrate: %v", err)
	}
	if err := dialTCP(addr2); err != nil {
		t.Fatalf("dial B via placement %s: %v", addr2, err)
	}
	if addr2 == addr1 {
		// Fake runtime allocates a new localhost port on restore; must differ.
		t.Fatalf("expected new dial addr after migrate, both %s", addr1)
	}

	// Idempotent migrate to same host.
	res2, err := mig.Migrate(ctx, "alice", "fortune", "host-b")
	if err != nil {
		t.Fatalf("re-migrate same host: %v", err)
	}
	if res2.ToHost != "host-b" || res2.Addr == "" {
		t.Fatalf("re-migrate result: %+v", res2)
	}

	// Migrate back to A.
	res3, err := mig.Migrate(ctx, "alice", "fortune", "host-a")
	if err != nil {
		t.Fatalf("migrate back: %v", err)
	}
	if err := dialTCP(res3.Addr); err != nil {
		t.Fatalf("dial after migrate back: %v", err)
	}
	if _, ok, _ := agents["host-b"].Status("alice", "fortune"); ok {
		t.Fatal("host-b should be empty after migrate back")
	}
}

type fakeAgent struct {
	URL string
	mgr *agent.Manager
	srv *http.Server
}

func startFakeAgent(t *testing.T, workDir, baseRootfs string, store snapshot.Store) *fakeAgent {
	t.Helper()
	mgr, err := agent.NewManager(agent.Config{
		WorkDir:     workDir,
		KernelPath:  filepath.Join(workDir, "vmlinux"),
		BaseRootfs:  baseRootfs,
		SnapStore:   store,
		Runtime:     &agent.FakeRuntime{},
		IdleTimeout: 0,
	})
	if err != nil {
		t.Fatal(err)
	}
	_ = os.WriteFile(filepath.Join(workDir, "vmlinux"), []byte("vmlinux"), 0o644)

	mux := http.NewServeMux()
	(&agent.Handler{Manager: mgr}).Mount(mux)
	ln, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	srv := &http.Server{Handler: mux}
	go func() { _ = srv.Serve(ln) }()
	t.Cleanup(func() {
		shutdown, cancel := context.WithTimeout(context.Background(), 2*time.Second)
		defer cancel()
		_ = srv.Shutdown(shutdown)
		_ = mgr.Close()
	})
	return &fakeAgent{URL: "http://" + ln.Addr().String(), mgr: mgr, srv: srv}
}

func dialTCP(addr string) error {
	c, err := net.DialTimeout("tcp", addr, 2*time.Second)
	if err != nil {
		return err
	}
	return c.Close()
}

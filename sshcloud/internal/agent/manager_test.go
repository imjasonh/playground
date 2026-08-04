package agent

import (
	"context"
	"os"
	"strings"
	"testing"
	"time"

	"github.com/imjasonh/playground/sshcloud/internal/firecracker"
	"github.com/imjasonh/playground/sshcloud/internal/snapshot"
)

func TestEnsureRequiresKVM(t *testing.T) {
	if firecracker.Available() {
		t.Skip("KVM available; this test asserts the no-KVM error path")
	}
	dir := t.TempDir()
	mgr, err := NewManager(Config{
		WorkDir:     dir,
		KernelPath:  dir + "/vmlinux",
		BaseRootfs:  dir + "/rootfs.ext4",
		IdleTimeout: 0,
	})
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { _ = mgr.Close() })
	_, err = mgr.Ensure(context.Background(), "alice", "fortune")
	if err == nil || !strings.Contains(err.Error(), "/dev/kvm") {
		t.Fatalf("expected kvm error, got %v", err)
	}
}

func TestSleepRequiresStoreAndRunning(t *testing.T) {
	dir := t.TempDir()
	mgr, err := NewManager(Config{
		WorkDir:     dir,
		KernelPath:  dir + "/vmlinux",
		BaseRootfs:  dir + "/rootfs.ext4",
		IdleTimeout: 0,
	})
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { _ = mgr.Close() })

	err = mgr.Sleep(context.Background(), "alice", "fortune")
	if err == nil || !strings.Contains(err.Error(), "snapshot store") {
		t.Fatalf("expected store error, got %v", err)
	}

	store, err := snapshot.NewLocalStore(dir + "/snaps")
	if err != nil {
		t.Fatal(err)
	}
	mgr2, err := NewManager(Config{
		WorkDir:     dir + "/w2",
		KernelPath:  dir + "/vmlinux",
		BaseRootfs:  dir + "/rootfs.ext4",
		SnapStore:   store,
		IdleTimeout: 0,
	})
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { _ = mgr2.Close() })
	err = mgr2.Sleep(context.Background(), "alice", "fortune")
	if err == nil || !strings.Contains(err.Error(), "not found") {
		t.Fatalf("expected not found, got %v", err)
	}
}

func TestFakeSleepWakeEvictAdopt(t *testing.T) {
	dir := t.TempDir()
	store, err := snapshot.NewLocalStore(dir + "/snaps")
	if err != nil {
		t.Fatal(err)
	}
	base := dir + "/base.ext4"
	if err := os.WriteFile(base, []byte("base\n"), 0o644); err != nil {
		t.Fatal(err)
	}
	mgr, err := NewManager(Config{
		WorkDir:     dir + "/w",
		KernelPath:  dir + "/vmlinux",
		BaseRootfs:  base,
		SnapStore:   store,
		Runtime:     &FakeRuntime{},
		IdleTimeout: 0,
	})
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { _ = mgr.Close() })

	ctx := context.Background()
	in, err := mgr.Ensure(ctx, "alice", "fortune")
	if err != nil {
		t.Fatal(err)
	}
	addr1 := in.Addr
	if err := mgr.Sleep(ctx, "alice", "fortune"); err != nil {
		t.Fatal(err)
	}
	st, ok := mgr.Status("alice", "fortune")
	if !ok || st.State != StateSleeping {
		t.Fatalf("status after sleep: ok=%v %+v", ok, st)
	}
	if err := mgr.Evict("alice", "fortune"); err != nil {
		t.Fatal(err)
	}
	if _, ok := mgr.Status("alice", "fortune"); ok {
		t.Fatal("expected gone after evict")
	}
	in2, err := mgr.Adopt(ctx, "alice", "fortune")
	if err != nil {
		t.Fatal(err)
	}
	if in2.Addr == "" || in2.Addr == addr1 {
		// New listener after restore.
		if in2.Addr == "" {
			t.Fatal("empty addr after adopt")
		}
	}
	if in2.State != StateRunning {
		t.Fatalf("state %s", in2.State)
	}
}

func TestIdleLoopDisabledWhenTimeoutZero(t *testing.T) {
	dir := t.TempDir()
	store, err := snapshot.NewLocalStore(dir + "/snaps")
	if err != nil {
		t.Fatal(err)
	}
	mgr, err := NewManager(Config{
		WorkDir:     dir,
		KernelPath:  dir + "/vmlinux",
		BaseRootfs:  dir + "/rootfs.ext4",
		SnapStore:   store,
		IdleTimeout: 0,
	})
	if err != nil {
		t.Fatal(err)
	}
	// Inject a fake running instance that looks idle; sleepIdle must no-op
	// when IdleTimeout is 0 (and Close must not hang on idleLoop).
	mgr.mu.Lock()
	mgr.inst[InstanceKey{User: "a", App: "b"}] = &Instance{
		Key:      InstanceKey{User: "a", App: "b"},
		State:    StateRunning,
		LastUsed: time.Now().Add(-time.Hour),
	}
	mgr.mu.Unlock()
	mgr.sleepIdle() // IdleTimeout 0 → return immediately
	st, ok := mgr.Status("a", "b")
	if !ok || st.State != StateRunning {
		t.Fatalf("expected still running, got ok=%v %+v", ok, st)
	}
	_ = mgr.Close()
}

func TestStatusUnknown(t *testing.T) {
	dir := t.TempDir()
	mgr, err := NewManager(Config{
		WorkDir:     dir,
		KernelPath:  dir + "/vmlinux",
		BaseRootfs:  dir + "/rootfs.ext4",
		IdleTimeout: 0,
	})
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { _ = mgr.Close() })
	if _, ok := mgr.Status("x", "y"); ok {
		t.Fatal("expected missing")
	}
}

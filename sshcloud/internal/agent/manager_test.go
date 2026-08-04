package agent

import (
	"context"
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

//go:build kvm

package agent_test

import (
	"context"
	"fmt"
	"net"
	"os"
	"path/filepath"
	"testing"
	"time"

	"github.com/imjasonh/playground/sshcloud/internal/agent"
	"github.com/imjasonh/playground/sshcloud/internal/firecracker"
	"github.com/imjasonh/playground/sshcloud/internal/guestinit"
	"github.com/imjasonh/playground/sshcloud/internal/snapshot"
)

// Real Firecracker e2e. Requires /dev/kvm, CAP_NET_ADMIN (TAP), and assets
// prepared by hack/run-kvm-e2e.sh (env SSHCLOUD_*).
func TestKVMSleepWake(t *testing.T) {
	cfg := kvmConfig(t)
	work := shortWorkDir(t, "sw")
	store, err := snapshot.NewLocalStore(filepath.Join(work, "snaps"))
	if err != nil {
		t.Fatal(err)
	}
	mgr, err := agent.NewManager(kvmManagerConfig(cfg, filepath.Join(work, "w"), store, "172.30"))
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { _ = mgr.Close() })

	ctx, cancel := context.WithTimeout(context.Background(), 3*time.Minute)
	defer cancel()

	in, err := mgr.Ensure(ctx, "alice", "fortune")
	if err != nil {
		t.Fatalf("boot: %v", err)
	}
	if err := dialTCP(in.Addr, 5*time.Second); err != nil {
		t.Fatalf("dial after boot %s: %v", in.Addr, err)
	}

	if err := mgr.Sleep(ctx, "alice", "fortune"); err != nil {
		t.Fatalf("sleep: %v", err)
	}
	st, ok := mgr.Status("alice", "fortune")
	if !ok || st.State != agent.StateSleeping {
		t.Fatalf("expected sleeping, got ok=%v %+v", ok, st)
	}
	// Guest should be down while sleeping.
	if err := dialTCP(in.Addr, 500*time.Millisecond); err == nil {
		t.Fatal("guest still accepting connections while sleeping")
	}

	woken, err := mgr.Ensure(ctx, "alice", "fortune")
	if err != nil {
		t.Fatalf("wake: %v", err)
	}
	if err := dialTCP(woken.Addr, 10*time.Second); err != nil {
		t.Fatalf("dial after wake %s: %v", woken.Addr, err)
	}
}

func TestKVMCrossHostMigrate(t *testing.T) {
	cfg := kvmConfig(t)
	work := shortWorkDir(t, "mig")
	store, err := snapshot.NewLocalStore(filepath.Join(work, "snaps"))
	if err != nil {
		t.Fatal(err)
	}

	mgrA, err := agent.NewManager(kvmManagerConfig(cfg, filepath.Join(work, "a"), store, "172.31"))
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { _ = mgrA.Close() })

	mgrB, err := agent.NewManager(kvmManagerConfig(cfg, filepath.Join(work, "b"), store, "172.32"))
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { _ = mgrB.Close() })

	ctx, cancel := context.WithTimeout(context.Background(), 4*time.Minute)
	defer cancel()

	in, err := mgrA.Ensure(ctx, "bob", "fortune")
	if err != nil {
		t.Fatalf("boot on A: %v", err)
	}
	if err := dialTCP(in.Addr, 5*time.Second); err != nil {
		t.Fatalf("dial A: %v", err)
	}

	if err := mgrA.Sleep(ctx, "bob", "fortune"); err != nil {
		t.Fatalf("sleep A: %v", err)
	}
	if err := mgrA.Evict("bob", "fortune"); err != nil {
		t.Fatalf("evict A: %v", err)
	}
	if _, ok := mgrA.Status("bob", "fortune"); ok {
		t.Fatal("A still has instance after evict")
	}

	adopted, err := mgrB.Adopt(ctx, "bob", "fortune")
	if err != nil {
		t.Fatalf("adopt on B: %v", err)
	}
	if err := dialTCP(adopted.Addr, 15*time.Second); err != nil {
		t.Fatalf("dial B after adopt %s: %v", adopted.Addr, err)
	}
	// Guest IP preserved across migrate (Firecracker memory).
	if adopted.GuestIP != in.GuestIP {
		t.Fatalf("guest IP changed: %s → %s", in.GuestIP, adopted.GuestIP)
	}
}

type kvmAssets struct {
	fc, kernel, rootfs, caPub, guestInit string
	bootSpec                             guestinit.Spec
}

func kvmManagerConfig(cfg kvmAssets, workDir string, store snapshot.Store, subnet string) agent.Config {
	return agent.Config{
		WorkDir:        workDir,
		FirecrackerBin: cfg.fc,
		KernelPath:     cfg.kernel,
		BaseRootfs:     cfg.rootfs,
		CAPubPath:      cfg.caPub,
		GuestInitPath:  cfg.guestInit,
		BaseBootSpec:   cfg.bootSpec,
		SnapStore:      store,
		IdleTimeout:    0,
		SubnetBase:     subnet,
	}
}

func kvmConfig(t *testing.T) kvmAssets {
	t.Helper()
	// Never Skip: CI and local runners must fail hard if KVM/assets are missing.
	if !firecracker.Available() {
		t.Fatal("/dev/kvm not available — enable nested virt (see hack/run-kvm-e2e.sh)")
	}
	a := kvmAssets{
		fc:        envOr(t, "SSHCLOUD_FIRECRACKER", "firecracker"),
		kernel:    mustEnv(t, "SSHCLOUD_KERNEL"),
		rootfs:    mustEnv(t, "SSHCLOUD_ROOTFS"),
		caPub:     mustEnv(t, "SSHCLOUD_CA_PUB"),
		guestInit: mustEnv(t, "SSHCLOUD_GUESTINIT"),
	}
	bootPath := os.Getenv("SSHCLOUD_BOOT_SPEC")
	if bootPath == "" {
		bootPath = guestinit.SpecBeside(a.rootfs)
	}
	spec, err := guestinit.LoadFile(bootPath)
	if err != nil {
		t.Fatalf("boot spec %s: %v", bootPath, err)
	}
	if err := spec.Validate(); err != nil {
		t.Fatalf("boot spec %s: %v", bootPath, err)
	}
	a.bootSpec = spec
	for _, p := range []string{a.kernel, a.rootfs, a.caPub, a.guestInit, bootPath} {
		if _, err := os.Stat(p); err != nil {
			t.Fatalf("missing asset %s: %v", p, err)
		}
	}
	if _, err := os.Stat(a.fc); err != nil {
		// allow PATH lookup
		if a.fc != "firecracker" {
			t.Fatalf("missing firecracker %s: %v", a.fc, err)
		}
	}
	return a
}

func mustEnv(t *testing.T, k string) string {
	t.Helper()
	v := os.Getenv(k)
	if v == "" {
		t.Fatalf("%s not set (run via hack/run-kvm-e2e.sh)", k)
	}
	return v
}

func envOr(t *testing.T, k, def string) string {
	t.Helper()
	if v := os.Getenv(k); v != "" {
		return v
	}
	return def
}

func dialTCP(addr string, timeout time.Duration) error {
	c, err := net.DialTimeout("tcp", addr, timeout)
	if err != nil {
		return err
	}
	return c.Close()
}

// shortWorkDir keeps Firecracker API socket paths under the unix sun_path limit.
func shortWorkDir(t *testing.T, name string) string {
	t.Helper()
	root := os.Getenv("SSHCLOUD_WORK_ROOT")
	if root == "" {
		root = "/tmp/sshcloud-kvm"
	}
	dir := filepath.Join(root, fmt.Sprintf("%s-%d", name, os.Getpid()))
	if err := os.MkdirAll(dir, 0o755); err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { _ = os.RemoveAll(dir) })
	return dir
}

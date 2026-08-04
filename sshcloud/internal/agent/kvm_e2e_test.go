//go:build kvm

package agent_test

import (
	"context"
	"fmt"
	"io"
	"log"
	"net"
	"net/http/httptest"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
	"time"

	"github.com/google/go-containerregistry/pkg/registry"

	"github.com/imjasonh/playground/sshcloud/internal/agent"
	"github.com/imjasonh/playground/sshcloud/internal/apppack"
	"github.com/imjasonh/playground/sshcloud/internal/firecracker"
	"github.com/imjasonh/playground/sshcloud/internal/ocirootfs"
	"github.com/imjasonh/playground/sshcloud/internal/snapshot"
)

// Real Firecracker e2e via the normal deploy path: fortune as a digest-pinned
// OCI image (not a built-in base rootfs). Requires /dev/kvm, CAP_NET_ADMIN,
// and assets from hack/run-kvm-e2e.sh (SSHCLOUD_*).
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

	in, err := mgr.EnsureWith(ctx, "alice", "fortune", agent.EnsureOpts{Image: cfg.image})
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
	if err := dialTCP(in.Addr, 500*time.Millisecond); err == nil {
		t.Fatal("guest still accepting connections while sleeping")
	}

	woken, err := mgr.EnsureWith(ctx, "alice", "fortune", agent.EnsureOpts{Image: cfg.image})
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

	in, err := mgrA.EnsureWith(ctx, "bob", "fortune", agent.EnsureOpts{Image: cfg.image})
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
	if adopted.GuestIP != in.GuestIP {
		t.Fatalf("guest IP changed: %s → %s", in.GuestIP, adopted.GuestIP)
	}
}

type kvmAssets struct {
	fc, kernel, caPub, guestInit, image string
	ociCache                            string
}

func kvmManagerConfig(cfg kvmAssets, workDir string, store snapshot.Store, subnet string) agent.Config {
	cache := cfg.ociCache
	return agent.Config{
		WorkDir:        workDir,
		FirecrackerBin: cfg.fc,
		KernelPath:     cfg.kernel,
		CAPubPath:      cfg.caPub,
		GuestInitPath:  cfg.guestInit,
		SnapStore:      store,
		IdleTimeout:    0,
		SubnetBase:     subnet,
		RootfsResolver: func(ctx context.Context, imageRef string) (agent.ResolvedRootfs, error) {
			res, err := ocirootfs.Materialize(ctx, imageRef, ocirootfs.Options{CacheDir: cache, SizeMB: 64})
			if err != nil {
				return agent.ResolvedRootfs{}, err
			}
			return agent.ResolvedRootfs{Path: res.Rootfs, Spec: res.Spec}, nil
		},
	}
}

func kvmConfig(t *testing.T) kvmAssets {
	t.Helper()
	if !firecracker.Available() {
		t.Fatal("/dev/kvm not available — enable nested virt (see hack/run-kvm-e2e.sh)")
	}
	workRoot := os.Getenv("SSHCLOUD_WORK_ROOT")
	if workRoot == "" {
		workRoot = "/tmp/sshcloud-kvm"
	}
	ociCache := filepath.Join(workRoot, fmt.Sprintf("oci-cache-%d", os.Getpid()))
	if err := os.MkdirAll(ociCache, 0o755); err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { _ = os.RemoveAll(ociCache) })
	a := kvmAssets{
		fc:        envOr(t, "SSHCLOUD_FIRECRACKER", "firecracker"),
		kernel:    mustEnv(t, "SSHCLOUD_KERNEL"),
		caPub:     mustEnv(t, "SSHCLOUD_CA_PUB"),
		guestInit: mustEnv(t, "SSHCLOUD_GUESTINIT"),
		ociCache:  ociCache,
	}
	for _, p := range []string{a.kernel, a.caPub, a.guestInit} {
		if _, err := os.Stat(p); err != nil {
			t.Fatalf("missing asset %s: %v", p, err)
		}
	}
	if _, err := os.Stat(a.fc); err != nil {
		if a.fc != "firecracker" {
			t.Fatalf("missing firecracker %s: %v", a.fc, err)
		}
	}
	a.image = publishFortuneImage(t)
	return a
}

func publishFortuneImage(t *testing.T) string {
	t.Helper()
	if ref := os.Getenv("SSHCLOUD_FORTUNE_IMAGE"); ref != "" {
		return ref
	}
	bin := mustEnv(t, "SSHCLOUD_FORTUNE_BIN")
	img, err := apppack.Build(apppack.Spec{Binary: bin, GuestPath: "/fortune"})
	if err != nil {
		t.Fatal(err)
	}
	srv := httptest.NewServer(registry.New(registry.Logger(log.New(io.Discard, "", 0))))
	t.Cleanup(srv.Close)
	host := strings.TrimPrefix(srv.URL, "http://")
	ref, err := apppack.Push(img, host+"/sshcloud/fortune:kvm")
	if err != nil {
		t.Fatal(err)
	}
	return ref
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

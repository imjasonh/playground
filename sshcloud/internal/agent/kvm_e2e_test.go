//go:build kvm

package agent_test

import (
	"bytes"
	"context"
	"encoding/json"
	"fmt"
	"io"
	"log"
	"net"
	"net/http"
	"net/http/httptest"
	"os"
	"path/filepath"
	"strings"
	"sync"
	"testing"
	"time"

	"github.com/google/go-containerregistry/pkg/registry"
	"golang.org/x/crypto/ssh"

	"github.com/imjasonh/playground/sshcloud/internal/agent"
	"github.com/imjasonh/playground/sshcloud/internal/apppack"
	"github.com/imjasonh/playground/sshcloud/internal/firecracker"
	"github.com/imjasonh/playground/sshcloud/internal/ocirootfs"
	"github.com/imjasonh/playground/sshcloud/internal/snapshot"
	"github.com/imjasonh/playground/sshcloud/internal/userca"
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
	faultStore := &cancelFirstPutStore{Store: store}
	mgr, err := agent.NewManager(kvmManagerConfig(cfg, filepath.Join(work, "w"), faultStore, "172.30"))
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { _ = mgr.Close() })

	ctx, cancel := context.WithTimeout(context.Background(), 3*time.Minute)
	defer cancel()

	mux := http.NewServeMux()
	(&agent.Handler{Manager: mgr}).Mount(mux)
	body, _ := json.Marshal(map[string]string{"user": "alice", "app": "fortune", "image": cfg.image})
	requestCtx, cancelRequest := context.WithCancel(ctx)
	req := httptest.NewRequest(http.MethodPost, "/v1/instances/ensure", bytes.NewReader(body)).WithContext(requestCtx)
	rec := httptest.NewRecorder()
	mux.ServeHTTP(rec, req)
	cancelRequest() // A completed HTTP request must not own the VMM lifetime.
	if rec.Code != http.StatusOK {
		t.Fatalf("boot via HTTP: %d %s", rec.Code, rec.Body.String())
	}
	var in struct {
		Addr             string `json:"addr"`
		GuestIP          string `json:"guest_ip"`
		SSHHostPublicKey string `json:"ssh_host_public_key"`
	}
	if err := json.NewDecoder(rec.Body).Decode(&in); err != nil {
		t.Fatal(err)
	}
	if _, _, _, _, err := ssh.ParseAuthorizedKey([]byte(in.SSHHostPublicKey)); err != nil {
		t.Fatalf("invalid app host key: %v", err)
	}
	time.Sleep(100 * time.Millisecond)
	if err := dialTCP(in.Addr, 5*time.Second); err != nil {
		t.Fatalf("dial after HTTP request ended %s: %v", in.Addr, err)
	}
	assertAppSSH(t, in.Addr, in.SSHHostPublicKey, cfg.caKey, "alice")

	// Chaos: persistence fails after canceling the request context. The manager
	// must use its recovery context to resume the paused VMM.
	failedSleepCtx, cancelFailedSleep := context.WithCancel(ctx)
	faultStore.CancelNextPut(cancelFailedSleep)
	if err := mgr.Sleep(failedSleepCtx, "alice", "fortune"); err == nil {
		t.Fatal("expected injected snapshot Put failure")
	}
	if err := dialTCP(in.Addr, 5*time.Second); err != nil {
		t.Fatalf("guest was not resumed after snapshot Put failure: %v", err)
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
	if woken.SSHHostPublicKey != in.SSHHostPublicKey {
		t.Fatal("SSH host key changed across snapshot wake")
	}
	assertAppSSH(t, woken.Addr, woken.SSHHostPublicKey, cfg.caKey, "alice")
}

func TestKVMCrossHostMigrate(t *testing.T) {
	cfg := kvmConfig(t)
	work := shortWorkDir(t, "mig")
	store, err := snapshot.NewLocalStore(filepath.Join(work, "snaps"))
	if err != nil {
		t.Fatal(err)
	}

	// The explicit direct test runtime embeds this host path. Production's
	// jailed layout instead embeds the fixed in-chroot /rootfs.ext4 path.
	hostWork := filepath.Join(work, "host")
	mgrA, err := agent.NewManager(kvmManagerConfig(cfg, hostWork, store, "172.31"))
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { _ = mgrA.Close() })

	mgrB, err := agent.NewManager(kvmManagerConfig(cfg, hostWork, store, "172.31"))
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

	// Simulate host replacement: the fresh manager has no in-memory instance,
	// so ordinary Ensure must discover and adopt the durable snapshot.
	adopted, err := mgrB.EnsureWith(ctx, "bob", "fortune", agent.EnsureOpts{Image: cfg.image})
	if err != nil {
		t.Fatalf("adopt on B: %v", err)
	}
	if err := dialTCP(adopted.Addr, 15*time.Second); err != nil {
		t.Fatalf("dial B after adopt %s: %v", adopted.Addr, err)
	}
	if adopted.GuestIP != in.GuestIP {
		t.Fatalf("guest IP changed: %s → %s", in.GuestIP, adopted.GuestIP)
	}
	if adopted.SSHHostPublicKey != in.SSHHostPublicKey {
		t.Fatal("SSH host key changed across host migration")
	}
	assertAppSSH(t, adopted.Addr, adopted.SSHHostPublicKey, cfg.caKey, "bob")
}

type cancelFirstPutStore struct {
	snapshot.Store
	mu     sync.Mutex
	cancel context.CancelFunc
}

func (s *cancelFirstPutStore) CancelNextPut(cancel context.CancelFunc) {
	s.mu.Lock()
	defer s.mu.Unlock()
	s.cancel = cancel
}

func (s *cancelFirstPutStore) Put(ctx context.Context, ref snapshot.Ref, pkg snapshot.Package) error {
	s.mu.Lock()
	cancel := s.cancel
	s.cancel = nil
	s.mu.Unlock()
	if cancel != nil {
		cancel()
		return context.Canceled
	}
	return s.Store.Put(ctx, ref, pkg)
}

type kvmAssets struct {
	fc, kernel, caPub, caKey, guestInit, image string
	ociCache                                   string
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
		Runtime:        agent.DirectRuntime{},
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
		caKey:     mustEnv(t, "SSHCLOUD_CA_KEY"),
		guestInit: mustEnv(t, "SSHCLOUD_GUESTINIT"),
		ociCache:  ociCache,
	}
	for _, p := range []string{a.kernel, a.caPub, a.caKey, a.guestInit} {
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

func assertAppSSH(t *testing.T, addr, hostPublicKey, caKey, principal string) {
	t.Helper()
	hostKey, _, _, _, err := ssh.ParseAuthorizedKey([]byte(hostPublicKey))
	if err != nil {
		t.Fatal(err)
	}
	ca, err := userca.LoadOrGenerate(caKey)
	if err != nil {
		t.Fatal(err)
	}
	cert, err := ca.Mint(principal, time.Minute)
	if err != nil {
		t.Fatal(err)
	}
	client, err := ssh.Dial("tcp", addr, &ssh.ClientConfig{
		User: principal, Auth: []ssh.AuthMethod{ssh.PublicKeys(cert.Signer)},
		HostKeyCallback: ssh.FixedHostKey(hostKey), Timeout: 5 * time.Second,
	})
	if err != nil {
		t.Fatalf("cert-authenticated SSH: %v", err)
	}
	defer client.Close()
	session, err := client.NewSession()
	if err != nil {
		t.Fatal(err)
	}
	output, err := session.CombinedOutput("probe")
	if err != nil {
		t.Fatalf("app exec: %v (%s)", err, output)
	}
	if !strings.Contains(string(output), "hello "+principal) {
		t.Fatalf("app output %q", output)
	}
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

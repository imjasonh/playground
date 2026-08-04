package agent

import (
	"context"
	"errors"
	"os"
	"strings"
	"sync/atomic"
	"testing"
	"time"

	"github.com/imjasonh/playground/sshcloud/internal/firecracker"
	"github.com/imjasonh/playground/sshcloud/internal/guestinit"
	"github.com/imjasonh/playground/sshcloud/internal/snapshot"
)

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

func TestEvictRequiresSleep(t *testing.T) {
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
	mgr.mu.Lock()
	mgr.inst[InstanceKey{User: "a", App: "b"}] = &Instance{
		Key:     InstanceKey{User: "a", App: "b"},
		State:   StateRunning,
		machine: &stubMachine{},
	}
	mgr.mu.Unlock()
	err = mgr.Evict("a", "b")
	if err == nil || !strings.Contains(err.Error(), "still running") {
		t.Fatalf("expected still running error, got %v", err)
	}
}

func TestResolveBaseRootfs(t *testing.T) {
	dir := t.TempDir()
	digest := "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"
	ref := "ghcr.io/me/app@sha256:" + digest
	baseSpec := guestinit.Spec{Entrypoint: []string{"/fortune"}, Cmd: []string{"-listen", "0.0.0.0:22"}}
	var got string
	mgr, err := NewManager(Config{
		WorkDir:      dir,
		KernelPath:   dir + "/vmlinux",
		BaseRootfs:   dir + "/rootfs.ext4",
		BaseBootSpec: baseSpec,
		RootfsResolver: func(_ context.Context, imageRef string) (ResolvedRootfs, error) {
			got = imageRef
			return ResolvedRootfs{
				Path: dir + "/cached.ext4",
				Spec: guestinit.Spec{Entrypoint: []string{"/app"}},
			}, nil
		},
	})
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { _ = mgr.Close() })

	res, err := mgr.resolveBaseRootfs(context.Background(), "")
	if err != nil || res.Path != dir+"/rootfs.ext4" {
		t.Fatalf("empty image: path=%q err=%v", res.Path, err)
	}
	if strings.Join(guestinit.Argv(res.Spec), " ") != "/fortune -listen 0.0.0.0:22" {
		t.Fatalf("base spec %+v", res.Spec)
	}

	res, err = mgr.resolveBaseRootfs(context.Background(), ref)
	if err != nil {
		t.Fatal(err)
	}
	if got != ref || res.Path != dir+"/cached.ext4" {
		t.Fatalf("got ref=%q path=%q", got, res.Path)
	}

	_, err = mgr.resolveBaseRootfs(context.Background(), "alpine:latest")
	if err == nil || !strings.Contains(err.Error(), "digest-pinned") {
		t.Fatalf("expected digest error, got %v", err)
	}
}

func TestResolveBaseRootfsRequiresSpec(t *testing.T) {
	dir := t.TempDir()
	mgr, err := NewManager(Config{
		WorkDir:    dir,
		KernelPath: dir + "/vmlinux",
		BaseRootfs: dir + "/rootfs.ext4",
	})
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { _ = mgr.Close() })
	_, err = mgr.resolveBaseRootfs(context.Background(), "")
	if err == nil || !strings.Contains(err.Error(), "no boot spec") {
		t.Fatalf("got %v", err)
	}

	if err := guestinit.WriteFile(guestinit.SpecBeside(dir+"/rootfs.ext4"), guestinit.Spec{
		Entrypoint: []string{"/app"},
	}); err != nil {
		t.Fatal(err)
	}
	res, err := mgr.resolveBaseRootfs(context.Background(), "")
	if err != nil || strings.Join(guestinit.Argv(res.Spec), " ") != "/app" {
		t.Fatalf("sidecar: %+v err=%v", res.Spec, err)
	}
}

func TestResolveBaseRootfsRequiresResolver(t *testing.T) {
	dir := t.TempDir()
	mgr, err := NewManager(Config{
		WorkDir:    dir,
		KernelPath: dir + "/vmlinux",
		BaseRootfs: dir + "/rootfs.ext4",
	})
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { _ = mgr.Close() })
	digest := "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"
	_, err = mgr.resolveBaseRootfs(context.Background(), "ghcr.io/me/app@sha256:"+digest)
	if err == nil || !strings.Contains(err.Error(), "RootfsResolver") {
		t.Fatalf("got %v", err)
	}
}

func TestSetNoIdleSkipsSleep(t *testing.T) {
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
		IdleTimeout: time.Minute,
	})
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { _ = mgr.Close() })
	mgr.mu.Lock()
	mgr.inst[InstanceKey{User: "a", App: "b"}] = &Instance{
		Key:      InstanceKey{User: "a", App: "b"},
		State:    StateRunning,
		LastUsed: time.Now().Add(-time.Hour),
		noIdle:   true,
	}
	mgr.mu.Unlock()
	mgr.sleepIdle()
	st, ok := mgr.Status("a", "b")
	if !ok || st.State != StateRunning {
		t.Fatalf("expected still running, got ok=%v %+v", ok, st)
	}
}

func TestPrepareGuestInitEmptySpecFails(t *testing.T) {
	mgr := &Manager{cfg: Config{GuestInitPath: "/bin/true"}}
	_, err := mgr.prepareGuestInit("unused.ext4", guestinit.Spec{})
	if err == nil || !strings.Contains(err.Error(), "empty Entrypoint and Cmd") {
		t.Fatalf("got %v", err)
	}
}

func TestPrepareGuestInitRequiresBinary(t *testing.T) {
	mgr := &Manager{}
	_, err := mgr.prepareGuestInit("unused.ext4", guestinit.Spec{Entrypoint: []string{"/app"}})
	if err == nil || !strings.Contains(err.Error(), "GuestInitPath") {
		t.Fatalf("got %v", err)
	}
}

func TestEnsureWithImageNoResolver(t *testing.T) {
	dir := t.TempDir()
	mgr, err := NewManager(Config{
		WorkDir:    dir,
		KernelPath: dir + "/vmlinux",
		BaseRootfs: dir + "/rootfs.ext4",
	})
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { _ = mgr.Close() })
	digest := "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"
	_, err = mgr.EnsureWith(context.Background(), "alice", "app", EnsureOpts{
		Image: "ghcr.io/me/app@sha256:" + digest,
	})
	if err == nil || !strings.Contains(err.Error(), "RootfsResolver") {
		t.Fatalf("got %v", err)
	}
}

func TestResourceReservationFencesConcurrentRestore(t *testing.T) {
	t.Parallel()
	mgr := &Manager{
		inst:     make(map[InstanceKey]*Instance),
		reserved: make(map[string]InstanceKey),
	}
	first := InstanceKey{User: "alice", App: "first"}
	second := InstanceKey{User: "alice", App: "second"}
	if err := mgr.reserveResources(first, "/work/first", "fc-first", "172.16.2.2", "172.16.2.1"); err != nil {
		t.Fatal(err)
	}
	if err := mgr.reserveResources(second, "/work/second", "fc-second", "172.16.2.2", "172.16.2.1"); err == nil {
		t.Fatal("expected overlapping restore network to be reserved")
	}
	mgr.releaseResources(first)
	if err := mgr.reserveResources(second, "/work/second", "fc-second", "172.16.2.2", "172.16.2.1"); err != nil {
		t.Fatalf("reservation was not released: %v", err)
	}
}

type orderedSnapshotMachine struct {
	events      *[]string
	pauseErr    error
	resumeErr   error
	snapshotErr error
}

func (m orderedSnapshotMachine) Alive() bool { return true }
func (m orderedSnapshotMachine) Pause(context.Context) error {
	*m.events = append(*m.events, "pause")
	return m.pauseErr
}
func (m orderedSnapshotMachine) Resume(context.Context) error {
	*m.events = append(*m.events, "resume")
	return m.resumeErr
}
func (m orderedSnapshotMachine) CreateSnapshot(_ context.Context, files firecracker.SnapshotFiles) error {
	*m.events = append(*m.events, "snapshot")
	if m.snapshotErr != nil {
		return m.snapshotErr
	}
	if err := os.WriteFile(files.StatePath, []byte("state"), 0o644); err != nil {
		return err
	}
	return os.WriteFile(files.MemPath, []byte("memory"), 0o644)
}
func (m orderedSnapshotMachine) Stop() error { return nil }
func (m orderedSnapshotMachine) Kill() error {
	*m.events = append(*m.events, "kill")
	return nil
}

type orderedSnapshotStore struct {
	events *[]string
	putErr error
}

func (s orderedSnapshotStore) Put(context.Context, string, snapshot.Package) error {
	*s.events = append(*s.events, "put")
	return s.putErr
}
func (orderedSnapshotStore) Get(context.Context, string, string) (snapshot.Package, error) {
	return snapshot.Package{}, os.ErrNotExist
}
func (orderedSnapshotStore) Has(context.Context, string) (bool, error) { return false, nil }
func (orderedSnapshotStore) Meta(context.Context, string) (snapshot.Meta, error) {
	return snapshot.Meta{}, os.ErrNotExist
}
func (orderedSnapshotStore) Delete(context.Context, string) error { return nil }

func TestSleepPublishesBeforeKillingVMM(t *testing.T) {
	t.Parallel()
	dir := t.TempDir()
	rootfsPath := dir + "/vm/rootfs.ext4"
	if err := os.MkdirAll(dir+"/vm", 0o755); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(rootfsPath, []byte("rootfs"), 0o644); err != nil {
		t.Fatal(err)
	}
	var events []string
	store := orderedSnapshotStore{events: &events}
	mgr, err := NewManager(Config{
		WorkDir: dir, KernelPath: dir + "/kernel", BaseRootfs: rootfsPath, SnapStore: store,
	})
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { _ = mgr.Close() })
	key := InstanceKey{User: "alice", App: "fortune"}
	mgr.inst[key] = &Instance{
		Key: key, State: StateRunning, Rootfs: rootfsPath, WorkDir: dir + "/vm",
		GuestIP: "172.16.2.2", HostIP: "172.16.2.1", TapName: "fc-test",
		GuestMAC: "AA:FC:00:00:00:01", Tier: "tiny",
		machine: orderedSnapshotMachine{events: &events},
	}
	if err := mgr.Sleep(context.Background(), key.User, key.App); err != nil {
		t.Fatal(err)
	}
	if got := strings.Join(events, ","); got != "pause,snapshot,put,kill" {
		t.Fatalf("snapshot order %q", got)
	}
}

func TestSleepFailureChaosMatrix(t *testing.T) {
	t.Parallel()
	injected := errors.New("injected failure")
	tests := []struct {
		name       string
		machine    orderedSnapshotMachine
		putErr     error
		wantEvents string
		wantState  State
	}{
		{name: "pause", machine: orderedSnapshotMachine{pauseErr: injected}, wantEvents: "pause", wantState: StateRunning},
		{name: "snapshot", machine: orderedSnapshotMachine{snapshotErr: injected}, wantEvents: "pause,snapshot,resume", wantState: StateRunning},
		{name: "publish", putErr: injected, wantEvents: "pause,snapshot,put,resume", wantState: StateRunning},
		{
			name: "publish_and_resume", putErr: injected,
			machine:    orderedSnapshotMachine{resumeErr: injected},
			wantEvents: "pause,snapshot,put,resume,kill", wantState: StateFailed,
		},
	}
	for _, tc := range tests {
		t.Run(tc.name, func(t *testing.T) {
			t.Parallel()
			dir := t.TempDir()
			rootfsPath := dir + "/vm/rootfs.ext4"
			if err := os.MkdirAll(dir+"/vm", 0o755); err != nil {
				t.Fatal(err)
			}
			if err := os.WriteFile(rootfsPath, []byte("rootfs"), 0o644); err != nil {
				t.Fatal(err)
			}
			var events []string
			tc.machine.events = &events
			store := orderedSnapshotStore{events: &events, putErr: tc.putErr}
			mgr, err := NewManager(Config{
				WorkDir: dir, KernelPath: dir + "/kernel", BaseRootfs: rootfsPath, SnapStore: store,
			})
			if err != nil {
				t.Fatal(err)
			}
			key := InstanceKey{User: "alice", App: "fortune"}
			mgr.inst[key] = &Instance{
				Key: key, State: StateRunning, Rootfs: rootfsPath, WorkDir: dir + "/vm",
				GuestIP: "172.16.2.2", HostIP: "172.16.2.1", TapName: "fc-test",
				GuestMAC: "AA:FC:00:00:00:01", Tier: "tiny", machine: tc.machine,
			}
			if err := mgr.Sleep(context.Background(), key.User, key.App); err == nil {
				t.Fatal("expected injected failure")
			}
			if got := strings.Join(events, ","); got != tc.wantEvents {
				t.Fatalf("events %q, want %q", got, tc.wantEvents)
			}
			status, ok := mgr.Status(key.User, key.App)
			if !ok || status.State != tc.wantState {
				t.Fatalf("state ok=%v got=%s want=%s", ok, status.State, tc.wantState)
			}
		})
	}
}

func TestStopDeletesSnapshotAfterManagerRestart(t *testing.T) {
	t.Parallel()
	dir := t.TempDir()
	store, err := snapshot.NewLocalStore(dir + "/snapshots")
	if err != nil {
		t.Fatal(err)
	}
	pkg := snapshot.NewPackageDir(dir + "/package")
	if err := os.MkdirAll(pkg.Dir, 0o755); err != nil {
		t.Fatal(err)
	}
	for _, file := range []string{pkg.StatePath, pkg.MemPath, pkg.RootfsPath} {
		if err := os.WriteFile(file, []byte("snapshot"), 0o644); err != nil {
			t.Fatal(err)
		}
	}
	if err := pkg.WriteMeta(snapshot.Meta{User: "alice", App: "fortune"}); err != nil {
		t.Fatal(err)
	}
	key := snapshot.KeyFor("alice", "fortune")
	if err := store.Put(context.Background(), key, pkg); err != nil {
		t.Fatal(err)
	}
	mgr, err := NewManager(Config{
		WorkDir: dir + "/work", KernelPath: dir + "/kernel",
		BaseRootfs: dir + "/rootfs", SnapStore: store,
	})
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { _ = mgr.Close() })
	if err := mgr.StopContext(context.Background(), "alice", "fortune"); err != nil {
		t.Fatal(err)
	}
	if exists, err := store.Has(context.Background(), key); err != nil || exists {
		t.Fatalf("snapshot remains after stop: exists=%v err=%v", exists, err)
	}
}

type deadMachine struct {
	killed atomic.Bool
}

func (*deadMachine) Alive() bool                  { return false }
func (*deadMachine) Pause(context.Context) error  { return nil }
func (*deadMachine) Resume(context.Context) error { return nil }
func (*deadMachine) CreateSnapshot(context.Context, firecracker.SnapshotFiles) error {
	return nil
}
func (*deadMachine) Stop() error { return nil }
func (m *deadMachine) Kill() error {
	m.killed.Store(true)
	return nil
}

func TestEnsureNeverReturnsUnexpectedlyExitedVMM(t *testing.T) {
	t.Parallel()
	dir := t.TempDir()
	mgr, err := NewManager(Config{
		WorkDir: dir, KernelPath: dir + "/kernel", BaseRootfs: dir + "/rootfs",
	})
	if err != nil {
		t.Fatal(err)
	}
	dead := &deadMachine{}
	key := InstanceKey{User: "alice", App: "fortune"}
	workDir := dir + "/vm-dead"
	if err := os.MkdirAll(workDir, 0o755); err != nil {
		t.Fatal(err)
	}
	mgr.inst[key] = &Instance{
		Key: key, State: StateRunning, Addr: "172.16.2.2:22",
		WorkDir: workDir, TapName: "fc-dead", Tier: "tiny", machine: dead,
	}
	_, err = mgr.Ensure(context.Background(), key.User, key.App)
	if err == nil {
		t.Fatal("expected recovery boot attempt to fail with missing test assets")
	}
	if !dead.killed.Load() {
		t.Fatal("exited VMM resources were not cleaned")
	}
	if _, ok := mgr.Status(key.User, key.App); ok {
		t.Fatal("exited VMM remained published as running")
	}
}

func TestClosedManagerRejectsNewEnsure(t *testing.T) {
	t.Parallel()
	dir := t.TempDir()
	mgr, err := NewManager(Config{
		WorkDir: dir, KernelPath: dir + "/kernel", BaseRootfs: dir + "/rootfs",
	})
	if err != nil {
		t.Fatal(err)
	}
	if err := mgr.Close(); err != nil {
		t.Fatal(err)
	}
	if _, err := mgr.Ensure(context.Background(), "alice", "fortune"); err == nil ||
		!strings.Contains(err.Error(), "closed") {
		t.Fatalf("closed manager Ensure error = %v", err)
	}
}

func TestCapacityReservationAndCordon(t *testing.T) {
	t.Parallel()
	dir := t.TempDir()
	mgr, err := NewManager(Config{
		WorkDir: dir, KernelPath: dir + "/kernel", BaseRootfs: dir + "/rootfs",
		CapacityVCPUs: 2, CapacityMemMiB: 512,
	})
	if err != nil {
		t.Fatal(err)
	}
	first := InstanceKey{User: "alice", App: "first"}
	if err := mgr.reserveCapacity(first, "tiny", false); err != nil {
		t.Fatal(err)
	}
	view := mgr.Capacity()
	if view.Reserved.VCPUs != 1 || view.Reserved.MemMiB != 128 {
		t.Fatalf("reserved %+v", view)
	}
	if err := mgr.reserveCapacity(InstanceKey{User: "alice", App: "second"}, "small", false); err == nil {
		t.Fatal("over-capacity reservation succeeded")
	} else {
		var capacity ErrCapacity
		if !errors.As(err, &capacity) {
			t.Fatalf("error %T, want ErrCapacity", err)
		}
	}
	mgr.releaseCapacity(first)
	mgr.SetCordoned(true)
	if err := mgr.reserveCapacity(first, "tiny", false); err == nil {
		t.Fatal("cordoned host accepted reservation")
	} else {
		var cordoned ErrCordoned
		if !errors.As(err, &cordoned) {
			t.Fatalf("error %T, want ErrCordoned", err)
		}
	}
}

func TestListInstancesSplitsGeneration(t *testing.T) {
	t.Parallel()
	mgr := &Manager{inst: map[InstanceKey]*Instance{
		{User: "alice", App: "myapp.gabc"}: {
			Key:   InstanceKey{User: "alice", App: "myapp.gabc"},
			State: StateRunning, Image: "example", Tier: "small", noIdle: true,
		},
	}}
	inventory := mgr.ListInstances()
	if len(inventory) != 1 || inventory[0].App != "myapp" || inventory[0].Gen != "gabc" || !inventory[0].NoIdle {
		t.Fatalf("inventory %+v", inventory)
	}
}

func TestCordonStateSurvivesManagerRestart(t *testing.T) {
	t.Parallel()
	dir := t.TempDir()
	config := Config{WorkDir: dir, KernelPath: dir + "/kernel", BaseRootfs: dir + "/rootfs"}
	first, err := NewManager(config)
	if err != nil {
		t.Fatal(err)
	}
	if err := first.SetCordoned(true); err != nil {
		t.Fatal(err)
	}
	if err := first.Close(); err != nil {
		t.Fatal(err)
	}
	second, err := NewManager(config)
	if err != nil {
		t.Fatal(err)
	}
	defer second.Close()
	if !second.Capacity().Cordoned {
		t.Fatal("cordon state was lost across restart")
	}
}

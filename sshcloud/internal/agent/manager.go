// Package agent manages app microVM instances on a host.
package agent

import (
	"context"
	"fmt"
	"os"
	"path/filepath"
	"strings"
	"sync"
	"time"

	"github.com/imjasonh/playground/sshcloud/internal/firecracker"
	"github.com/imjasonh/playground/sshcloud/internal/guestinit"
	"github.com/imjasonh/playground/sshcloud/internal/image"
	"github.com/imjasonh/playground/sshcloud/internal/rootfs"
	"github.com/imjasonh/playground/sshcloud/internal/snapshot"
)

// InstanceKey identifies a running or sleeping app instance.
type InstanceKey struct {
	User string
	App  string
}

func (k InstanceKey) String() string { return k.User + "/" + k.App }

// State of an instance.
type State string

const (
	StateRunning  State = "running"
	StateSleeping State = "sleeping"
)

// Instance is a live or sleeping microVM endpoint.
type Instance struct {
	Key      InstanceKey
	State    State
	Addr     string
	GuestIP  string
	HostIP   string
	TapName  string
	GuestMAC string
	Rootfs   string
	WorkDir  string
	LastUsed time.Time
	machine  machine
	snapKey  string
	noIdle   bool
}

// Config for the Manager.
type Config struct {
	WorkDir        string
	FirecrackerBin string
	KernelPath     string
	BaseRootfs     string
	CAPubPath      string
	SubnetBase     string // default 172.16
	// IdleTimeout after LastUsed with no Ensure; 0 disables auto-sleep.
	IdleTimeout time.Duration
	// SnapStore persists sleep snapshots (required for sleep/migrate).
	SnapStore snapshot.Store
	// Runtime boots VMs; nil selects FirecrackerRuntime.
	Runtime Runtime
	// RootfsResolver materializes a digest-pinned OCI image to an ext4 path
	// plus the image's PID 1 spec. Used by bootCold when Ensure has an image ref.
	RootfsResolver func(ctx context.Context, imageRef string) (ResolvedRootfs, error)
	// GuestInitPath is a linux/amd64 guestinit binary injected as /platform-init.
	// Required for every cold boot.
	GuestInitPath string
	// BaseBootSpec is PID 1 for BaseRootfs (no image ref). If zero, the
	// manager loads the sibling `<rootfs>.boot.json` when booting the base image.
	BaseBootSpec guestinit.Spec
}

// ResolvedRootfs is a materialized ext4 and the OCI PID 1 spec to boot it with.
type ResolvedRootfs struct {
	Path string
	Spec guestinit.Spec
}

// EnsureOpts configures a cold boot.
type EnsureOpts struct {
	// Image is a digest-pinned OCI ref (repo@sha256:…). Empty uses BaseRootfs
	// when configured (test/dev only); production apps always set Image.
	Image string
}

// Manager boots, sleeps, wakes, and migrates Firecracker instances.
type Manager struct {
	cfg  Config
	rt   Runtime
	mu   sync.Mutex
	inst map[InstanceKey]*Instance
	seq  int
	stop chan struct{}
}

// NewManager validates config essentials.
func NewManager(cfg Config) (*Manager, error) {
	if cfg.WorkDir == "" {
		return nil, fmt.Errorf("WorkDir required")
	}
	if cfg.KernelPath == "" {
		return nil, fmt.Errorf("KernelPath required")
	}
	if cfg.BaseRootfs == "" && cfg.RootfsResolver == nil {
		return nil, fmt.Errorf("BaseRootfs or RootfsResolver required")
	}
	if cfg.SubnetBase == "" {
		cfg.SubnetBase = "172.16"
	}
	rt := cfg.Runtime
	if rt == nil {
		rt = FirecrackerRuntime{}
	}
	if err := os.MkdirAll(cfg.WorkDir, 0o755); err != nil {
		return nil, err
	}
	m := &Manager{
		cfg:  cfg,
		rt:   rt,
		inst: make(map[InstanceKey]*Instance),
		stop: make(chan struct{}),
	}
	if cfg.IdleTimeout > 0 && cfg.SnapStore != nil {
		go m.idleLoop()
	}
	return m, nil
}

// Ensure starts or wakes the instance and returns a dialable SSH address.
func (m *Manager) Ensure(ctx context.Context, user, app string) (*Instance, error) {
	return m.EnsureWith(ctx, user, app, EnsureOpts{})
}

// EnsureWith is Ensure with optional cold-boot options (digest-pinned image).
func (m *Manager) EnsureWith(ctx context.Context, user, app string, opt EnsureOpts) (*Instance, error) {
	k := InstanceKey{User: user, App: app}
	m.mu.Lock()
	if in, ok := m.inst[k]; ok {
		switch in.State {
		case StateRunning:
			in.LastUsed = time.Now()
			m.mu.Unlock()
			return in, nil
		case StateSleeping:
			m.mu.Unlock()
			return m.wake(ctx, k)
		}
	}
	m.seq++
	n := m.seq
	m.mu.Unlock()

	in, err := m.bootCold(ctx, k, n, opt.Image)
	if err != nil {
		return nil, err
	}
	m.mu.Lock()
	m.inst[k] = in
	m.mu.Unlock()
	return in, nil
}

func (m *Manager) prepareGuestInit(rootfsPath string, spec guestinit.Spec) (string, error) {
	if err := spec.Validate(); err != nil {
		return "", err
	}
	if m.cfg.GuestInitPath == "" {
		return "", fmt.Errorf("GuestInitPath required to boot a microVM")
	}
	if err := rootfs.InjectFile(rootfsPath, m.cfg.GuestInitPath, "platform-init", "0755"); err != nil {
		return "", fmt.Errorf("inject guestinit: %w", err)
	}
	specFile, err := os.CreateTemp("", "platform-boot-*.json")
	if err != nil {
		return "", err
	}
	specPath := specFile.Name()
	_ = specFile.Close()
	defer os.Remove(specPath)
	if err := guestinit.WriteFile(specPath, spec); err != nil {
		return "", err
	}
	if err := rootfs.InjectFile(rootfsPath, specPath, "platform-boot.json", "0644"); err != nil {
		return "", fmt.Errorf("inject boot spec: %w", err)
	}
	return "init=" + guestinit.GuestBinary, nil
}

func (m *Manager) resolveBaseRootfs(ctx context.Context, imageRef string) (ResolvedRootfs, error) {
	imageRef = strings.TrimSpace(imageRef)
	if imageRef == "" {
		if m.cfg.BaseRootfs == "" {
			return ResolvedRootfs{}, fmt.Errorf("image required (no base rootfs configured)")
		}
		spec, err := m.baseBootSpec()
		if err != nil {
			return ResolvedRootfs{}, err
		}
		return ResolvedRootfs{Path: m.cfg.BaseRootfs, Spec: spec}, nil
	}
	if m.cfg.RootfsResolver == nil {
		return ResolvedRootfs{}, fmt.Errorf("image %q supplied but RootfsResolver is not configured", imageRef)
	}
	if err := image.ValidateDigestPinned(imageRef); err != nil {
		return ResolvedRootfs{}, err
	}
	res, err := m.cfg.RootfsResolver(ctx, imageRef)
	if err != nil {
		return ResolvedRootfs{}, fmt.Errorf("resolve rootfs: %w", err)
	}
	if res.Path == "" {
		return ResolvedRootfs{}, fmt.Errorf("RootfsResolver returned empty path")
	}
	if err := res.Spec.Validate(); err != nil {
		return ResolvedRootfs{}, fmt.Errorf("image %q has no boot spec: %w", imageRef, err)
	}
	return res, nil
}

func (m *Manager) baseBootSpec() (guestinit.Spec, error) {
	if err := m.cfg.BaseBootSpec.Validate(); err == nil {
		return m.cfg.BaseBootSpec, nil
	}
	path := guestinit.SpecBeside(m.cfg.BaseRootfs)
	spec, err := guestinit.LoadFile(path)
	if err != nil {
		return guestinit.Spec{}, fmt.Errorf("no boot spec for base rootfs: %w (set Config.BaseBootSpec or %s)", err, path)
	}
	if err := spec.Validate(); err != nil {
		return guestinit.Spec{}, fmt.Errorf("boot spec %s: %w", path, err)
	}
	return spec, nil
}

func (m *Manager) bootCold(ctx context.Context, k InstanceKey, n int, imageRef string) (*Instance, error) {
	imageRef = strings.TrimSpace(imageRef)
	if imageRef != "" {
		if err := image.ValidateDigestPinned(imageRef); err != nil {
			return nil, err
		}
		if m.cfg.RootfsResolver == nil {
			return nil, fmt.Errorf("image %q supplied but RootfsResolver is not configured", imageRef)
		}
	}
	if !m.rt.Available() {
		return nil, fmt.Errorf("firecracker requires /dev/kvm (not available on this host)")
	}
	dir := filepath.Join(m.cfg.WorkDir, fmt.Sprintf("vm-%d", n))
	if err := os.MkdirAll(dir, 0o755); err != nil {
		return nil, err
	}
	resolved, err := m.resolveBaseRootfs(ctx, imageRef)
	if err != nil {
		return nil, err
	}
	rootfsPath := filepath.Join(dir, "rootfs.ext4")
	if err := rootfs.Clone(resolved.Path, rootfsPath); err != nil {
		return nil, err
	}
	if m.cfg.CAPubPath != "" {
		if err := rootfs.InjectFile(rootfsPath, m.cfg.CAPubPath, "ca.pub", "0644"); err != nil {
			return nil, fmt.Errorf("inject CA: %w", err)
		}
	}
	initArgs, err := m.prepareGuestInit(rootfsPath, resolved.Spec)
	if err != nil {
		return nil, err
	}

	tapName := fmt.Sprintf("fc-%d", n)
	octet := n%200 + 1
	hostIP := fmt.Sprintf("%s.%d.1", m.cfg.SubnetBase, octet)
	guestIP := fmt.Sprintf("%s.%d.2", m.cfg.SubnetBase, octet)
	if err := firecracker.CreateTap(tapName, hostIP, 24); err != nil {
		return nil, fmt.Errorf("create tap: %w (agent needs CAP_NET_ADMIN)", err)
	}

	mac := fmt.Sprintf("AA:FC:00:00:%02x:%02x", (n>>8)&0xff, n&0xff)
	bootArgs := firecracker.GuestBootArgs(guestIP, hostIP, "255.255.255.0", k.App)
	bootArgs += " " + initArgs

	mach, addr, err := m.rt.Boot(ctx, BootSpec{
		FirecrackerBin: m.cfg.FirecrackerBin,
		WorkDir:        dir,
		KernelPath:     m.cfg.KernelPath,
		RootfsPath:     rootfsPath,
		BootArgs:       bootArgs,
		TapName:        tapName,
		GuestMAC:       mac,
		GuestIP:        guestIP,
		VCPUs:          1,
		MemMiB:         128,
	})
	if err != nil {
		_ = firecracker.DeleteTap(tapName)
		return nil, err
	}

	return &Instance{
		Key:      k,
		State:    StateRunning,
		Addr:     addr,
		GuestIP:  guestIP,
		HostIP:   hostIP,
		TapName:  tapName,
		GuestMAC: mac,
		Rootfs:   rootfsPath,
		WorkDir:  dir,
		LastUsed: time.Now(),
		machine:  mach,
	}, nil
}

// InstanceStatus is a read-only view for the HTTP API.
type InstanceStatus struct {
	State    State
	Addr     string
	GuestIP  string
	LastUsed time.Time
	SnapKey  string
}

// Status returns the current state of an instance, if known.
func (m *Manager) Status(user, app string) (InstanceStatus, bool) {
	k := InstanceKey{User: user, App: app}
	m.mu.Lock()
	defer m.mu.Unlock()
	in, ok := m.inst[k]
	if !ok {
		return InstanceStatus{}, false
	}
	return InstanceStatus{
		State:    in.State,
		Addr:     in.Addr,
		GuestIP:  in.GuestIP,
		LastUsed: in.LastUsed,
		SnapKey:  in.snapKey,
	}, true
}

// Sleep snapshots a running instance, uploads it, and frees the VMM (keeps TAP).
func (m *Manager) Sleep(ctx context.Context, user, app string) error {
	k := InstanceKey{User: user, App: app}
	if m.cfg.SnapStore == nil {
		return fmt.Errorf("snapshot store not configured")
	}

	m.mu.Lock()
	in, ok := m.inst[k]
	if !ok {
		m.mu.Unlock()
		return fmt.Errorf("instance %s not found", k)
	}
	if in.State == StateSleeping {
		m.mu.Unlock()
		return nil
	}
	if in.State != StateRunning || in.machine == nil {
		m.mu.Unlock()
		return fmt.Errorf("instance %s not running", k)
	}
	mach := in.machine
	m.mu.Unlock()

	snapDir := filepath.Join(in.WorkDir, "snap")
	_ = os.RemoveAll(snapDir)
	pkg := snapshot.NewPackageDir(snapDir)
	if err := os.MkdirAll(snapDir, 0o755); err != nil {
		return err
	}
	if err := rootfs.Clone(in.Rootfs, pkg.RootfsPath); err != nil {
		return fmt.Errorf("clone rootfs for snap: %w", err)
	}
	files := firecracker.SnapshotFiles{StatePath: pkg.StatePath, MemPath: pkg.MemPath}
	if err := mach.SnapshotThenKill(ctx, files); err != nil {
		return err
	}

	meta := snapshot.Meta{
		User:       user,
		App:        app,
		GuestIP:    in.GuestIP,
		TapName:    in.TapName,
		GuestMAC:   in.GuestMAC,
		HostIP:     in.HostIP,
		RootfsPath: in.Rootfs,
		CreatedAt:  time.Now().UTC(),
	}
	if err := pkg.WriteMeta(meta); err != nil {
		return err
	}
	key := snapshot.KeyFor(user, app)
	if err := m.cfg.SnapStore.Put(ctx, key, pkg); err != nil {
		if restored, addr, wakeErr := m.restoreFromPackage(ctx, in, pkg); wakeErr == nil {
			m.mu.Lock()
			in.machine = restored
			in.Addr = addr
			in.State = StateRunning
			m.mu.Unlock()
		} else {
			m.mu.Lock()
			in.machine = nil
			m.mu.Unlock()
		}
		return fmt.Errorf("upload snapshot: %w", err)
	}

	m.mu.Lock()
	in.machine = nil
	in.State = StateSleeping
	in.snapKey = key
	in.LastUsed = time.Now()
	m.mu.Unlock()
	return nil
}

// Evict drops a sleeping instance from this host without deleting the snapshot.
// Used after Sleep as the source side of cross-host migrate. Deletes TAP and
// frees the VMM bookkeeping; the shared snapshot package retains rootfs bytes.
// The on-disk rootfs path may be removed — Adopt recreates it from the package
// at the same absolute path before snapshot/load.
func (m *Manager) Evict(user, app string) error {
	k := InstanceKey{User: user, App: app}
	m.mu.Lock()
	in, ok := m.inst[k]
	if !ok {
		m.mu.Unlock()
		return nil
	}
	if in.State == StateRunning && in.machine != nil {
		m.mu.Unlock()
		return fmt.Errorf("instance %s still running; sleep before evict", k)
	}
	delete(m.inst, k)
	m.mu.Unlock()

	if in.machine != nil {
		_ = in.machine.Kill()
	}
	if in.TapName != "" {
		_ = firecracker.DeleteTap(in.TapName)
	}
	// Remove workdir but keep parent; Adopt will recreate rootfs at Meta.RootfsPath.
	_ = os.RemoveAll(in.WorkDir)
	return nil
}

// Adopt restores an instance onto this host from the shared snapshot store.
// Used as the target side of cross-host migrate.
func (m *Manager) Adopt(ctx context.Context, user, app string) (*Instance, error) {
	k := InstanceKey{User: user, App: app}
	if m.cfg.SnapStore == nil {
		return nil, fmt.Errorf("snapshot store not configured")
	}
	if !m.rt.Available() {
		return nil, fmt.Errorf("firecracker requires /dev/kvm (not available on this host)")
	}

	m.mu.Lock()
	if in, ok := m.inst[k]; ok {
		switch in.State {
		case StateRunning:
			in.LastUsed = time.Now()
			m.mu.Unlock()
			return in, nil
		case StateSleeping:
			m.mu.Unlock()
			return m.wake(ctx, k)
		}
	}
	m.seq++
	n := m.seq
	m.mu.Unlock()

	snapDir := filepath.Join(m.cfg.WorkDir, fmt.Sprintf("adopt-%d", n))
	_ = os.RemoveAll(snapDir)
	pkg, err := m.cfg.SnapStore.Get(ctx, snapshot.KeyFor(user, app), snapDir)
	if err != nil {
		return nil, fmt.Errorf("download snapshot: %w", err)
	}
	meta := pkg.Meta
	if meta.GuestIP == "" {
		meta, err = pkg.ReadMeta()
		if err != nil {
			return nil, err
		}
		pkg.Meta = meta
	}

	// Firecracker snapshots embed absolute rootfs + TAP names. Recreate those
	// exact paths before snapshot/load (cross-host migrate and same-host wake).
	rootfsPath := meta.RootfsPath
	if rootfsPath == "" {
		rootfsPath = filepath.Join(m.cfg.WorkDir, fmt.Sprintf("vm-%d", n), "rootfs.ext4")
	}
	dir := filepath.Dir(rootfsPath)
	if err := os.MkdirAll(dir, 0o755); err != nil {
		return nil, err
	}
	tapName := meta.TapName
	if tapName == "" {
		tapName = fmt.Sprintf("fc-%d", n)
	}
	in := &Instance{
		Key:      k,
		State:    StateSleeping,
		GuestIP:  meta.GuestIP,
		HostIP:   meta.HostIP,
		TapName:  tapName,
		GuestMAC: meta.GuestMAC,
		Rootfs:   rootfsPath,
		WorkDir:  dir,
		snapKey:  snapshot.KeyFor(user, app),
		LastUsed: time.Now(),
	}

	mach, addr, err := m.restoreFromPackage(ctx, in, pkg)
	if err != nil {
		_ = os.RemoveAll(dir)
		return nil, err
	}
	in.machine = mach
	in.Addr = addr
	in.State = StateRunning

	m.mu.Lock()
	m.inst[k] = in
	m.mu.Unlock()
	return in, nil
}

func (m *Manager) wake(ctx context.Context, k InstanceKey) (*Instance, error) {
	if !m.rt.Available() {
		return nil, fmt.Errorf("firecracker requires /dev/kvm (not available on this host)")
	}
	if m.cfg.SnapStore == nil {
		return nil, fmt.Errorf("snapshot store not configured")
	}

	m.mu.Lock()
	in, ok := m.inst[k]
	if !ok {
		m.mu.Unlock()
		return nil, fmt.Errorf("unknown instance %s", k)
	}
	if in.State == StateRunning && in.machine != nil {
		in.LastUsed = time.Now()
		m.mu.Unlock()
		return in, nil
	}
	m.mu.Unlock()

	snapDir := filepath.Join(in.WorkDir, "snap-wake")
	_ = os.RemoveAll(snapDir)
	pkg, err := m.cfg.SnapStore.Get(ctx, snapshot.KeyFor(k.User, k.App), snapDir)
	if err != nil {
		return nil, fmt.Errorf("download snapshot: %w", err)
	}

	mach, addr, err := m.restoreFromPackage(ctx, in, pkg)
	if err != nil {
		return nil, err
	}

	m.mu.Lock()
	in.State = StateRunning
	in.machine = mach
	in.Addr = addr
	in.LastUsed = time.Now()
	m.mu.Unlock()
	return in, nil
}

func (m *Manager) restoreFromPackage(ctx context.Context, in *Instance, pkg snapshot.Package) (machine, string, error) {
	return m.rt.Restore(ctx, RestoreSpec{
		FirecrackerBin: m.cfg.FirecrackerBin,
		WorkDir:        in.WorkDir,
		StatePath:      pkg.StatePath,
		MemPath:        pkg.MemPath,
		RootfsSrc:      pkg.RootfsPath,
		RootfsDst:      in.Rootfs,
		TapName:        in.TapName,
		HostIP:         in.HostIP,
		GuestIP:        in.GuestIP,
	})
}

// Stop tears down an instance (running or sleeping) and deletes its snapshot.
func (m *Manager) Stop(user, app string) error {
	k := InstanceKey{User: user, App: app}
	m.mu.Lock()
	in, ok := m.inst[k]
	if ok {
		delete(m.inst, k)
	}
	m.mu.Unlock()
	if !ok {
		return nil
	}
	var err error
	if in.machine != nil {
		err = in.machine.Stop()
	}
	_ = firecracker.DeleteTap(in.TapName)
	if m.cfg.SnapStore != nil {
		_ = m.cfg.SnapStore.Delete(context.Background(), snapshot.KeyFor(user, app))
	}
	_ = os.RemoveAll(in.WorkDir)
	return err
}

// Addr ensures the instance (app may be genid.AgentApp form) and returns its SSH address.
func (m *Manager) Addr(user, app string) (string, error) {
	in, err := m.Ensure(context.Background(), user, app)
	if err != nil {
		return "", err
	}
	return in.Addr, nil
}

// SetNoIdle prevents idle snapshot-sleep (used while a generation is draining
// or freshly booted during cutover).
func (m *Manager) SetNoIdle(user, app string, noIdle bool) {
	k := InstanceKey{User: user, App: app}
	m.mu.Lock()
	defer m.mu.Unlock()
	if in, ok := m.inst[k]; ok {
		in.noIdle = noIdle
		in.LastUsed = time.Now()
	}
}

// Touch updates LastUsed so idle sleep is deferred.
func (m *Manager) Touch(user, app string) {
	k := InstanceKey{User: user, App: app}
	m.mu.Lock()
	defer m.mu.Unlock()
	if in, ok := m.inst[k]; ok {
		in.LastUsed = time.Now()
	}
}

func (m *Manager) idleLoop() {
	t := time.NewTicker(30 * time.Second)
	defer t.Stop()
	for {
		select {
		case <-m.stop:
			return
		case <-t.C:
			m.sleepIdle()
		}
	}
}

func (m *Manager) sleepIdle() {
	if m.cfg.SnapStore == nil || m.cfg.IdleTimeout <= 0 {
		return
	}
	cutoff := time.Now().Add(-m.cfg.IdleTimeout)
	m.mu.Lock()
	var due []InstanceKey
	for k, in := range m.inst {
		if in.State == StateRunning && !in.noIdle && in.LastUsed.Before(cutoff) {
			due = append(due, k)
		}
	}
	m.mu.Unlock()
	for _, k := range due {
		_ = m.Sleep(context.Background(), k.User, k.App)
	}
}

// Close stops the idle loop and all instances.
func (m *Manager) Close() error {
	select {
	case <-m.stop:
	default:
		close(m.stop)
	}
	m.mu.Lock()
	keys := make([]InstanceKey, 0, len(m.inst))
	for k := range m.inst {
		keys = append(keys, k)
	}
	m.mu.Unlock()
	var first error
	for _, k := range keys {
		if err := m.Stop(k.User, k.App); err != nil && first == nil {
			first = err
		}
	}
	return first
}

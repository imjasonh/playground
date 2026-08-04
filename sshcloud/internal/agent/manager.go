// Package agent manages app microVM instances on a host.
package agent

import (
	"context"
	"fmt"
	"net"
	"os"
	"path/filepath"
	"sync"
	"time"

	"github.com/imjasonh/playground/sshcloud/internal/firecracker"
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
	machine  *firecracker.Machine
	snapKey  string // blob store key when sleeping
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
	// SnapStore persists sleep snapshots (required for sleep). Local or GCS.
	SnapStore snapshot.Store
}

// Manager boots, sleeps, and wakes Firecracker instances.
type Manager struct {
	cfg  Config
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
	if cfg.KernelPath == "" || cfg.BaseRootfs == "" {
		return nil, fmt.Errorf("KernelPath and BaseRootfs required")
	}
	if cfg.SubnetBase == "" {
		cfg.SubnetBase = "172.16"
	}
	// IdleTimeout 0 disables auto-sleep (callers set a positive default, e.g. 5m).
	if err := os.MkdirAll(cfg.WorkDir, 0o755); err != nil {
		return nil, err
	}
	m := &Manager{
		cfg:  cfg,
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

	in, err := m.bootCold(ctx, k, n)
	if err != nil {
		return nil, err
	}
	m.mu.Lock()
	m.inst[k] = in
	m.mu.Unlock()
	return in, nil
}

func (m *Manager) bootCold(ctx context.Context, k InstanceKey, n int) (*Instance, error) {
	if !firecracker.Available() {
		return nil, fmt.Errorf("firecracker requires /dev/kvm (not available on this host)")
	}
	dir := filepath.Join(m.cfg.WorkDir, fmt.Sprintf("vm-%d", n))
	if err := os.MkdirAll(dir, 0o755); err != nil {
		return nil, err
	}
	rootfsPath := filepath.Join(dir, "rootfs.ext4")
	if err := rootfs.Clone(m.cfg.BaseRootfs, rootfsPath); err != nil {
		return nil, err
	}
	if m.cfg.CAPubPath != "" {
		if err := rootfs.InjectFile(rootfsPath, m.cfg.CAPubPath, "ca.pub", "0644"); err != nil {
			return nil, fmt.Errorf("inject CA: %w", err)
		}
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
	bootArgs += " init=/fortune -- -listen 0.0.0.0:22 -ca /ca.pub"

	sock := filepath.Join(dir, "firecracker.sock")
	logPath := filepath.Join(dir, "firecracker.log")
	machine, err := firecracker.Start(ctx, firecracker.Config{
		FirecrackerBin: m.cfg.FirecrackerBin,
		SocketPath:     sock,
		KernelPath:     m.cfg.KernelPath,
		RootfsPath:     rootfsPath,
		BootArgs:       bootArgs,
		VCPUs:          1,
		MemMiB:         128,
		TapDevice:      tapName,
		GuestMAC:       mac,
		LogPath:        logPath,
	})
	if err != nil {
		_ = firecracker.DeleteTap(tapName)
		return nil, err
	}

	addr := net.JoinHostPort(guestIP, "22")
	if err := firecracker.WaitTCP(ctx, addr, 30*time.Second); err != nil {
		_ = machine.Stop()
		_ = firecracker.DeleteTap(tapName)
		return nil, fmt.Errorf("guest SSH not ready: %w (see %s)", err, logPath)
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
		machine:  machine,
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
	machine := in.machine
	m.mu.Unlock()

	snapDir := filepath.Join(in.WorkDir, "snap")
	_ = os.RemoveAll(snapDir)
	pkg := snapshot.NewPackageDir(snapDir)
	if err := os.MkdirAll(snapDir, 0o755); err != nil {
		return err
	}
	// Copy live rootfs into package (mutable disk state).
	if err := rootfs.Clone(in.Rootfs, pkg.RootfsPath); err != nil {
		return fmt.Errorf("clone rootfs for snap: %w", err)
	}
	files := firecracker.SnapshotFiles{StatePath: pkg.StatePath, MemPath: pkg.MemPath}
	if err := machine.SnapshotThenKill(ctx, files); err != nil {
		return err
	}

	meta := snapshot.Meta{
		User:      user,
		App:       app,
		GuestIP:   in.GuestIP,
		TapName:   in.TapName,
		GuestMAC:  in.GuestMAC,
		HostIP:    in.HostIP,
		CreatedAt: time.Now().UTC(),
	}
	if err := pkg.WriteMeta(meta); err != nil {
		return err
	}
	key := snapshot.KeyFor(user, app)
	if err := m.cfg.SnapStore.Put(ctx, key, pkg); err != nil {
		// Best-effort wake from the local package so the instance isn't lost.
		if restored, wakeErr := m.restoreFromPackage(ctx, in, pkg); wakeErr == nil {
			m.mu.Lock()
			in.machine = restored
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

func (m *Manager) wake(ctx context.Context, k InstanceKey) (*Instance, error) {
	if !firecracker.Available() {
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

	machine, err := m.restoreFromPackage(ctx, in, pkg)
	if err != nil {
		return nil, err
	}

	m.mu.Lock()
	in.State = StateRunning
	in.machine = machine
	in.Addr = net.JoinHostPort(in.GuestIP, "22")
	in.LastUsed = time.Now()
	m.mu.Unlock()
	return in, nil
}

func (m *Manager) restoreFromPackage(ctx context.Context, in *Instance, pkg snapshot.Package) (*firecracker.Machine, error) {
	if err := rootfs.Clone(pkg.RootfsPath, in.Rootfs); err != nil {
		return nil, err
	}
	// Ensure TAP still exists (recreate if host restarted; CreateTap is idempotent).
	if err := firecracker.CreateTap(in.TapName, in.HostIP, 24); err != nil {
		return nil, fmt.Errorf("recreate tap: %w", err)
	}

	sock := filepath.Join(in.WorkDir, "firecracker.sock")
	logPath := filepath.Join(in.WorkDir, "firecracker-wake.log")
	machine, err := firecracker.Restore(ctx, firecracker.RestoreConfig{
		FirecrackerBin:    m.cfg.FirecrackerBin,
		SocketPath:        sock,
		Snapshot:          firecracker.SnapshotFiles{StatePath: pkg.StatePath, MemPath: pkg.MemPath},
		LogPath:           logPath,
		ResumeImmediately: false,
	})
	if err != nil {
		return nil, err
	}
	if err := machine.Resume(ctx); err != nil {
		_ = machine.Kill()
		return nil, fmt.Errorf("resume: %w", err)
	}
	addr := net.JoinHostPort(in.GuestIP, "22")
	if err := firecracker.WaitTCP(ctx, addr, 30*time.Second); err != nil {
		_ = machine.Kill()
		return nil, fmt.Errorf("guest SSH not ready after wake: %w (see %s)", err, logPath)
	}
	return machine, nil
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
	return err
}

// Addr implements gateway DialFunc shape (Ensure + return addr).
func (m *Manager) Addr(user, app string) (string, error) {
	in, err := m.Ensure(context.Background(), user, app)
	if err != nil {
		return "", err
	}
	return in.Addr, nil
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
		if in.State == StateRunning && in.LastUsed.Before(cutoff) {
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
	close(m.stop)
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

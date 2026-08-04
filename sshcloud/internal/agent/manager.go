// Package agent manages app microVM instances on a host.
package agent

import (
	"context"
	"crypto/sha256"
	"fmt"
	"net"
	"os"
	"os/exec"
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
	StateFailed   State = "failed"
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
	Image    string
	Tier     string
	machine  machine
	snapKey  string
	noIdle   bool
	relay    *tcpRelay
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
	// RelayHost is the agent's VPC IP. When set, Ensure returns a host-side
	// TCP relay in RelayPortMin..RelayPortMax instead of a TAP-local guest IP.
	RelayHost    string
	RelayPortMin int
	RelayPortMax int
	// AllowedRegistries constrains OCI pull hosts to prevent control-plane
	// requests from becoming arbitrary SSRF. Empty is local-dev only.
	AllowedRegistries []string
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
	// Tier selects guest resources: tiny (1 vCPU/128 MiB) or small
	// (2 vCPU/512 MiB). Empty defaults to tiny.
	Tier string
	// NoIdle holds the instance awake for an active or draining SSH session.
	NoIdle bool
}

// Manager boots, sleeps, wakes, and migrates Firecracker instances.
type Manager struct {
	cfg  Config
	rt   Runtime
	mu   sync.Mutex
	inst map[InstanceKey]*Instance
	ops  map[InstanceKey]*sync.Mutex
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
	if cfg.RelayHost != "" {
		if cfg.RelayPortMin == 0 {
			cfg.RelayPortMin = 20_000
		}
		if cfg.RelayPortMax == 0 {
			cfg.RelayPortMax = 29_999
		}
		if cfg.RelayPortMin < 1 || cfg.RelayPortMax > 65_535 || cfg.RelayPortMin > cfg.RelayPortMax {
			return nil, fmt.Errorf("invalid relay port range %d-%d", cfg.RelayPortMin, cfg.RelayPortMax)
		}
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
		ops:  make(map[InstanceKey]*sync.Mutex),
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
	if img := strings.TrimSpace(opt.Image); img != "" {
		if err := image.ValidateDigestPinned(img); err != nil {
			return nil, err
		}
		opt.Image = img
	}
	if strings.TrimSpace(opt.Tier) != "" {
		tier, _, _, err := tierResources(opt.Tier)
		if err != nil {
			return nil, err
		}
		opt.Tier = tier
	}

	op := m.instanceLock(k)
	op.Lock()
	defer op.Unlock()

	m.mu.Lock()
	if in, ok := m.inst[k]; ok {
		if err := compatibleInstance(in, opt); err != nil {
			m.mu.Unlock()
			return nil, err
		}
		switch in.State {
		case StateRunning:
			in.LastUsed = time.Now()
			in.noIdle = opt.NoIdle
			m.mu.Unlock()
			return instanceCopy(in), nil
		case StateSleeping:
			in.noIdle = opt.NoIdle
			m.mu.Unlock()
			return m.wake(ctx, k)
		case StateFailed:
			delete(m.inst, k)
		}
	}
	m.seq++
	n := m.seq
	m.mu.Unlock()

	if m.cfg.SnapStore != nil {
		has, err := m.cfg.SnapStore.Has(ctx, snapshot.KeyFor(user, app))
		if err != nil {
			return nil, fmt.Errorf("check snapshot: %w", err)
		}
		if has {
			return m.adopt(ctx, k, n, opt)
		}
	}

	if opt.Tier == "" {
		opt.Tier = "tiny"
	}
	in, err := m.bootCold(ctx, k, n, opt)
	if err != nil {
		return nil, err
	}
	if err := ctx.Err(); err != nil {
		_ = in.relay.Close()
		_ = in.machine.Stop()
		_ = firecracker.DeleteTap(in.TapName)
		_ = os.RemoveAll(in.WorkDir)
		return nil, err
	}
	m.mu.Lock()
	m.inst[k] = in
	m.mu.Unlock()
	return instanceCopy(in), nil
}

func (m *Manager) instanceLock(k InstanceKey) *sync.Mutex {
	m.mu.Lock()
	defer m.mu.Unlock()
	op := m.ops[k]
	if op == nil {
		op = &sync.Mutex{}
		m.ops[k] = op
	}
	return op
}

func compatibleInstance(in *Instance, opt EnsureOpts) error {
	if opt.Image != "" && in.Image != opt.Image {
		return fmt.Errorf("instance %s already uses image %q, not %q", in.Key, in.Image, opt.Image)
	}
	currentTier := in.Tier
	if currentTier == "" {
		currentTier = "tiny"
	}
	if opt.Tier != "" && opt.Tier != currentTier {
		return fmt.Errorf("instance %s already uses tier %q, not %q", in.Key, currentTier, opt.Tier)
	}
	return nil
}

func instanceCopy(in *Instance) *Instance {
	if in == nil {
		return nil
	}
	cp := *in
	cp.machine = nil
	cp.relay = nil
	return &cp
}

func tierResources(tier string) (normalized string, vcpus, memMiB int64, err error) {
	switch strings.ToLower(strings.TrimSpace(tier)) {
	case "", "tiny":
		return "tiny", 1, 128, nil
	case "small":
		return "small", 2, 512, nil
	default:
		return "", 0, 0, fmt.Errorf("unknown tier %q (want tiny or small)", tier)
	}
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
	if err := image.ValidateAllowedRegistry(imageRef, m.cfg.AllowedRegistries); err != nil {
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

func (m *Manager) bootCold(ctx context.Context, k InstanceKey, n int, opt EnsureOpts) (_ *Instance, retErr error) {
	imageRef := strings.TrimSpace(opt.Image)
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
	resourceID := instanceResourceID(k)
	dir := filepath.Join(m.cfg.WorkDir, "vm-"+resourceID)
	if err := os.RemoveAll(dir); err != nil {
		return nil, err
	}
	if err := os.MkdirAll(dir, 0o755); err != nil {
		return nil, err
	}
	defer func() {
		if retErr != nil {
			_ = os.RemoveAll(dir)
		}
	}()
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
		if err := rootfs.InjectFile(rootfsPath, m.cfg.CAPubPath, "/run/platform/ssh_user_ca.pub", "0644"); err != nil {
			return nil, fmt.Errorf("inject canonical CA path: %w", err)
		}
	}
	initArgs, err := m.prepareGuestInit(rootfsPath, resolved.Spec)
	if err != nil {
		return nil, err
	}

	tapName := "fc-" + resourceID
	var hostIP, guestIP string
	for i := 0; i < 200; i++ {
		octet := (n+i)%200 + 1
		candidateHost := fmt.Sprintf("%s.%d.1", m.cfg.SubnetBase, octet)
		candidateGuest := fmt.Sprintf("%s.%d.2", m.cfg.SubnetBase, octet)
		if err := m.checkResourceConflict(k, rootfsPath, tapName, candidateGuest, candidateHost); err == nil {
			hostIP, guestIP = candidateHost, candidateGuest
			break
		}
	}
	if hostIP == "" {
		return nil, fmt.Errorf("no guest subnet available for %s", k)
	}
	if err := firecracker.CreateTap(tapName, hostIP, 24); err != nil {
		return nil, fmt.Errorf("create tap: %w (agent needs CAP_NET_ADMIN)", err)
	}
	defer func() {
		if retErr != nil {
			_ = firecracker.DeleteTap(tapName)
		}
	}()

	resourceHash := sha256.Sum256([]byte(k.User + "\x00" + k.App))
	mac := fmt.Sprintf("AA:FC:00:%02x:%02x:%02x", resourceHash[0], resourceHash[1], resourceHash[2])
	bootArgs := firecracker.GuestBootArgs(guestIP, hostIP, "255.255.255.0", k.App)
	bootArgs += " " + initArgs

	_, vcpus, memMiB, _ := tierResources(opt.Tier)
	mach, addr, err := m.rt.Boot(ctx, BootSpec{
		FirecrackerBin: m.cfg.FirecrackerBin,
		WorkDir:        dir,
		KernelPath:     m.cfg.KernelPath,
		RootfsPath:     rootfsPath,
		BootArgs:       bootArgs,
		TapName:        tapName,
		GuestMAC:       mac,
		GuestIP:        guestIP,
		VCPUs:          vcpus,
		MemMiB:         memMiB,
	})
	if err != nil {
		return nil, err
	}
	var relay *tcpRelay
	if m.cfg.RelayHost != "" {
		sum := sha256.Sum256([]byte(k.User + "\x00" + k.App))
		offset := int(sum[6])<<8 | int(sum[7])
		relay, err = startTCPRelay(m.cfg.RelayHost, addr, m.cfg.RelayPortMin, m.cfg.RelayPortMax, offset)
		if err != nil {
			_ = mach.Stop()
			return nil, fmt.Errorf("start SSH relay: %w", err)
		}
		addr = relay.Addr()
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
		Image:    imageRef,
		Tier:     opt.Tier,
		machine:  mach,
		noIdle:   opt.NoIdle,
		relay:    relay,
	}, nil
}

func instanceResourceID(k InstanceKey) string {
	sum := sha256.Sum256([]byte(k.User + "\x00" + k.App))
	// 12 hex characters keeps TAP names at Linux's 15-byte IFNAMSIZ limit.
	return fmt.Sprintf("%x", sum[:6])
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

// Ready verifies host prerequisites needed for a cold boot. Health checks use
// this instead of reporting ready before KVM, assets, or rootfs tools exist.
func (m *Manager) Ready() error {
	if !m.rt.Available() {
		return fmt.Errorf("/dev/kvm is unavailable")
	}
	for label, file := range map[string]string{
		"kernel":    m.cfg.KernelPath,
		"guestinit": m.cfg.GuestInitPath,
	} {
		st, err := os.Stat(file)
		if err != nil {
			return fmt.Errorf("%s %q: %w", label, file, err)
		}
		if !st.Mode().IsRegular() {
			return fmt.Errorf("%s %q is not a regular file", label, file)
		}
	}
	fc := m.cfg.FirecrackerBin
	if fc == "" {
		fc = "firecracker"
	}
	if _, err := exec.LookPath(fc); err != nil {
		return fmt.Errorf("firecracker %q: %w", fc, err)
	}
	for _, tool := range []string{"ip", "mkfs.ext4", "debugfs"} {
		if _, err := exec.LookPath(tool); err != nil {
			return fmt.Errorf("required tool %q: %w", tool, err)
		}
	}
	return nil
}

// Sleep snapshots a running instance, uploads it, and frees the VMM (keeps TAP).
func (m *Manager) Sleep(ctx context.Context, user, app string) error {
	k := InstanceKey{User: user, App: app}
	if m.cfg.SnapStore == nil {
		return fmt.Errorf("snapshot store not configured")
	}
	op := m.instanceLock(k)
	op.Lock()
	defer op.Unlock()

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
	if in.noIdle {
		m.mu.Unlock()
		return fmt.Errorf("instance %s is held awake by an active operation", k)
	}
	mach := in.machine
	m.mu.Unlock()

	snapDir := filepath.Join(in.WorkDir, "snap")
	_ = os.RemoveAll(snapDir)
	pkg := snapshot.NewPackageDir(snapDir)
	if err := os.MkdirAll(snapDir, 0o755); err != nil {
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
		Image:      in.Image,
		Tier:       in.Tier,
		CreatedAt:  time.Now().UTC(),
	}
	if err := pkg.WriteMeta(meta); err != nil {
		return err
	}
	if err := mach.Pause(ctx); err != nil {
		return fmt.Errorf("pause: %w", err)
	}
	if err := rootfs.Clone(in.Rootfs, pkg.RootfsPath); err != nil {
		_ = mach.Resume(ctx)
		return fmt.Errorf("clone rootfs for snap: %w", err)
	}
	files := firecracker.SnapshotFiles{StatePath: pkg.StatePath, MemPath: pkg.MemPath}
	if err := mach.CreateSnapshot(ctx, files); err != nil {
		_ = mach.Resume(ctx)
		return fmt.Errorf("create snapshot: %w", err)
	}
	if err := mach.Kill(); err != nil {
		return fmt.Errorf("kill after snapshot: %w", err)
	}

	key := snapshot.KeyFor(user, app)
	if err := m.cfg.SnapStore.Put(ctx, key, pkg); err != nil {
		if restored, addr, wakeErr := m.restoreFromPackage(ctx, in, pkg); wakeErr == nil {
			if in.relay != nil {
				addr = in.relay.Addr()
			}
			m.mu.Lock()
			in.machine = restored
			in.Addr = addr
			in.State = StateRunning
			m.mu.Unlock()
		} else {
			m.mu.Lock()
			in.machine = nil
			in.State = StateFailed
			m.mu.Unlock()
			return fmt.Errorf("upload snapshot: %w (restore also failed: %v)", err, wakeErr)
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
	op := m.instanceLock(k)
	op.Lock()
	defer op.Unlock()
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

	_ = in.relay.Close()
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
	op := m.instanceLock(k)
	op.Lock()
	defer op.Unlock()

	m.mu.Lock()
	if in, ok := m.inst[k]; ok {
		switch in.State {
		case StateRunning:
			in.LastUsed = time.Now()
			m.mu.Unlock()
			return instanceCopy(in), nil
		case StateSleeping:
			m.mu.Unlock()
			return m.wake(ctx, k)
		case StateFailed:
			delete(m.inst, k)
		}
	}
	m.seq++
	n := m.seq
	m.mu.Unlock()

	return m.adopt(ctx, k, n, EnsureOpts{})
}

func (m *Manager) adopt(ctx context.Context, k InstanceKey, n int, opt EnsureOpts) (*Instance, error) {
	snapDir := filepath.Join(m.cfg.WorkDir, fmt.Sprintf("adopt-%d", n))
	_ = os.RemoveAll(snapDir)
	defer os.RemoveAll(snapDir)
	pkg, err := m.cfg.SnapStore.Get(ctx, snapshot.KeyFor(k.User, k.App), snapDir)
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
	if meta.User != k.User || meta.App != k.App {
		return nil, fmt.Errorf("snapshot identity mismatch: got %s/%s, want %s", meta.User, meta.App, k)
	}
	tier, _, _, err := tierResources(meta.Tier)
	if err != nil {
		return nil, fmt.Errorf("snapshot tier: %w", err)
	}
	meta.Tier = tier
	if opt.Image != "" && meta.Image != opt.Image {
		return nil, fmt.Errorf("snapshot image %q does not match requested %q", meta.Image, opt.Image)
	}
	if opt.Tier != "" && meta.Tier != opt.Tier {
		return nil, fmt.Errorf("snapshot tier %q does not match requested %q", meta.Tier, opt.Tier)
	}

	// Firecracker snapshots embed absolute rootfs + TAP names. Recreate those
	// exact paths before snapshot/load. Paths and TAP names are deterministic
	// from the instance identity so snapshot metadata cannot select host paths.
	resourceID := instanceResourceID(k)
	dir := filepath.Join(m.cfg.WorkDir, "vm-"+resourceID)
	rootfsPath := filepath.Join(dir, "rootfs.ext4")
	tapName := "fc-" + resourceID
	if meta.RootfsPath != rootfsPath {
		return nil, fmt.Errorf("snapshot rootfs path %q does not match expected %q", meta.RootfsPath, rootfsPath)
	}
	if meta.TapName != tapName {
		return nil, fmt.Errorf("snapshot TAP %q does not match expected %q", meta.TapName, tapName)
	}
	if meta.GuestIP == "" || meta.HostIP == "" || meta.GuestMAC == "" {
		return nil, fmt.Errorf("snapshot network metadata is incomplete")
	}
	if err := m.validateSnapshotNetwork(k, meta); err != nil {
		return nil, err
	}
	if err := m.checkResourceConflict(k, rootfsPath, tapName, meta.GuestIP, meta.HostIP); err != nil {
		return nil, err
	}
	if err := os.MkdirAll(dir, 0o755); err != nil {
		return nil, err
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
		snapKey:  snapshot.KeyFor(k.User, k.App),
		LastUsed: time.Now(),
		Image:    meta.Image,
		Tier:     meta.Tier,
		noIdle:   opt.NoIdle,
	}

	mach, addr, err := m.restoreFromPackage(ctx, in, pkg)
	if err != nil {
		_ = os.RemoveAll(dir)
		return nil, err
	}
	if m.cfg.RelayHost != "" {
		sum := sha256.Sum256([]byte(k.User + "\x00" + k.App))
		offset := int(sum[6])<<8 | int(sum[7])
		relay, relayErr := startTCPRelay(m.cfg.RelayHost, addr, m.cfg.RelayPortMin, m.cfg.RelayPortMax, offset)
		if relayErr != nil {
			_ = mach.Stop()
			_ = os.RemoveAll(dir)
			return nil, fmt.Errorf("start SSH relay: %w", relayErr)
		}
		in.relay = relay
		addr = relay.Addr()
	}
	in.machine = mach
	in.Addr = addr
	in.State = StateRunning
	if err := ctx.Err(); err != nil {
		_ = in.relay.Close()
		_ = mach.Stop()
		_ = firecracker.DeleteTap(tapName)
		_ = os.RemoveAll(dir)
		return nil, err
	}

	m.mu.Lock()
	m.inst[k] = in
	m.mu.Unlock()
	return instanceCopy(in), nil
}

func (m *Manager) checkResourceConflict(k InstanceKey, rootfsPath, tapName, guestIP, hostIP string) error {
	m.mu.Lock()
	defer m.mu.Unlock()
	for otherKey, in := range m.inst {
		if otherKey == k {
			continue
		}
		if in.Rootfs == rootfsPath || in.TapName == tapName || in.GuestIP == guestIP || in.HostIP == hostIP {
			return fmt.Errorf("snapshot resources for %s collide with instance %s", k, otherKey)
		}
	}
	return nil
}

func (m *Manager) validateSnapshotNetwork(k InstanceKey, meta snapshot.Meta) error {
	host := net.ParseIP(meta.HostIP)
	guest := net.ParseIP(meta.GuestIP)
	if host == nil || guest == nil || host.To4() == nil || guest.To4() == nil {
		return fmt.Errorf("snapshot has invalid guest network addresses")
	}
	host4, guest4 := host.To4(), guest.To4()
	if host4[0] != guest4[0] || host4[1] != guest4[1] || host4[2] != guest4[2] ||
		host4[3] != 1 || guest4[3] != 2 ||
		!strings.HasPrefix(meta.HostIP, m.cfg.SubnetBase+".") {
		return fmt.Errorf("snapshot guest network %s/%s is outside configured subnet base %s", meta.HostIP, meta.GuestIP, m.cfg.SubnetBase)
	}
	sum := sha256.Sum256([]byte(k.User + "\x00" + k.App))
	wantMAC := fmt.Sprintf("AA:FC:00:%02x:%02x:%02x", sum[0], sum[1], sum[2])
	if !strings.EqualFold(meta.GuestMAC, wantMAC) {
		return fmt.Errorf("snapshot MAC %q does not match expected %q", meta.GuestMAC, wantMAC)
	}
	return nil
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
		return instanceCopy(in), nil
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
	if err := ctx.Err(); err != nil {
		_ = mach.Stop()
		return nil, err
	}
	if in.relay != nil {
		addr = in.relay.Addr()
	} else if m.cfg.RelayHost != "" {
		sum := sha256.Sum256([]byte(k.User + "\x00" + k.App))
		offset := int(sum[6])<<8 | int(sum[7])
		relay, relayErr := startTCPRelay(m.cfg.RelayHost, addr, m.cfg.RelayPortMin, m.cfg.RelayPortMax, offset)
		if relayErr != nil {
			_ = mach.Stop()
			return nil, fmt.Errorf("start SSH relay: %w", relayErr)
		}
		in.relay = relay
		addr = relay.Addr()
	}

	m.mu.Lock()
	in.State = StateRunning
	in.machine = mach
	in.Addr = addr
	in.LastUsed = time.Now()
	m.mu.Unlock()
	return instanceCopy(in), nil
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
	ctx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
	defer cancel()
	return m.StopContext(ctx, user, app)
}

// StopContext is Stop with cancellation for durable snapshot deletion.
func (m *Manager) StopContext(ctx context.Context, user, app string) error {
	k := InstanceKey{User: user, App: app}
	op := m.instanceLock(k)
	op.Lock()
	defer op.Unlock()
	m.mu.Lock()
	in, ok := m.inst[k]
	m.mu.Unlock()
	if !ok {
		return nil
	}
	if m.cfg.SnapStore != nil {
		if err := m.cfg.SnapStore.Delete(ctx, snapshot.KeyFor(user, app)); err != nil {
			return fmt.Errorf("delete snapshot: %w", err)
		}
	}
	m.mu.Lock()
	delete(m.inst, k)
	m.mu.Unlock()
	var err error
	_ = in.relay.Close()
	if in.machine != nil {
		err = in.machine.Stop()
	}
	_ = firecracker.DeleteTap(in.TapName)
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
func (m *Manager) SetNoIdle(user, app string, noIdle bool) error {
	k := InstanceKey{User: user, App: app}
	op := m.instanceLock(k)
	op.Lock()
	defer op.Unlock()
	m.mu.Lock()
	defer m.mu.Unlock()
	if in, ok := m.inst[k]; ok {
		in.noIdle = noIdle
		in.LastUsed = time.Now()
		return nil
	}
	return fmt.Errorf("instance %s not found", k)
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

// Close stops the idle loop and local VMMs. When a snapshot store is
// configured, running instances are snapshotted and evicted without deleting
// their durable package so a replacement agent can recover them on Ensure.
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
		if m.cfg.SnapStore != nil {
			_ = m.SetNoIdle(k.User, k.App, false)
			st, ok := m.Status(k.User, k.App)
			if ok && st.State == StateRunning {
				ctx, cancel := context.WithTimeout(context.Background(), 2*time.Minute)
				err := m.Sleep(ctx, k.User, k.App)
				cancel()
				if err != nil {
					if first == nil {
						first = err
					}
					_ = m.shutdownLocal(k)
					continue
				}
			}
			if err := m.Evict(k.User, k.App); err != nil && first == nil {
				first = err
			}
			continue
		}
		if err := m.Stop(k.User, k.App); err != nil && first == nil {
			first = err
		}
	}
	return first
}

func (m *Manager) shutdownLocal(k InstanceKey) error {
	op := m.instanceLock(k)
	op.Lock()
	defer op.Unlock()
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
	_ = in.relay.Close()
	if in.machine != nil {
		err = in.machine.Stop()
	}
	_ = firecracker.DeleteTap(in.TapName)
	_ = os.RemoveAll(in.WorkDir)
	return err
}

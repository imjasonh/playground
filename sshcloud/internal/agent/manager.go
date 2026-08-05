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
	"runtime"
	"sort"
	"strconv"
	"strings"
	"sync"
	"syscall"
	"time"

	"github.com/imjasonh/playground/sshcloud/internal/firecracker"
	"github.com/imjasonh/playground/sshcloud/internal/genid"
	"github.com/imjasonh/playground/sshcloud/internal/guestinit"
	"github.com/imjasonh/playground/sshcloud/internal/hostkey"
	"github.com/imjasonh/playground/sshcloud/internal/image"
	"github.com/imjasonh/playground/sshcloud/internal/rootfs"
	"github.com/imjasonh/playground/sshcloud/internal/snapshot"
	"golang.org/x/crypto/ssh"
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

// Resources are Firecracker capacity units.
type Resources struct {
	VCPUs  int64 `json:"vcpus"`
	MemMiB int64 `json:"mem_mib"`
}

// Capacity is one host's current allocatable resource view.
type Capacity struct {
	Total    Resources `json:"total"`
	Used     Resources `json:"used"`
	Reserved Resources `json:"reserved"`
	Cordoned bool      `json:"cordoned"`
}

// ErrCapacity means the host cannot fit another running generation.
type ErrCapacity struct {
	Need, Available Resources
}

func (e ErrCapacity) Error() string {
	return fmt.Sprintf("insufficient host capacity: need %d vCPU/%d MiB, available %d vCPU/%d MiB",
		e.Need.VCPUs, e.Need.MemMiB, e.Available.VCPUs, e.Available.MemMiB)
}

// ErrCordoned means the host is draining and rejects new boots/restores.
type ErrCordoned struct{}

func (ErrCordoned) Error() string { return "host is cordoned" }

// Instance is a live or sleeping microVM endpoint.
type Instance struct {
	Key              InstanceKey
	State            State
	Addr             string
	GuestIP          string
	HostIP           string
	TapName          string
	GuestMAC         string
	Rootfs           string
	WorkDir          string
	LastUsed         time.Time
	Image            string
	Tier             string
	VCPUs            int64
	MemMiB           int64
	SSHHostPublicKey string
	machine          machine
	snapKey          string
	noIdle           bool
	relay            *tcpRelay
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
	// CapacityVCPUs/CapacityMemMiB are allocatable guest resources. Zero
	// detects the host and reserves 1 GiB of memory for the host agent.
	CapacityVCPUs  int64
	CapacityMemMiB int64
	// PlatformVersion fences Firecracker snapshots to compatible kernel/VMM
	// assets during host rollout.
	PlatformVersion string
	CPUTemplate     string
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
	// CordonEpoch permits rollback only for the operation that cordoned host.
	CordonEpoch string
}

// Manager boots, sleeps, wakes, and migrates Firecracker instances.
type Manager struct {
	cfg  Config
	rt   Runtime
	mu   sync.Mutex
	inst map[InstanceKey]*Instance
	ops  map[InstanceKey]*sync.Mutex
	// reserved fences resources during slow boot/restore before inst is
	// published, so concurrent instances cannot claim the same IP or TAP.
	reserved         map[string]InstanceKey
	capacityReserved map[InstanceKey]Resources
	lifecyclePending map[InstanceKey]bool
	capacity         Resources
	cordoned         bool
	cordonEpoch      string
	seq              int
	stop             chan struct{}
	closed           bool
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
	if err := os.MkdirAll(cfg.WorkDir, 0o700); err != nil {
		return nil, err
	}
	if err := os.Chmod(cfg.WorkDir, 0o700); err != nil {
		return nil, err
	}
	if cfg.CapacityVCPUs <= 0 {
		cfg.CapacityVCPUs = int64(runtime.NumCPU())
	}
	if cfg.CapacityMemMiB <= 0 {
		cfg.CapacityMemMiB = detectedGuestMemoryMiB()
	}
	m := &Manager{
		cfg:              cfg,
		rt:               rt,
		inst:             make(map[InstanceKey]*Instance),
		ops:              make(map[InstanceKey]*sync.Mutex),
		reserved:         make(map[string]InstanceKey),
		capacityReserved: make(map[InstanceKey]Resources),
		lifecyclePending: make(map[InstanceKey]bool),
		capacity:         Resources{VCPUs: cfg.CapacityVCPUs, MemMiB: cfg.CapacityMemMiB},
		stop:             make(chan struct{}),
	}
	if cordonBytes, err := os.ReadFile(filepath.Join(cfg.WorkDir, ".cordoned")); err == nil {
		m.cordoned = true
		m.cordonEpoch = strings.TrimSpace(string(cordonBytes))
	} else if !os.IsNotExist(err) {
		return nil, fmt.Errorf("read cordon state: %w", err)
	}
	if cfg.IdleTimeout > 0 && cfg.SnapStore != nil {
		go m.idleLoop()
	}
	return m, nil
}

func detectedGuestMemoryMiB() int64 {
	b, err := os.ReadFile("/proc/meminfo")
	if err == nil {
		for _, line := range strings.Split(string(b), "\n") {
			fields := strings.Fields(line)
			if len(fields) >= 2 && fields[0] == "MemTotal:" {
				kib, parseErr := strconv.ParseInt(fields[1], 10, 64)
				if parseErr == nil {
					mib := kib/1024 - 1024
					if mib >= 512 {
						return mib
					}
				}
			}
		}
	}
	return 512
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

	var stale *Instance
	m.mu.Lock()
	if m.closed {
		m.mu.Unlock()
		return nil, fmt.Errorf("agent manager is closed")
	}
	if in, ok := m.inst[k]; ok {
		if err := compatibleInstance(in, opt); err != nil {
			m.mu.Unlock()
			return nil, err
		}
		switch in.State {
		case StateRunning:
			if in.machine != nil && in.machine.Alive() {
				in.LastUsed = time.Now()
				in.noIdle = opt.NoIdle
				m.mu.Unlock()
				return instanceCopy(in), nil
			}
			stale = in
			if opt.Image == "" {
				opt.Image = in.Image
			}
			if opt.Tier == "" {
				opt.Tier = in.Tier
			}
			delete(m.inst, k)
		case StateSleeping:
			in.noIdle = opt.NoIdle
			m.mu.Unlock()
			return m.wake(ctx, k)
		case StateFailed:
			stale = in
			delete(m.inst, k)
		}
	}
	m.seq++
	n := m.seq
	m.mu.Unlock()
	if stale != nil {
		_ = stale.relay.Close()
		if stale.machine != nil {
			_ = stale.machine.Kill()
		}
		_ = firecracker.DeleteTap(stale.TapName)
		_ = os.RemoveAll(stale.WorkDir)
	}

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
		m.releaseResources(k)
		m.releaseCapacity(k)
		return nil, err
	}
	m.publishInstance(in)
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

func resourcesForTier(tier string) (Resources, error) {
	_, vcpus, memMiB, err := tierResources(tier)
	return Resources{VCPUs: vcpus, MemMiB: memMiB}, err
}

func (m *Manager) platformVersion() string {
	switch {
	case m.cfg.PlatformVersion == "":
		if m.cfg.CPUTemplate == "" {
			return ""
		}
		return "cpu=" + m.cfg.CPUTemplate
	case m.cfg.CPUTemplate == "":
		return m.cfg.PlatformVersion
	default:
		return m.cfg.PlatformVersion + ";cpu=" + m.cfg.CPUTemplate
	}
}

// ResourcesForTier returns the host capacity consumed by a tier.
func ResourcesForTier(tier string) (Resources, error) { return resourcesForTier(tier) }

func addResources(a, b Resources) Resources {
	return Resources{VCPUs: a.VCPUs + b.VCPUs, MemMiB: a.MemMiB + b.MemMiB}
}

func subResources(a, b Resources) Resources {
	return Resources{VCPUs: a.VCPUs - b.VCPUs, MemMiB: a.MemMiB - b.MemMiB}
}

func (m *Manager) reserveCapacity(k InstanceKey, tier, cordonEpoch string) error {
	need, err := resourcesForTier(tier)
	if err != nil {
		return err
	}
	m.mu.Lock()
	defer m.mu.Unlock()
	if m.cordoned && (cordonEpoch == "" || cordonEpoch != m.cordonEpoch) {
		return ErrCordoned{}
	}
	if _, ok := m.capacityReserved[k]; ok {
		return nil
	}
	view := m.capacityLocked()
	available := subResources(view.Total, addResources(view.Used, view.Reserved))
	if need.VCPUs > available.VCPUs || need.MemMiB > available.MemMiB {
		return ErrCapacity{Need: need, Available: available}
	}
	m.capacityReserved[k] = need
	return nil
}

func (m *Manager) releaseCapacity(k InstanceKey) {
	m.mu.Lock()
	defer m.mu.Unlock()
	delete(m.capacityReserved, k)
}

func (m *Manager) beginLifecycle(k InstanceKey, cordonEpoch string) error {
	m.mu.Lock()
	defer m.mu.Unlock()
	if m.cordoned && (cordonEpoch == "" || cordonEpoch != m.cordonEpoch) {
		return ErrCordoned{}
	}
	m.lifecyclePending[k] = true
	return nil
}

func (m *Manager) endLifecycle(k InstanceKey) {
	m.mu.Lock()
	defer m.mu.Unlock()
	delete(m.lifecyclePending, k)
}

func (m *Manager) capacityLocked() Capacity {
	view := Capacity{Total: m.capacity, Cordoned: m.cordoned}
	for _, in := range m.inst {
		if in.State == StateRunning && in.machine != nil {
			view.Used = addResources(view.Used, Resources{VCPUs: in.VCPUs, MemMiB: in.MemMiB})
		}
	}
	for _, reserved := range m.capacityReserved {
		view.Reserved = addResources(view.Reserved, reserved)
	}
	return view
}

// Capacity reports resources currently used and reserved.
func (m *Manager) Capacity() Capacity {
	m.mu.Lock()
	defer m.mu.Unlock()
	return m.capacityLocked()
}

// SetCordoned durably controls whether new boots/restores are admitted.
func (m *Manager) SetCordoned(cordoned bool) error {
	m.mu.Lock()
	defer m.mu.Unlock()
	path := filepath.Join(m.cfg.WorkDir, ".cordoned")
	if cordoned {
		if m.cordonEpoch == "" {
			m.cordonEpoch = genid.New()
		}
		tmp := path + ".tmp"
		if err := os.WriteFile(tmp, []byte(m.cordonEpoch+"\n"), 0o600); err != nil {
			return err
		}
		if err := os.Rename(tmp, path); err != nil {
			_ = os.Remove(tmp)
			return err
		}
	} else if err := os.Remove(path); err != nil && !os.IsNotExist(err) {
		return err
	}
	m.cordoned = cordoned
	if !cordoned {
		m.cordonEpoch = ""
	}
	return nil
}

// Uncordon clears only the cordon epoch owned by the requesting operation.
func (m *Manager) Uncordon(epoch string) error {
	m.mu.Lock()
	if !m.cordoned {
		m.mu.Unlock()
		return nil
	}
	if epoch == "" || epoch != m.cordonEpoch {
		m.mu.Unlock()
		return fmt.Errorf("cordon epoch mismatch")
	}
	m.mu.Unlock()
	return m.SetCordoned(false)
}

// Cordon rejects new reservations and waits for pre-existing boots/restores to
// either publish into inventory or fail.
func (m *Manager) Cordon(ctx context.Context) (string, error) {
	if err := ctx.Err(); err != nil {
		return "", err
	}
	if err := m.SetCordoned(true); err != nil {
		return "", err
	}
	ticker := time.NewTicker(10 * time.Millisecond)
	defer ticker.Stop()
	for {
		m.mu.Lock()
		pending := len(m.capacityReserved) + len(m.lifecyclePending)
		m.mu.Unlock()
		if pending == 0 {
			m.mu.Lock()
			epoch := m.cordonEpoch
			m.mu.Unlock()
			return epoch, nil
		}
		select {
		case <-ctx.Done():
			return "", ctx.Err()
		case <-ticker.C:
		}
	}
}

// InstanceInfo is host-drain inventory.
type InstanceInfo struct {
	User             string `json:"user"`
	App              string `json:"app"`
	Gen              string `json:"gen,omitempty"`
	AgentApp         string `json:"agent_app"`
	Image            string `json:"image,omitempty"`
	Tier             string `json:"tier"`
	State            State  `json:"state"`
	NoIdle           bool   `json:"no_idle"`
	SSHHostPublicKey string `json:"ssh_host_public_key"`
}

// ListInstances returns a stable snapshot of this host's inventory.
func (m *Manager) ListInstances() []InstanceInfo {
	m.mu.Lock()
	defer m.mu.Unlock()
	out := make([]InstanceInfo, 0, len(m.inst))
	for _, in := range m.inst {
		app, gen := genid.SplitAgentApp(in.Key.App)
		out = append(out, InstanceInfo{
			User: in.Key.User, App: app, Gen: gen, AgentApp: in.Key.App,
			Image: in.Image, Tier: in.Tier, State: in.State, NoIdle: in.noIdle,
			SSHHostPublicKey: in.SSHHostPublicKey,
		})
	}
	sort.Slice(out, func(i, j int) bool {
		if out[i].User != out[j].User {
			return out[i].User < out[j].User
		}
		if out[i].App != out[j].App {
			return out[i].App < out[j].App
		}
		return out[i].Gen < out[j].Gen
	})
	return out
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
	if err := m.reserveCapacity(k, opt.Tier, opt.CordonEpoch); err != nil {
		return nil, err
	}
	defer func() {
		if retErr != nil {
			m.releaseCapacity(k)
		}
	}()
	resourceID := instanceResourceID(k)
	dir := filepath.Join(m.cfg.WorkDir, "vm-"+resourceID)
	if err := os.RemoveAll(dir); err != nil {
		return nil, err
	}
	if err := os.MkdirAll(dir, 0o700); err != nil {
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
	sshHostPublicKey, err := injectSSHHostKey(rootfsPath)
	if err != nil {
		return nil, err
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
		if err := m.reserveResources(k, rootfsPath, tapName, candidateGuest, candidateHost); err == nil {
			hostIP, guestIP = candidateHost, candidateGuest
			break
		}
	}
	if hostIP == "" {
		return nil, fmt.Errorf("no guest subnet available for %s", k)
	}
	defer func() {
		if retErr != nil {
			m.releaseResources(k)
		}
	}()
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
		CPUTemplate:    m.cfg.CPUTemplate,
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
		Key:              k,
		State:            StateRunning,
		Addr:             addr,
		GuestIP:          guestIP,
		HostIP:           hostIP,
		TapName:          tapName,
		GuestMAC:         mac,
		Rootfs:           rootfsPath,
		WorkDir:          dir,
		LastUsed:         time.Now(),
		Image:            imageRef,
		Tier:             opt.Tier,
		VCPUs:            vcpus,
		MemMiB:           memMiB,
		SSHHostPublicKey: sshHostPublicKey,
		machine:          mach,
		noIdle:           opt.NoIdle,
		relay:            relay,
	}, nil
}

func injectSSHHostKey(rootfsPath string) (string, error) {
	privateKey, signer, err := hostkey.Generate()
	if err != nil {
		return "", fmt.Errorf("generate app host key: %w", err)
	}
	tmp, err := os.CreateTemp("", "sshcloud-app-host-key-*")
	if err != nil {
		return "", err
	}
	path := tmp.Name()
	defer os.Remove(path)
	if err := tmp.Chmod(0o600); err != nil {
		_ = tmp.Close()
		return "", err
	}
	if _, err := tmp.Write(privateKey); err != nil {
		_ = tmp.Close()
		return "", err
	}
	if err := tmp.Close(); err != nil {
		return "", err
	}
	if err := rootfs.InjectFile(rootfsPath, path, "/run/platform/ssh_host_ed25519_key", "0600"); err != nil {
		return "", fmt.Errorf("inject app host key: %w", err)
	}
	public := ssh.MarshalAuthorizedKey(signer.PublicKey())
	publicPath, err := os.CreateTemp("", "sshcloud-app-host-key-*.pub")
	if err != nil {
		return "", err
	}
	publicTmp := publicPath.Name()
	defer os.Remove(publicTmp)
	if _, err := publicPath.Write(public); err != nil {
		_ = publicPath.Close()
		return "", err
	}
	if err := publicPath.Close(); err != nil {
		return "", err
	}
	if err := rootfs.InjectFile(rootfsPath, publicTmp, "/run/platform/ssh_host_ed25519_key.pub", "0644"); err != nil {
		return "", fmt.Errorf("inject app host public key: %w", err)
	}
	return string(public), nil
}

func instanceResourceID(k InstanceKey) string {
	sum := sha256.Sum256([]byte(k.User + "\x00" + k.App))
	// 12 hex characters keeps TAP names at Linux's 15-byte IFNAMSIZ limit.
	return fmt.Sprintf("%x", sum[:6])
}

// InstanceStatus is a read-only view for the HTTP API.
type InstanceStatus struct {
	State            State
	Addr             string
	GuestIP          string
	LastUsed         time.Time
	SnapKey          string
	SSHHostPublicKey string
}

// Status returns the current state of an instance, if known.
func (m *Manager) Status(user, app string) (InstanceStatus, bool) {
	k := InstanceKey{User: user, App: app}
	op := m.instanceLock(k)
	op.Lock()
	defer op.Unlock()
	return m.statusLocked(k)
}

// StatusContext waits for an in-flight lifecycle mutation, making a missing
// result authoritative for RPC reconciliation.
func (m *Manager) StatusContext(ctx context.Context, user, app string) (InstanceStatus, bool, error) {
	k := InstanceKey{User: user, App: app}
	op := m.instanceLock(k)
	for !op.TryLock() {
		select {
		case <-ctx.Done():
			return InstanceStatus{}, false, ctx.Err()
		case <-time.After(5 * time.Millisecond):
		}
	}
	defer op.Unlock()
	status, ok := m.statusLocked(k)
	return status, ok, nil
}

func (m *Manager) statusLocked(k InstanceKey) (InstanceStatus, bool) {
	m.mu.Lock()
	defer m.mu.Unlock()
	in, ok := m.inst[k]
	if !ok {
		return InstanceStatus{}, false
	}
	return InstanceStatus{
		State:            in.State,
		Addr:             in.Addr,
		GuestIP:          in.GuestIP,
		LastUsed:         in.LastUsed,
		SnapKey:          in.snapKey,
		SSHHostPublicKey: in.SSHHostPublicKey,
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
	for _, tool := range []string{"ip", "iptables", "mkfs.ext4", "debugfs"} {
		if _, err := exec.LookPath(tool); err != nil {
			return fmt.Errorf("required tool %q: %w", tool, err)
		}
	}
	var fs syscall.Statfs_t
	if err := syscall.Statfs(m.cfg.WorkDir, &fs); err != nil {
		return fmt.Errorf("work-dir filesystem: %w", err)
	}
	if available := int64(fs.Bavail) * int64(fs.Bsize); available < 1<<30 {
		return fmt.Errorf("work-dir has less than 1 GiB available")
	}
	if m.cfg.SnapStore != nil {
		ctx, cancel := context.WithTimeout(context.Background(), 3*time.Second)
		_, err := m.cfg.SnapStore.Has(ctx, snapshot.KeyFor("healthcheck", "healthcheck"))
		cancel()
		if err != nil {
			return fmt.Errorf("snapshot store: %w", err)
		}
	}
	return nil
}

// Sleep snapshots a running instance, uploads it, and frees the VMM (keeps TAP).
func (m *Manager) Sleep(ctx context.Context, user, app string) error {
	return m.SleepWithEpoch(ctx, user, app, "")
}

func (m *Manager) SleepWithEpoch(ctx context.Context, user, app, cordonEpoch string) error {
	k := InstanceKey{User: user, App: app}
	if m.cfg.SnapStore == nil {
		return fmt.Errorf("snapshot store not configured")
	}
	op := m.instanceLock(k)
	op.Lock()
	defer op.Unlock()
	if err := m.beginLifecycle(k, cordonEpoch); err != nil {
		return err
	}
	defer m.endLifecycle(k)

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
	if err := os.MkdirAll(snapDir, 0o700); err != nil {
		return err
	}
	meta := snapshot.Meta{
		SchemaVersion:    snapshot.SchemaVersion,
		User:             user,
		App:              app,
		GuestIP:          in.GuestIP,
		TapName:          in.TapName,
		GuestMAC:         in.GuestMAC,
		HostIP:           in.HostIP,
		RootfsPath:       in.Rootfs,
		Image:            in.Image,
		Tier:             in.Tier,
		PlatformVersion:  m.platformVersion(),
		SSHHostPublicKey: in.SSHHostPublicKey,
		CreatedAt:        time.Now().UTC(),
	}
	if err := pkg.WriteMeta(meta); err != nil {
		return err
	}
	if err := mach.Pause(ctx); err != nil {
		return fmt.Errorf("pause: %w", err)
	}
	resumeAfterFailure := func(cause error) error {
		recoveryCtx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
		defer cancel()
		if resumeErr := mach.Resume(recoveryCtx); resumeErr != nil {
			_ = mach.Kill()
			m.mu.Lock()
			in.machine = nil
			in.State = StateFailed
			m.mu.Unlock()
			return fmt.Errorf("%w (resume also failed: %v)", cause, resumeErr)
		}
		return cause
	}
	if err := rootfs.Clone(in.Rootfs, pkg.RootfsPath); err != nil {
		return resumeAfterFailure(fmt.Errorf("clone rootfs for snap: %w", err))
	}
	files := firecracker.SnapshotFiles{StatePath: pkg.StatePath, MemPath: pkg.MemPath}
	if err := mach.CreateSnapshot(ctx, files); err != nil {
		return resumeAfterFailure(fmt.Errorf("create snapshot: %w", err))
	}
	key := snapshot.KeyFor(user, app)
	if err := m.cfg.SnapStore.Put(ctx, key, pkg); err != nil {
		return resumeAfterFailure(fmt.Errorf("upload snapshot: %w", err))
	}
	if err := mach.Kill(); err != nil {
		// The durable snapshot is already committed. Keep state recoverable even
		// if process teardown reports an error.
		_ = mach.Kill()
		m.mu.Lock()
		in.machine = nil
		in.State = StateSleeping
		in.snapKey = key
		in.LastUsed = time.Now()
		m.mu.Unlock()
		return fmt.Errorf("kill after durable snapshot: %w", err)
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
	return m.EvictContext(context.Background(), user, app)
}

func (m *Manager) EvictContext(ctx context.Context, user, app string) error {
	return m.EvictWithEpoch(ctx, user, app, "")
}

func (m *Manager) EvictWithEpoch(ctx context.Context, user, app, cordonEpoch string) error {
	k := InstanceKey{User: user, App: app}
	op := m.instanceLock(k)
	op.Lock()
	defer op.Unlock()
	if err := ctx.Err(); err != nil {
		return err
	}
	if err := m.beginLifecycle(k, cordonEpoch); err != nil {
		return err
	}
	defer m.endLifecycle(k)
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
	return m.adoptWith(ctx, user, app, "")
}

// PreflightSnapshot validates that this host can eventually restore a sleeping
// instance without allocating guest capacity or starting a VMM.
func (m *Manager) PreflightSnapshot(ctx context.Context, user, app string) (InstanceInfo, error) {
	k := InstanceKey{User: user, App: app}
	if m.cfg.SnapStore == nil {
		return InstanceInfo{}, fmt.Errorf("snapshot store not configured")
	}
	if !m.rt.Available() {
		return InstanceInfo{}, fmt.Errorf("firecracker requires /dev/kvm (not available on this host)")
	}
	meta, err := m.cfg.SnapStore.Meta(ctx, snapshot.KeyFor(user, app))
	if err != nil {
		return InstanceInfo{}, err
	}
	if meta.User != user || meta.App != app {
		return InstanceInfo{}, fmt.Errorf("snapshot identity mismatch: got %s/%s, want %s", meta.User, meta.App, k)
	}
	if meta.SchemaVersion != snapshot.SchemaVersion {
		return InstanceInfo{}, fmt.Errorf("snapshot schema version %d is unsupported", meta.SchemaVersion)
	}
	tier, _, _, err := tierResources(meta.Tier)
	if err != nil {
		return InstanceInfo{}, err
	}
	if platformVersion := m.platformVersion(); platformVersion != "" && meta.PlatformVersion != platformVersion {
		return InstanceInfo{}, fmt.Errorf("snapshot platform version %q is incompatible with host %q", meta.PlatformVersion, platformVersion)
	}
	if err := validateSSHHostPublicKey(meta.SSHHostPublicKey); err != nil {
		return InstanceInfo{}, err
	}
	resourceID := instanceResourceID(k)
	if meta.RootfsPath != filepath.Join(m.cfg.WorkDir, "vm-"+resourceID, "rootfs.ext4") ||
		meta.TapName != "fc-"+resourceID {
		return InstanceInfo{}, fmt.Errorf("snapshot host resource metadata is incompatible")
	}
	if err := m.validateSnapshotNetwork(k, meta); err != nil {
		return InstanceInfo{}, err
	}
	baseApp, gen := genid.SplitAgentApp(app)
	return InstanceInfo{
		User: user, App: baseApp, Gen: gen, AgentApp: app,
		Image: meta.Image, Tier: tier, State: StateSleeping,
		SSHHostPublicKey: meta.SSHHostPublicKey,
	}, nil
}

// RegisterSleeping validates and records snapshot ownership on a target without
// waking the VM. It is a cordon-visible host claim for sleeping generations.
func (m *Manager) RegisterSleeping(ctx context.Context, user, app string) (InstanceInfo, error) {
	k := InstanceKey{User: user, App: app}
	op := m.instanceLock(k)
	op.Lock()
	defer op.Unlock()
	m.mu.Lock()
	if existing := m.inst[k]; existing != nil {
		baseApp, gen := genid.SplitAgentApp(app)
		info := InstanceInfo{
			User: user, App: baseApp, Gen: gen, AgentApp: app,
			Image: existing.Image, Tier: existing.Tier, State: existing.State,
			SSHHostPublicKey: existing.SSHHostPublicKey,
		}
		m.mu.Unlock()
		return info, nil
	}
	m.mu.Unlock()
	if err := m.beginLifecycle(k, ""); err != nil {
		return InstanceInfo{}, err
	}
	defer m.endLifecycle(k)
	if err := ctx.Err(); err != nil {
		return InstanceInfo{}, err
	}
	info, err := m.PreflightSnapshot(ctx, user, app)
	if err != nil {
		return InstanceInfo{}, err
	}
	meta, err := m.cfg.SnapStore.Meta(ctx, snapshot.KeyFor(user, app))
	if err != nil {
		return InstanceInfo{}, err
	}
	resourceID := instanceResourceID(k)
	in := &Instance{
		Key: k, State: StateSleeping,
		GuestIP: meta.GuestIP, HostIP: meta.HostIP, TapName: meta.TapName,
		GuestMAC: meta.GuestMAC,
		Rootfs:   filepath.Join(m.cfg.WorkDir, "vm-"+resourceID, "rootfs.ext4"),
		WorkDir:  filepath.Join(m.cfg.WorkDir, "vm-"+resourceID),
		Image:    meta.Image, Tier: info.Tier, snapKey: snapshot.KeyFor(user, app),
		SSHHostPublicKey: meta.SSHHostPublicKey, LastUsed: time.Now(),
	}
	_, in.VCPUs, in.MemMiB, _ = tierResources(info.Tier)
	m.mu.Lock()
	m.inst[k] = in
	m.mu.Unlock()
	return info, nil
}

// AdoptForced permits rollback onto a cordoned source host.
func (m *Manager) AdoptForced(ctx context.Context, user, app, cordonEpoch string) (*Instance, error) {
	if cordonEpoch == "" {
		return nil, fmt.Errorf("cordon epoch required for forced adopt")
	}
	return m.adoptWith(ctx, user, app, cordonEpoch)
}

func (m *Manager) adoptWith(ctx context.Context, user, app, cordonEpoch string) (*Instance, error) {
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
	if m.closed {
		m.mu.Unlock()
		return nil, fmt.Errorf("agent manager is closed")
	}
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

	return m.adopt(ctx, k, n, EnsureOpts{CordonEpoch: cordonEpoch})
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
	if meta.SchemaVersion != snapshot.SchemaVersion {
		return nil, fmt.Errorf("snapshot schema version %d is unsupported", meta.SchemaVersion)
	}
	if platformVersion := m.platformVersion(); platformVersion != "" && meta.PlatformVersion != platformVersion {
		return nil, fmt.Errorf("snapshot platform version %q is incompatible with host %q", meta.PlatformVersion, platformVersion)
	}
	if err := validateSSHHostPublicKey(meta.SSHHostPublicKey); err != nil {
		return nil, err
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
	if err := m.reserveCapacity(k, meta.Tier, opt.CordonEpoch); err != nil {
		return nil, err
	}
	if err := m.reserveResources(k, rootfsPath, tapName, meta.GuestIP, meta.HostIP); err != nil {
		m.releaseCapacity(k)
		return nil, err
	}
	published := false
	defer func() {
		if !published {
			m.releaseResources(k)
			m.releaseCapacity(k)
		}
	}()
	if err := os.MkdirAll(dir, 0o700); err != nil {
		return nil, err
	}
	in := &Instance{
		Key:              k,
		State:            StateSleeping,
		GuestIP:          meta.GuestIP,
		HostIP:           meta.HostIP,
		TapName:          tapName,
		GuestMAC:         meta.GuestMAC,
		Rootfs:           rootfsPath,
		WorkDir:          dir,
		snapKey:          snapshot.KeyFor(k.User, k.App),
		LastUsed:         time.Now(),
		Image:            meta.Image,
		Tier:             meta.Tier,
		SSHHostPublicKey: meta.SSHHostPublicKey,
		noIdle:           opt.NoIdle,
	}
	_, in.VCPUs, in.MemMiB, _ = tierResources(meta.Tier)

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

	m.publishInstance(in)
	published = true
	return instanceCopy(in), nil
}

func resourceKeys(rootfsPath, tapName, guestIP, hostIP string) []string {
	return []string{
		"rootfs:" + rootfsPath,
		"tap:" + tapName,
		"guest-ip:" + guestIP,
		"host-ip:" + hostIP,
	}
}

func (m *Manager) reserveResources(k InstanceKey, rootfsPath, tapName, guestIP, hostIP string) error {
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
	for _, resource := range resourceKeys(rootfsPath, tapName, guestIP, hostIP) {
		if other, ok := m.reserved[resource]; ok && other != k {
			return fmt.Errorf("resource %s for %s is being prepared by instance %s", resource, k, other)
		}
	}
	for _, resource := range resourceKeys(rootfsPath, tapName, guestIP, hostIP) {
		m.reserved[resource] = k
	}
	return nil
}

func (m *Manager) releaseResources(k InstanceKey) {
	m.mu.Lock()
	defer m.mu.Unlock()
	m.releaseResourcesLocked(k)
}

func (m *Manager) releaseResourcesLocked(k InstanceKey) {
	for resource, owner := range m.reserved {
		if owner == k {
			delete(m.reserved, resource)
		}
	}
}

func (m *Manager) publishInstance(in *Instance) {
	m.mu.Lock()
	defer m.mu.Unlock()
	m.releaseResourcesLocked(in.Key)
	delete(m.capacityReserved, in.Key)
	m.inst[in.Key] = in
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

func validateSSHHostPublicKey(raw string) error {
	key, _, _, rest, err := ssh.ParseAuthorizedKey([]byte(raw))
	if err != nil {
		return fmt.Errorf("invalid snapshot SSH host key: %w", err)
	}
	if strings.TrimSpace(string(rest)) != "" || key.Type() != ssh.KeyAlgoED25519 {
		return fmt.Errorf("snapshot SSH host key must contain exactly one Ed25519 key")
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
	if err := m.reserveCapacity(k, in.Tier, ""); err != nil {
		return nil, err
	}
	reserved := true
	defer func() {
		if reserved {
			m.releaseCapacity(k)
		}
	}()

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
	delete(m.capacityReserved, k)
	in.State = StateRunning
	in.machine = mach
	in.Addr = addr
	in.LastUsed = time.Now()
	m.mu.Unlock()
	reserved = false
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
	if m.cfg.SnapStore != nil {
		if err := m.cfg.SnapStore.Delete(ctx, snapshot.KeyFor(user, app)); err != nil {
			return fmt.Errorf("delete snapshot: %w", err)
		}
	}
	if !ok {
		return nil
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
	return m.SetNoIdleContext(context.Background(), user, app, noIdle)
}

func (m *Manager) SetNoIdleContext(ctx context.Context, user, app string, noIdle bool) error {
	return m.SetNoIdleWithEpoch(ctx, user, app, noIdle, "")
}

func (m *Manager) SetNoIdleWithEpoch(ctx context.Context, user, app string, noIdle bool, cordonEpoch string) error {
	k := InstanceKey{User: user, App: app}
	op := m.instanceLock(k)
	op.Lock()
	defer op.Unlock()
	if err := ctx.Err(); err != nil {
		return err
	}
	if err := m.beginLifecycle(k, cordonEpoch); err != nil {
		return err
	}
	defer m.endLifecycle(k)
	m.mu.Lock()
	defer m.mu.Unlock()
	if in, ok := m.inst[k]; ok {
		in.noIdle = noIdle
		in.LastUsed = time.Now()
		return nil
	}
	return nil
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
	m.mu.Lock()
	if m.closed {
		m.mu.Unlock()
		return nil
	}
	m.closed = true
	close(m.stop)
	ops := make([]*sync.Mutex, 0, len(m.ops))
	for _, op := range m.ops {
		ops = append(ops, op)
	}
	m.mu.Unlock()

	// An in-flight boot/restore may not be visible in inst yet. Fence every
	// operation that existed when closing began before collecting instances.
	for _, op := range ops {
		op.Lock()
		op.Unlock()
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
			m.mu.Lock()
			epoch := m.cordonEpoch
			m.mu.Unlock()
			_ = m.SetNoIdleWithEpoch(context.Background(), k.User, k.App, false, epoch)
			st, ok := m.Status(k.User, k.App)
			if ok && st.State == StateRunning {
				ctx, cancel := context.WithTimeout(context.Background(), 2*time.Minute)
				err := m.SleepWithEpoch(ctx, k.User, k.App, epoch)
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

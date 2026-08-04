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
)

// InstanceKey identifies a running app instance.
type InstanceKey struct {
	User string
	App  string
}

func (k InstanceKey) String() string { return k.User + "/" + k.App }

// Instance is a live microVM endpoint.
type Instance struct {
	Key      InstanceKey
	Addr     string // host-reachable host:port for SSH
	GuestIP  string
	TapName  string
	Rootfs   string
	machine  *firecracker.Machine
}

// Config for the Manager.
type Config struct {
	WorkDir        string // sockets, per-instance rootfs copies
	FirecrackerBin string
	KernelPath     string
	BaseRootfs     string // fortune (or app) base ext4
	CAPubPath      string // injected into each instance rootfs as /ca.pub
	// Network: host uses 172.16.<n>.1, guest .2 on tap fc-<n>
	SubnetBase string // default 172.16
}

// Manager boots and tracks Firecracker instances.
type Manager struct {
	cfg   Config
	mu    sync.Mutex
	inst  map[InstanceKey]*Instance
	seq   int
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
	if err := os.MkdirAll(cfg.WorkDir, 0o755); err != nil {
		return nil, err
	}
	return &Manager{cfg: cfg, inst: make(map[InstanceKey]*Instance)}, nil
}

// Ensure starts the instance if needed and returns host:22 dial address
// (actually host reaches guestIP:22).
func (m *Manager) Ensure(ctx context.Context, user, app string) (*Instance, error) {
	k := InstanceKey{User: user, App: app}
	m.mu.Lock()
	if in, ok := m.inst[k]; ok {
		m.mu.Unlock()
		return in, nil
	}
	m.seq++
	n := m.seq
	m.mu.Unlock()

	in, err := m.boot(ctx, k, n)
	if err != nil {
		return nil, err
	}
	m.mu.Lock()
	m.inst[k] = in
	m.mu.Unlock()
	return in, nil
}

func (m *Manager) boot(ctx context.Context, k InstanceKey, n int) (*Instance, error) {
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
	octet := n%200 + 1 // 1..200
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
		Key:     k,
		Addr:    addr,
		GuestIP: guestIP,
		TapName: tapName,
		Rootfs:  rootfsPath,
		machine: machine,
	}, nil
}

// Stop tears down an instance.
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
	err := in.machine.Stop()
	_ = firecracker.DeleteTap(in.TapName)
	return err
}

// Addr implements gateway DialFunc shape.
func (m *Manager) Addr(user, app string) (string, error) {
	in, err := m.Ensure(context.Background(), user, app)
	if err != nil {
		return "", err
	}
	return in.Addr, nil
}

// Close stops all instances.
func (m *Manager) Close() error {
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

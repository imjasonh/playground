package agent

import (
	"context"
	"fmt"
	"net"
	"path/filepath"
	"time"

	"github.com/imjasonh/playground/sshcloud/internal/firecracker"
	"github.com/imjasonh/playground/sshcloud/internal/hostisolation"
	"github.com/imjasonh/playground/sshcloud/internal/rootfs"
)

// machine is the running VMM handle.
type machine interface {
	Alive() bool
	Pause(ctx context.Context) error
	Resume(ctx context.Context) error
	CreateSnapshot(ctx context.Context, files firecracker.SnapshotFiles) error
	Stop() error
	Kill() error
}

// Runtime boots and restores microVMs. dialAddr is what the gateway should dial.
type Runtime interface {
	Available() bool
	Ready(ctx context.Context) error
	SnapshotLayout() string
	CreateTap(ctx context.Context, name, hostIP string) error
	DeleteTap(ctx context.Context, name string) error
	Boot(ctx context.Context, spec BootSpec) (m machine, dialAddr string, err error)
	Restore(ctx context.Context, spec RestoreSpec) (m machine, dialAddr string, err error)
}

// BootSpec is a cold-start request.
type BootSpec struct {
	FirecrackerBin string
	WorkDir        string
	KernelPath     string
	RootfsPath     string
	BootArgs       string
	TapName        string
	GuestMAC       string
	GuestIP        string
	VCPUs          int64
	MemMiB         int64
	CPUTemplate    string
}

// RestoreSpec loads a snapshot and resumes.
type RestoreSpec struct {
	FirecrackerBin string
	WorkDir        string
	StatePath      string
	MemPath        string
	RootfsSrc      string
	RootfsDst      string
	TapName        string
	HostIP         string
	GuestIP        string
	VCPUs          int64
	MemMiB         int64
}

// DirectRuntime launches Firecracker directly. It exists only for explicit
// local/KVM integration tests; production uses HelperRuntime.
type DirectRuntime struct{}

func (DirectRuntime) Available() bool { return firecracker.Available() }

func (DirectRuntime) Ready(context.Context) error {
	if !firecracker.Available() {
		return fmt.Errorf("/dev/kvm is unavailable")
	}
	return nil
}

func (DirectRuntime) SnapshotLayout() string {
	return hostisolation.SnapshotLayoutDirect
}

func (DirectRuntime) CreateTap(_ context.Context, name, hostIP string) error {
	return firecracker.CreateTap(name, hostIP, 24)
}

func (DirectRuntime) DeleteTap(_ context.Context, name string) error {
	return firecracker.DeleteTap(name)
}

func (DirectRuntime) Boot(ctx context.Context, spec BootSpec) (machine, string, error) {
	sock := filepath.Join(spec.WorkDir, "firecracker.sock")
	logPath := filepath.Join(spec.WorkDir, "firecracker.log")
	m, err := firecracker.Start(ctx, firecracker.Config{
		FirecrackerBin: spec.FirecrackerBin,
		SocketPath:     sock,
		KernelPath:     spec.KernelPath,
		RootfsPath:     spec.RootfsPath,
		BootArgs:       spec.BootArgs,
		VCPUs:          spec.VCPUs,
		MemMiB:         spec.MemMiB,
		CPUTemplate:    spec.CPUTemplate,
		TapDevice:      spec.TapName,
		GuestMAC:       spec.GuestMAC,
		LogPath:        logPath,
	})
	if err != nil {
		return nil, "", err
	}
	addr := net.JoinHostPort(spec.GuestIP, "22")
	if err := firecracker.WaitTCP(ctx, addr, 30*time.Second); err != nil {
		_ = m.Stop()
		return nil, "", fmt.Errorf("guest SSH not ready: %w (see %s)", err, logPath)
	}
	return m, addr, nil
}

func (r DirectRuntime) Restore(ctx context.Context, spec RestoreSpec) (machine, string, error) {
	if err := rootfs.Clone(spec.RootfsSrc, spec.RootfsDst); err != nil {
		return nil, "", err
	}
	if err := r.CreateTap(ctx, spec.TapName, spec.HostIP); err != nil {
		return nil, "", fmt.Errorf("recreate tap: %w", err)
	}
	keepTap := false
	defer func() {
		if !keepTap {
			_ = r.DeleteTap(context.Background(), spec.TapName)
		}
	}()
	sock := filepath.Join(spec.WorkDir, "firecracker.sock")
	logPath := filepath.Join(spec.WorkDir, "firecracker-wake.log")
	m, err := firecracker.Restore(ctx, firecracker.RestoreConfig{
		FirecrackerBin:    spec.FirecrackerBin,
		SocketPath:        sock,
		Snapshot:          firecracker.SnapshotFiles{StatePath: spec.StatePath, MemPath: spec.MemPath},
		LogPath:           logPath,
		ResumeImmediately: false,
	})
	if err != nil {
		return nil, "", err
	}
	if err := m.Resume(ctx); err != nil {
		_ = m.Kill()
		return nil, "", fmt.Errorf("resume: %w", err)
	}
	addr := net.JoinHostPort(spec.GuestIP, "22")
	if err := firecracker.WaitTCP(ctx, addr, 30*time.Second); err != nil {
		_ = m.Kill()
		return nil, "", fmt.Errorf("guest SSH not ready after wake: %w (see %s)", err, logPath)
	}
	keepTap = true
	return m, addr, nil
}

type unavailableRuntime struct{}

func (unavailableRuntime) Available() bool { return false }
func (unavailableRuntime) Ready(context.Context) error {
	return fmt.Errorf("runtime is not configured")
}
func (unavailableRuntime) SnapshotLayout() string { return "" }
func (unavailableRuntime) CreateTap(context.Context, string, string) error {
	return fmt.Errorf("runtime is not configured")
}
func (unavailableRuntime) DeleteTap(context.Context, string) error { return nil }
func (unavailableRuntime) Boot(context.Context, BootSpec) (machine, string, error) {
	return nil, "", fmt.Errorf("runtime is not configured")
}
func (unavailableRuntime) Restore(context.Context, RestoreSpec) (machine, string, error) {
	return nil, "", fmt.Errorf("runtime is not configured")
}

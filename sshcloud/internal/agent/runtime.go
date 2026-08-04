package agent

import (
	"context"
	"fmt"
	"net"
	"path/filepath"
	"time"

	"github.com/imjasonh/playground/sshcloud/internal/firecracker"
	"github.com/imjasonh/playground/sshcloud/internal/rootfs"
)

// machine is the running VMM handle.
type machine interface {
	SnapshotThenKill(ctx context.Context, files firecracker.SnapshotFiles) error
	Stop() error
	Kill() error
}

// Runtime boots and restores microVMs. dialAddr is what the gateway should dial.
type Runtime interface {
	Available() bool
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
}

// FirecrackerRuntime is the production Runtime.
type FirecrackerRuntime struct{}

func (FirecrackerRuntime) Available() bool { return firecracker.Available() }

func (FirecrackerRuntime) Boot(ctx context.Context, spec BootSpec) (machine, string, error) {
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

func (FirecrackerRuntime) Restore(ctx context.Context, spec RestoreSpec) (machine, string, error) {
	if err := rootfs.Clone(spec.RootfsSrc, spec.RootfsDst); err != nil {
		return nil, "", err
	}
	if err := firecracker.CreateTap(spec.TapName, spec.HostIP, 24); err != nil {
		return nil, "", fmt.Errorf("recreate tap: %w", err)
	}
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
	return m, addr, nil
}

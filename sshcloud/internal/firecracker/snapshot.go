package firecracker

import (
	"context"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
)

// SnapshotFiles are the on-disk artifacts for a full Firecracker snapshot.
type SnapshotFiles struct {
	StatePath string // microVM state (snapshot_path)
	MemPath   string // guest memory (mem_file_path)
}

// SnapshotFilesIn returns default snapshot file paths inside dir.
func SnapshotFilesIn(dir string) SnapshotFiles {
	return SnapshotFiles{
		StatePath: filepath.Join(dir, "vm.state"),
		MemPath:   filepath.Join(dir, "vm.mem"),
	}
}

// Pause freezes the running microVM (required before CreateSnapshot).
func (m *Machine) Pause(ctx context.Context) error {
	return m.put(ctx, "/actions", map[string]string{"action_type": "Pause"})
}

// Resume continues a paused microVM.
func (m *Machine) Resume(ctx context.Context) error {
	return m.put(ctx, "/actions", map[string]string{"action_type": "Resume"})
}

// CreateSnapshot writes a full snapshot. The VM must already be Paused.
func (m *Machine) CreateSnapshot(ctx context.Context, files SnapshotFiles) error {
	if files.StatePath == "" || files.MemPath == "" {
		return fmt.Errorf("StatePath and MemPath required")
	}
	if err := os.MkdirAll(filepath.Dir(files.StatePath), 0o755); err != nil {
		return err
	}
	if err := os.MkdirAll(filepath.Dir(files.MemPath), 0o755); err != nil {
		return err
	}
	return m.put(ctx, "/snapshot/create", map[string]any{
		"snapshot_type": "Full",
		"snapshot_path": files.StatePath,
		"mem_file_path": files.MemPath,
	})
}

// Kill terminates the Firecracker process without guest shutdown (used after snapshot).
func (m *Machine) Kill() error {
	if m == nil || m.cmd == nil || m.cmd.Process == nil {
		return nil
	}
	_ = m.cmd.Process.Kill()
	_, _ = m.cmd.Process.Wait()
	_ = os.Remove(m.cfg.SocketPath)
	m.cmd = nil
	return nil
}

// RestoreConfig boots a fresh Firecracker process by loading a snapshot (no cold boot).
type RestoreConfig struct {
	FirecrackerBin string
	SocketPath     string
	Snapshot       SnapshotFiles
	LogPath        string
	// ResumeImmediately if true sets resume_vm on load.
	ResumeImmediately bool
}

// Restore starts firecracker and loads snapshot files.
func Restore(ctx context.Context, cfg RestoreConfig) (*Machine, error) {
	if cfg.SocketPath == "" || cfg.Snapshot.StatePath == "" || cfg.Snapshot.MemPath == "" {
		return nil, fmt.Errorf("SocketPath and Snapshot files required")
	}
	if cfg.FirecrackerBin == "" {
		cfg.FirecrackerBin = "firecracker"
	}
	if err := os.MkdirAll(filepath.Dir(cfg.SocketPath), 0o755); err != nil {
		return nil, err
	}
	_ = os.Remove(cfg.SocketPath)

	cmd := exec.CommandContext(ctx, cfg.FirecrackerBin, "--api-sock", cfg.SocketPath)
	if cfg.LogPath != "" {
		f, err := os.Create(cfg.LogPath)
		if err != nil {
			return nil, err
		}
		cmd.Stdout = f
		cmd.Stderr = f
	}
	if err := cmd.Start(); err != nil {
		return nil, fmt.Errorf("start firecracker: %w", err)
	}
	m := &Machine{
		cfg: Config{FirecrackerBin: cfg.FirecrackerBin, SocketPath: cfg.SocketPath, LogPath: cfg.LogPath},
		cmd: cmd,
		hc:  newUnixHTTPClient(cfg.SocketPath),
	}
	if err := m.waitSocket(ctx); err != nil {
		_ = m.Kill()
		return nil, err
	}
	body := map[string]any{
		"snapshot_path": cfg.Snapshot.StatePath,
		"mem_backend": map[string]string{
			"backend_path": cfg.Snapshot.MemPath,
			"backend_type": "File",
		},
		"resume_vm": cfg.ResumeImmediately,
	}
	if err := m.put(ctx, "/snapshot/load", body); err != nil {
		_ = m.Kill()
		return nil, fmt.Errorf("snapshot/load: %w", err)
	}
	return m, nil
}

// SnapshotThenKill pauses, writes a full snapshot, then kills the VMM.
func (m *Machine) SnapshotThenKill(ctx context.Context, files SnapshotFiles) error {
	if err := m.Pause(ctx); err != nil {
		return fmt.Errorf("pause: %w", err)
	}
	if err := m.CreateSnapshot(ctx, files); err != nil {
		_ = m.Resume(ctx)
		return fmt.Errorf("create snapshot: %w", err)
	}
	return m.Kill()
}

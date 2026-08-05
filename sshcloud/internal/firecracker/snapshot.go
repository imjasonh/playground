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
// Firecracker ≥1.0 uses PATCH /vm {"state":"Paused"} (not /actions).
func (m *Machine) Pause(ctx context.Context) error {
	return m.patch(ctx, "/vm", map[string]string{"state": "Paused"})
}

// Resume continues a paused microVM.
func (m *Machine) Resume(ctx context.Context) error {
	return m.patch(ctx, "/vm", map[string]string{"state": "Resumed"})
}

// CreateSnapshot writes a full snapshot. The VM must already be Paused.
func (m *Machine) CreateSnapshot(ctx context.Context, files SnapshotFiles) error {
	if files.StatePath == "" || files.MemPath == "" {
		return fmt.Errorf("StatePath and MemPath required")
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

	// The restore context bounds startup/load only; the restored VMM is owned
	// by the agent manager and must survive after the request returns.
	cmd := exec.Command(cfg.FirecrackerBin, "--api-sock", cfg.SocketPath)
	var logFile *os.File
	if cfg.LogPath != "" {
		f, err := os.Create(cfg.LogPath)
		if err != nil {
			return nil, err
		}
		logFile = f
		cmd.Stdout = f
		cmd.Stderr = f
	}
	if err := cmd.Start(); err != nil {
		if logFile != nil {
			_ = logFile.Close()
		}
		return nil, fmt.Errorf("start firecracker: %w", err)
	}
	if logFile != nil {
		_ = logFile.Close()
	}
	m := &Machine{
		cfg: Config{FirecrackerBin: cfg.FirecrackerBin, SocketPath: cfg.SocketPath, LogPath: cfg.LogPath},
		cmd: cmd,
		hc:  newUnixHTTPClient(cfg.SocketPath),
	}
	if err := m.WaitAPI(ctx); err != nil {
		logTail := readLogTail(cfg.LogPath, 4<<10)
		exit := processExitErr(cmd)
		_ = m.Kill()
		if logTail != "" || exit != "" {
			return nil, fmt.Errorf("%w%s%s", err, exit, logTail)
		}
		return nil, err
	}
	if err := m.LoadSnapshot(ctx, cfg.Snapshot, cfg.ResumeImmediately); err != nil {
		_ = m.Kill()
		return nil, fmt.Errorf("snapshot/load: %w", err)
	}
	return m, nil
}

// LoadSnapshot asks an already-running Firecracker API to load fixed snapshot
// files. Process lifecycle may be owned by the direct runtime or VMM helper.
func (m *Machine) LoadSnapshot(ctx context.Context, snapshot SnapshotFiles, resumeImmediately bool) error {
	if snapshot.StatePath == "" || snapshot.MemPath == "" {
		return fmt.Errorf("snapshot files required")
	}
	body := map[string]any{
		"snapshot_path": snapshot.StatePath,
		"mem_backend": map[string]string{
			"backend_path": snapshot.MemPath,
			"backend_type": "File",
		},
		"resume_vm": resumeImmediately,
	}
	return m.put(ctx, "/snapshot/load", body)
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

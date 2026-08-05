// Package firecracker boots microVMs via the Firecracker HTTP API socket.
package firecracker

import (
	"bytes"
	"context"
	"encoding/json"
	"fmt"
	"io"
	"net"
	"net/http"
	"os"
	"os/exec"
	"path/filepath"
	"syscall"
	"time"
)

// Config is the host-side description of a microVM.
type Config struct {
	// FirecrackerBin is the path to the firecracker binary (default: "firecracker" on PATH).
	FirecrackerBin string
	// SocketPath is the API unix socket path.
	SocketPath string
	// KernelPath is a Firecracker-compatible vmlinux.
	KernelPath string
	// RootfsPath is an ext4 image used as the root drive.
	RootfsPath string
	// BootArgs are appended to the default console/reboot args.
	BootArgs string
	// VCPUs and MemMiB size the VM (defaults: 1, 128).
	VCPUs  int64
	MemMiB int64
	// CPUTemplate selects a portable Firecracker CPU feature baseline (e.g. T2).
	CPUTemplate string
	// TapDevice is an existing TAP device name on the host (e.g. "fc-tap0").
	// Empty skips network configuration (vsock-only / no SSH over TCP).
	TapDevice string
	// GuestMAC is the virtio-net MAC (required when TapDevice is set).
	GuestMAC string
	// LogPath optional firecracker log file.
	LogPath string
}

// Machine is a running Firecracker process.
type Machine struct {
	cfg Config
	cmd *exec.Cmd
	hc  *http.Client
}

// Start launches firecracker, configures the VM, and issues InstanceStart.
func Start(ctx context.Context, cfg Config) (*Machine, error) {
	if err := cfg.validate(); err != nil {
		return nil, err
	}
	if cfg.FirecrackerBin == "" {
		cfg.FirecrackerBin = "firecracker"
	}
	if cfg.VCPUs == 0 {
		cfg.VCPUs = 1
	}
	if cfg.MemMiB == 0 {
		cfg.MemMiB = 128
	}
	if err := os.MkdirAll(filepath.Dir(cfg.SocketPath), 0o755); err != nil {
		return nil, err
	}
	_ = os.Remove(cfg.SocketPath)

	args := []string{"--api-sock", cfg.SocketPath}
	// The caller's context bounds startup only. A Firecracker VMM must outlive
	// the HTTP Ensure request that started it, so never tie the process lifetime
	// to that request with exec.CommandContext.
	cmd := exec.Command(cfg.FirecrackerBin, args...)
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
		cfg: cfg,
		cmd: cmd,
		hc:  newUnixHTTPClient(cfg.SocketPath),
	}
	if err := m.waitSocket(ctx); err != nil {
		logTail := readLogTail(cfg.LogPath, 4<<10)
		exit := processExitErr(cmd)
		_ = m.Kill()
		if logTail != "" || exit != "" {
			return nil, fmt.Errorf("%w%s%s", err, exit, logTail)
		}
		return nil, err
	}
	if err := m.configure(ctx); err != nil {
		_ = m.Stop()
		return nil, err
	}
	if err := m.put(ctx, "/actions", map[string]string{"action_type": "InstanceStart"}); err != nil {
		_ = m.Stop()
		return nil, fmt.Errorf("InstanceStart: %w", err)
	}
	return m, nil
}

func (c Config) validate() error {
	if c.SocketPath == "" {
		return fmt.Errorf("SocketPath required")
	}
	if c.KernelPath == "" {
		return fmt.Errorf("KernelPath required")
	}
	if c.RootfsPath == "" {
		return fmt.Errorf("RootfsPath required")
	}
	if c.TapDevice != "" && c.GuestMAC == "" {
		return fmt.Errorf("GuestMAC required when TapDevice is set")
	}
	return nil
}

func (m *Machine) waitSocket(ctx context.Context) error {
	deadline := time.Now().Add(5 * time.Second)
	var d net.Dialer
	for {
		c, err := d.DialContext(ctx, "unix", m.cfg.SocketPath)
		if err == nil {
			_ = c.Close()
			return nil
		}
		if time.Now().After(deadline) {
			return fmt.Errorf("timeout waiting for firecracker API socket %s: %w", m.cfg.SocketPath, err)
		}
		select {
		case <-ctx.Done():
			return ctx.Err()
		case <-time.After(20 * time.Millisecond):
		}
	}
}

func (m *Machine) configure(ctx context.Context) error {
	machineConfig := map[string]any{
		"vcpu_count":   m.cfg.VCPUs,
		"mem_size_mib": m.cfg.MemMiB,
	}
	if m.cfg.CPUTemplate != "" {
		machineConfig["cpu_template"] = m.cfg.CPUTemplate
	}
	if err := m.put(ctx, "/machine-config", machineConfig); err != nil {
		return fmt.Errorf("machine-config: %w", err)
	}
	bootArgs := "console=ttyS0 reboot=k panic=1 pci=off ipv6.disable=1"
	if m.cfg.BootArgs != "" {
		bootArgs = bootArgs + " " + m.cfg.BootArgs
	}
	if err := m.put(ctx, "/boot-source", map[string]any{
		"kernel_image_path": m.cfg.KernelPath,
		"boot_args":         bootArgs,
	}); err != nil {
		return fmt.Errorf("boot-source: %w", err)
	}
	if err := m.put(ctx, "/drives/1", map[string]any{
		"drive_id":       "1",
		"path_on_host":   m.cfg.RootfsPath,
		"is_root_device": true,
		"is_read_only":   false,
	}); err != nil {
		return fmt.Errorf("drives: %w", err)
	}
	if m.cfg.TapDevice != "" {
		if err := m.put(ctx, "/network-interfaces/eth0", map[string]any{
			"iface_id":      "eth0",
			"guest_mac":     m.cfg.GuestMAC,
			"host_dev_name": m.cfg.TapDevice,
		}); err != nil {
			return fmt.Errorf("network-interfaces: %w", err)
		}
	}
	return nil
}

func (m *Machine) put(ctx context.Context, path string, body any) error {
	return m.doJSON(ctx, http.MethodPut, path, body)
}

func (m *Machine) patch(ctx context.Context, path string, body any) error {
	return m.doJSON(ctx, http.MethodPatch, path, body)
}

func (m *Machine) doJSON(ctx context.Context, method, path string, body any) error {
	var buf bytes.Buffer
	if err := json.NewEncoder(&buf).Encode(body); err != nil {
		return err
	}
	req, err := http.NewRequestWithContext(ctx, method, "http://localhost"+path, &buf)
	if err != nil {
		return err
	}
	req.Header.Set("Content-Type", "application/json")
	res, err := m.hc.Do(req)
	if err != nil {
		return err
	}
	defer res.Body.Close()
	if res.StatusCode >= 300 {
		b, _ := io.ReadAll(res.Body)
		return fmt.Errorf("%s %s: %s: %s", method, path, res.Status, bytes.TrimSpace(b))
	}
	return nil
}

// Stop sends a shutdown and kills the Firecracker process if needed.
func (m *Machine) Stop() error {
	if m == nil || m.cmd == nil || m.cmd.Process == nil {
		return nil
	}
	ctx, cancel := context.WithTimeout(context.Background(), 2*time.Second)
	defer cancel()
	_ = m.put(ctx, "/actions", map[string]string{"action_type": "SendCtrlAltDel"})
	done := make(chan error, 1)
	go func() { done <- m.cmd.Wait() }()
	select {
	case <-done:
	case <-time.After(2 * time.Second):
		_ = m.cmd.Process.Kill()
		<-done
	}
	_ = os.Remove(m.cfg.SocketPath)
	return nil
}

// PID returns the Firecracker VMM pid.
func (m *Machine) PID() int {
	if m.cmd == nil || m.cmd.Process == nil {
		return 0
	}
	return m.cmd.Process.Pid
}

// Alive reports whether the VMM process still exists and is not a zombie.
// Firecracker is Linux-only, so /proc provides the missing exited-but-unreaped
// distinction that signal 0 cannot detect.
func (m *Machine) Alive() bool {
	if m == nil || m.cmd == nil || m.cmd.Process == nil {
		return false
	}
	if m.cmd.ProcessState != nil && m.cmd.ProcessState.Exited() {
		return false
	}
	if err := m.cmd.Process.Signal(syscall.Signal(0)); err != nil {
		return false
	}
	stat, err := os.ReadFile(fmt.Sprintf("/proc/%d/stat", m.cmd.Process.Pid))
	if err == nil {
		if end := bytes.LastIndexByte(stat, ')'); end >= 0 && end+2 < len(stat) {
			switch stat[end+2] {
			case 'Z', 'X':
				return false
			}
		}
	}
	return true
}

// WaitTCP waits until addr accepts TCP connections (guest SSH ready).
func WaitTCP(ctx context.Context, addr string, timeout time.Duration) error {
	deadline := time.Now().Add(timeout)
	var d net.Dialer
	for {
		c, err := d.DialContext(ctx, "tcp", addr)
		if err == nil {
			_ = c.Close()
			return nil
		}
		if time.Now().After(deadline) {
			return fmt.Errorf("timeout waiting for %s: %w", addr, err)
		}
		select {
		case <-ctx.Done():
			return ctx.Err()
		case <-time.After(100 * time.Millisecond):
		}
	}
}

// Available reports whether /dev/kvm exists (required to boot).
func Available() bool {
	_, err := os.Stat("/dev/kvm")
	return err == nil
}

func newUnixHTTPClient(socketPath string) *http.Client {
	return &http.Client{
		Transport: &http.Transport{
			DialContext: func(ctx context.Context, _, _ string) (net.Conn, error) {
				var d net.Dialer
				return d.DialContext(ctx, "unix", socketPath)
			},
		},
		Timeout: 30 * time.Second,
	}
}

func readLogTail(path string, max int) string {
	if path == "" {
		return ""
	}
	b, err := os.ReadFile(path)
	if err != nil || len(b) == 0 {
		return ""
	}
	if len(b) > max {
		b = b[len(b)-max:]
	}
	return "\n--- firecracker log ---\n" + string(b)
}

func processExitErr(cmd *exec.Cmd) string {
	if cmd == nil || cmd.ProcessState == nil {
		// Non-blocking check: if already exited, Wait returns quickly.
		if cmd != nil && cmd.Process != nil {
			ch := make(chan error, 1)
			go func() { ch <- cmd.Wait() }()
			select {
			case err := <-ch:
				if err != nil {
					return fmt.Sprintf("\n--- firecracker exit ---\n%v", err)
				}
				return "\n--- firecracker exit ---\nexited 0"
			case <-time.After(50 * time.Millisecond):
				return ""
			}
		}
		return ""
	}
	return fmt.Sprintf("\n--- firecracker exit ---\n%s", cmd.ProcessState.String())
}

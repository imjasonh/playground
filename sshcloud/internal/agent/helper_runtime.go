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
	"github.com/imjasonh/playground/sshcloud/internal/taphelper"
	"github.com/imjasonh/playground/sshcloud/internal/vmmhelper"
)

// HelperRuntime is the production runtime. The agent performs Firecracker API
// calls through a peer-authenticated proxy but delegates every privileged
// process and network lifecycle operation to the host helpers.
type HelperRuntime struct {
	VMM vmmhelper.Client
	TAP taphelper.Client
}

// NewHelperRuntime connects the production runtime to fixed local sockets.
func NewHelperRuntime(vmmSocket, tapSocket string) HelperRuntime {
	return HelperRuntime{
		VMM: vmmhelper.Client{SocketPath: vmmSocket},
		TAP: taphelper.Client{SocketPath: tapSocket},
	}
}

func (r HelperRuntime) Available() bool {
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()
	return r.Ready(ctx) == nil
}

func (r HelperRuntime) Ready(ctx context.Context) error {
	if err := r.VMM.Ready(ctx); err != nil {
		return fmt.Errorf("VMM helper: %w", err)
	}
	if err := r.TAP.Ready(ctx); err != nil {
		return fmt.Errorf("TAP helper: %w", err)
	}
	return nil
}

func (HelperRuntime) SnapshotLayout() string {
	return hostisolation.SnapshotLayoutJailer
}

func (r HelperRuntime) CreateTap(ctx context.Context, name, hostIP string) error {
	vmID, err := hostisolation.VMIDFromTapName(name)
	if err != nil {
		return err
	}
	return r.TAP.Create(ctx, vmID, hostIP)
}

func (r HelperRuntime) DeleteTap(ctx context.Context, name, hostIP string) error {
	if name == "" {
		return nil
	}
	vmID, err := hostisolation.VMIDFromTapName(name)
	if err != nil {
		return err
	}
	return r.TAP.Delete(ctx, vmID, hostIP)
}

func (r HelperRuntime) Boot(ctx context.Context, spec BootSpec) (machine, string, error) {
	vmID, err := validateHelperSpec(spec.WorkDir, spec.TapName)
	if err != nil {
		return nil, "", err
	}
	response, err := r.VMM.Launch(ctx, vmmhelper.LaunchRequest{
		VMID: vmID, Mode: vmmhelper.LaunchCold, VCPUs: spec.VCPUs, MemMiB: spec.MemMiB,
		Identity: spec.Identity,
	})
	if err != nil {
		cleanupCtx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
		defer cancel()
		_ = r.VMM.Kill(cleanupCtx, vmID)
		return nil, "", err
	}
	api := firecracker.Attach(response.APISocket)
	cleanup := func(cause error) (machine, string, error) {
		cleanupCtx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
		defer cancel()
		_ = r.VMM.Kill(cleanupCtx, vmID)
		return nil, "", cause
	}
	if err := validateLaunchIdentity(vmID, response); err != nil {
		return cleanup(err)
	}
	if err := api.ConfigureAndStart(ctx, firecracker.Config{
		SocketPath:  response.APISocket,
		KernelPath:  hostisolation.JailedKernelPath,
		RootfsPath:  hostisolation.JailedRootfsPath,
		BootArgs:    spec.BootArgs,
		VCPUs:       spec.VCPUs,
		MemMiB:      spec.MemMiB,
		CPUTemplate: spec.CPUTemplate,
		TapDevice:   spec.TapName,
		GuestMAC:    spec.GuestMAC,
	}); err != nil {
		return cleanup(err)
	}
	m := &helperMachine{vmID: vmID, workDir: spec.WorkDir, api: api, vmm: r.VMM}
	addr := net.JoinHostPort(spec.GuestIP, "22")
	if err := firecracker.WaitTCP(ctx, addr, 30*time.Second); err != nil {
		_ = m.Stop()
		return nil, "", fmt.Errorf("guest SSH not ready: %w (see bounded host Firecracker diagnostics)", err)
	}
	return m, addr, nil
}

func (r HelperRuntime) Restore(ctx context.Context, spec RestoreSpec) (machine, string, error) {
	vmID, err := validateHelperSpec(spec.WorkDir, spec.TapName)
	if err != nil {
		return nil, "", err
	}
	if err := validateRestoreLayout(spec); err != nil {
		return nil, "", err
	}
	if err := rootfs.Clone(spec.RootfsSrc, spec.RootfsDst); err != nil {
		return nil, "", err
	}
	if err := r.CreateTap(ctx, spec.TapName, spec.HostIP); err != nil {
		return nil, "", fmt.Errorf("recreate tap: %w", err)
	}
	keepTap := false
	defer func() {
		if !keepTap {
			cleanupCtx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
			defer cancel()
			_ = r.DeleteTap(cleanupCtx, spec.TapName, spec.HostIP)
		}
	}()
	response, err := r.VMM.Launch(ctx, vmmhelper.LaunchRequest{
		VMID: vmID, Mode: vmmhelper.LaunchRestore, VCPUs: spec.VCPUs, MemMiB: spec.MemMiB,
		Identity: spec.Identity,
	})
	if err != nil {
		cleanupCtx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
		defer cancel()
		_ = r.VMM.Kill(cleanupCtx, vmID)
		return nil, "", err
	}
	api := firecracker.Attach(response.APISocket)
	m := &helperMachine{vmID: vmID, workDir: spec.WorkDir, api: api, vmm: r.VMM}
	fail := func(cause error) (machine, string, error) {
		_ = m.Kill()
		return nil, "", cause
	}
	if err := validateLaunchIdentity(vmID, response); err != nil {
		return fail(err)
	}
	if err := api.LoadSnapshot(ctx, firecracker.SnapshotFiles{
		StatePath: hostisolation.JailedSnapshotState,
		MemPath:   hostisolation.JailedSnapshotMemory,
	}, false); err != nil {
		return fail(fmt.Errorf("snapshot/load: %w", err))
	}
	if err := api.Resume(ctx); err != nil {
		return fail(fmt.Errorf("resume: %w", err))
	}
	addr := net.JoinHostPort(spec.GuestIP, "22")
	if err := firecracker.WaitTCP(ctx, addr, 30*time.Second); err != nil {
		return fail(fmt.Errorf("guest SSH not ready after wake: %w (see bounded host Firecracker diagnostics)", err))
	}
	keepTap = true
	return m, addr, nil
}

func validateHelperSpec(workDir, tapName string) (string, error) {
	vmID, err := hostisolation.VMIDFromWorkDir(workDir)
	if err != nil {
		return "", err
	}
	wantTap, _ := hostisolation.TapName(vmID)
	if tapName != wantTap {
		return "", fmt.Errorf("TAP %q does not match VM %s", tapName, vmID)
	}
	return vmID, nil
}

func validateRestoreLayout(spec RestoreSpec) error {
	restoreDir := filepath.Join(spec.WorkDir, hostisolation.HostRestoreDir)
	for label, gotWant := range map[string][2]string{
		"snapshot state":  {spec.StatePath, filepath.Join(restoreDir, "vm.state")},
		"snapshot memory": {spec.MemPath, filepath.Join(restoreDir, "vm.mem")},
		"snapshot rootfs": {spec.RootfsSrc, filepath.Join(restoreDir, "rootfs.ext4")},
		"working rootfs":  {spec.RootfsDst, filepath.Join(spec.WorkDir, "rootfs.ext4")},
	} {
		if filepath.Clean(gotWant[0]) != filepath.Clean(gotWant[1]) {
			return fmt.Errorf("%s path is outside the fixed restore layout", label)
		}
	}
	return nil
}

func validateLaunchIdentity(vmID string, response vmmhelper.LaunchResponse) error {
	want, err := hostisolation.SandboxID(vmID)
	if err != nil {
		return err
	}
	if response.UID != want || response.GID != want {
		return fmt.Errorf("VMM helper returned unexpected sandbox identity %d:%d", response.UID, response.GID)
	}
	if !filepath.IsAbs(response.APISocket) || filepath.Clean(response.APISocket) != response.APISocket ||
		filepath.Base(response.APISocket) != vmID+".sock" {
		return fmt.Errorf("VMM helper returned unexpected API proxy path")
	}
	return nil
}

type helperMachine struct {
	vmID    string
	workDir string
	api     *firecracker.Machine
	vmm     vmmhelper.Client
}

func (m *helperMachine) Alive() bool {
	ctx, cancel := context.WithTimeout(context.Background(), time.Second)
	defer cancel()
	alive, err := m.vmm.Alive(ctx, m.vmID)
	return err == nil && alive
}

func (m *helperMachine) Pause(ctx context.Context) error {
	return m.api.Pause(ctx)
}

func (m *helperMachine) Resume(ctx context.Context) error {
	return m.api.Resume(ctx)
}

func (m *helperMachine) CreateSnapshot(ctx context.Context, files firecracker.SnapshotFiles) error {
	wantDir := filepath.Join(m.workDir, hostisolation.HostSnapshotDir)
	if filepath.Clean(files.StatePath) != filepath.Join(wantDir, "vm.state") ||
		filepath.Clean(files.MemPath) != filepath.Join(wantDir, "vm.mem") {
		return fmt.Errorf("snapshot output is outside the fixed layout")
	}
	if err := m.api.CreateSnapshot(ctx, firecracker.SnapshotFiles{
		StatePath: hostisolation.JailedSnapshotState,
		MemPath:   hostisolation.JailedSnapshotMemory,
	}); err != nil {
		return err
	}
	return m.vmm.ExportSnapshot(ctx, m.vmID)
}

func (m *helperMachine) Stop() error {
	shutdownCtx, cancel := context.WithTimeout(context.Background(), 2*time.Second)
	requestErr := m.api.RequestShutdown(shutdownCtx)
	cancel()
	deadline := time.Now().Add(2 * time.Second)
	for time.Now().Before(deadline) && m.Alive() {
		time.Sleep(20 * time.Millisecond)
	}
	killCtx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
	defer cancel()
	killErr := m.vmm.Kill(killCtx, m.vmID)
	if killErr != nil && requestErr != nil {
		return fmt.Errorf("graceful shutdown request failed (%v); forced termination: %w", requestErr, killErr)
	}
	return killErr
}

func (m *helperMachine) Kill() error {
	ctx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
	defer cancel()
	return m.vmm.Kill(ctx, m.vmID)
}

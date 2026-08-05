// Package vmmhelper launches and owns jailed Firecracker processes on behalf of
// the unprivileged production agent.
package vmmhelper

import (
	"context"
	"errors"
	"fmt"

	"github.com/imjasonh/playground/sshcloud/internal/genid"
	"github.com/imjasonh/playground/sshcloud/internal/helperrpc"
	"github.com/imjasonh/playground/sshcloud/internal/hostisolation"
	"github.com/imjasonh/playground/sshcloud/internal/observability"
)

const (
	operationReady          = "ready"
	operationLaunch         = "launch"
	operationAlive          = "alive"
	operationKill           = "kill"
	operationExportSnapshot = "export-snapshot"
)

// LaunchMode selects one of the two fixed staging layouts.
type LaunchMode string

const (
	LaunchCold    LaunchMode = "cold"
	LaunchRestore LaunchMode = "restore"
)

// LaunchRequest deliberately contains no executable, host path, API argument,
// cgroup knob, UID, or GID. Those are fixed or derived by the root helper.
type LaunchRequest struct {
	VMID     string                        `json:"vm_id"`
	Mode     LaunchMode                    `json:"mode"`
	VCPUs    int64                         `json:"vcpus"`
	MemMiB   int64                         `json:"mem_mib"`
	Identity observability.RuntimeIdentity `json:"identity"`
}

func (r LaunchRequest) validate() error {
	if err := hostisolation.ValidateVMID(r.VMID); err != nil {
		return err
	}
	switch r.Mode {
	case LaunchCold, LaunchRestore:
	default:
		return fmt.Errorf("invalid launch mode %q", r.Mode)
	}
	switch {
	case r.VCPUs == 1 && r.MemMiB == 128:
	case r.VCPUs == 2 && r.MemMiB == 512:
	default:
		return fmt.Errorf("unsupported VM resources %d vCPU/%d MiB", r.VCPUs, r.MemMiB)
	}
	if err := r.Identity.Validate(false); err != nil {
		return fmt.Errorf("log identity: %w", err)
	}
	if r.Identity.RunID == "" {
		return fmt.Errorf("log identity run id is required")
	}
	if r.Identity.Host != "" {
		return fmt.Errorf("launch request cannot select host attribution")
	}
	agentApp := genid.AgentApp(r.Identity.App, r.Identity.Generation)
	if expected := hostisolation.VMIDForInstance(r.Identity.User, agentApp); r.VMID != expected {
		return fmt.Errorf("VM id does not match authoritative log identity")
	}
	return nil
}

// LaunchResponse contains only helper-derived values.
type LaunchResponse struct {
	APISocket string `json:"api_socket"`
	UID       uint32 `json:"uid"`
	GID       uint32 `json:"gid"`
}

type vmRequest struct {
	VMID string `json:"vm_id"`
}

type aliveResponse struct {
	Alive bool `json:"alive"`
}

type killResponse struct {
	Terminated   bool   `json:"terminated"`
	CleanupError string `json:"cleanup_error,omitempty"`
}

// TerminationError distinguishes failure to prove cgroup termination from a
// later jail/rootfs cleanup error after termination was already proved.
type TerminationError struct {
	VMID         string
	WasConfirmed bool
	Underlying   error
}

func (e *TerminationError) Error() string {
	if e.WasConfirmed {
		return fmt.Sprintf("VM %s termination confirmed but cleanup failed: %v", e.VMID, e.Underlying)
	}
	return fmt.Sprintf("VM %s termination was not confirmed: %v", e.VMID, e.Underlying)
}

func (e *TerminationError) Unwrap() error              { return e.Underlying }
func (e *TerminationError) TerminationConfirmed() bool { return e.WasConfirmed }

// TerminationConfirmed reports whether err proves that the complete derived
// cgroup was empty, even when later non-lifecycle cleanup failed.
func TerminationConfirmed(err error) bool {
	if err == nil {
		return true
	}
	var terminationErr *TerminationError
	return errors.As(err, &terminationErr) && terminationErr.TerminationConfirmed()
}

// Client talks to the root VMM helper.
type Client struct {
	SocketPath string
}

func (c Client) call(ctx context.Context, operation string, request, response any) error {
	if c.SocketPath == "" {
		return fmt.Errorf("VMM helper socket required")
	}
	return helperrpc.Call(ctx, c.SocketPath, operation, request, response)
}

// Ready verifies the helper, pinned assets, KVM, and cgroup v2 substrate.
func (c Client) Ready(ctx context.Context) error {
	return c.call(ctx, operationReady, struct{}{}, nil)
}

// Launch stages one fixed VM layout and starts the pinned jailer.
func (c Client) Launch(ctx context.Context, request LaunchRequest) (LaunchResponse, error) {
	if err := request.validate(); err != nil {
		return LaunchResponse{}, err
	}
	var response LaunchResponse
	err := c.call(ctx, operationLaunch, request, &response)
	return response, err
}

// Alive asks the process-owning helper, rather than probing a client-visible
// PID, whether the jailer/Firecracker process is still running.
func (c Client) Alive(ctx context.Context, vmID string) (bool, error) {
	if err := hostisolation.ValidateVMID(vmID); err != nil {
		return false, err
	}
	var response aliveResponse
	if err := c.call(ctx, operationAlive, vmRequest{VMID: vmID}, &response); err != nil {
		return false, err
	}
	return response.Alive, nil
}

// Kill terminates the complete derived cgroup and then removes its jail/API
// proxy. It is idempotent. A TerminationError says whether cgroup emptiness was
// proved before a later cleanup failure.
func (c Client) Kill(ctx context.Context, vmID string) error {
	if err := hostisolation.ValidateVMID(vmID); err != nil {
		return err
	}
	var response killResponse
	if err := c.call(ctx, operationKill, vmRequest{VMID: vmID}, &response); err != nil {
		return &TerminationError{VMID: vmID, Underlying: err}
	}
	if !response.Terminated {
		return &TerminationError{VMID: vmID, Underlying: fmt.Errorf("helper returned no termination proof")}
	}
	if response.CleanupError != "" {
		return &TerminationError{
			VMID: vmID, WasConfirmed: true, Underlying: errors.New(response.CleanupError),
		}
	}
	return nil
}

// ExportSnapshot copies only the fixed jailed state, memory, and rootfs files
// into vm-<id>/snap after Firecracker has completed snapshot/create.
func (c Client) ExportSnapshot(ctx context.Context, vmID string) error {
	if err := hostisolation.ValidateVMID(vmID); err != nil {
		return err
	}
	return c.call(ctx, operationExportSnapshot, vmRequest{VMID: vmID}, nil)
}

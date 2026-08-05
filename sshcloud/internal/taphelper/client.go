// Package taphelper owns the only CAP_NET_ADMIN process in the production
// agent stack.
package taphelper

import (
	"context"
	"fmt"

	"github.com/imjasonh/playground/sshcloud/internal/helperrpc"
	"github.com/imjasonh/playground/sshcloud/internal/hostisolation"
)

const (
	operationReady  = "ready"
	operationCreate = "create"
	operationDelete = "delete"
)

// CreateRequest contains no TAP name, prefix, owner, rule, command, or path.
// All of those are fixed or derived by the helper.
type CreateRequest struct {
	VMID   string `json:"vm_id"`
	HostIP string `json:"host_ip"`
}

type vmRequest struct {
	VMID string `json:"vm_id"`
}

// Client talks to the CAP_NET_ADMIN-only TAP helper.
type Client struct {
	SocketPath string
}

func (c Client) call(ctx context.Context, operation string, request any) error {
	if c.SocketPath == "" {
		return fmt.Errorf("TAP helper socket required")
	}
	return helperrpc.Call(ctx, c.SocketPath, operation, request, nil)
}

// Ready verifies peer service readiness and effective CAP_NET_ADMIN.
func (c Client) Ready(ctx context.Context) error {
	return c.call(ctx, operationReady, struct{}{})
}

// Create constructs the one fixed TAP/ruleset for a VM.
func (c Client) Create(ctx context.Context, vmID, hostIP string) error {
	if err := hostisolation.ValidateVMID(vmID); err != nil {
		return err
	}
	return c.call(ctx, operationCreate, CreateRequest{VMID: vmID, HostIP: hostIP})
}

// Delete removes the fixed TAP/ruleset for a VM. It is idempotent.
func (c Client) Delete(ctx context.Context, vmID string) error {
	if err := hostisolation.ValidateVMID(vmID); err != nil {
		return err
	}
	return c.call(ctx, operationDelete, vmRequest{VMID: vmID})
}

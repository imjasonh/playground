package agent

import (
	"context"

	"github.com/imjasonh/playground/sshcloud/internal/firecracker"
)

// stubMachine satisfies machine for manager unit tests (no Firecracker).
type stubMachine struct{}

func (stubMachine) Alive() bool                                                     { return true }
func (stubMachine) Pause(context.Context) error                                     { return nil }
func (stubMachine) Resume(context.Context) error                                    { return nil }
func (stubMachine) CreateSnapshot(context.Context, firecracker.SnapshotFiles) error { return nil }
func (stubMachine) Stop() error                                                     { return nil }
func (stubMachine) Kill() error                                                     { return nil }

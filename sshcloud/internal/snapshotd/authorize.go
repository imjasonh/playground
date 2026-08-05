// Package snapshotd owns the authenticated snapshot storage boundary.
package snapshotd

import (
	"context"
	"errors"
	"fmt"
	"time"

	"github.com/imjasonh/playground/sshcloud/internal/controlauth"
	"github.com/imjasonh/playground/sshcloud/internal/placement"
	"github.com/imjasonh/playground/sshcloud/internal/snapshot"
)

type Action string

const (
	ActionPut    Action = "put"
	ActionGet    Action = "get"
	ActionHas    Action = "has"
	ActionMeta   Action = "meta"
	ActionDelete Action = "delete"
)

var ErrForbidden = errors.New("snapshot operation is not authorized")

type Authorizer struct {
	Placement placement.Store
	Now       func() time.Time
}

// Authorize binds every package operation to a complete placement reference
// and one exact GCE VM incarnation.
func (a *Authorizer) Authorize(ctx context.Context, caller controlauth.Identity, ref snapshot.Ref, action Action) error {
	if a == nil || a.Placement == nil {
		return fmt.Errorf("%w: placement store is unavailable", ErrForbidden)
	}
	if err := ref.Validate(); err != nil {
		return err
	}
	if caller.InstanceName == "" || caller.InstanceID == "" {
		return fmt.Errorf("%w: caller has no verified GCE instance identity", ErrForbidden)
	}
	record, ok, err := a.Placement.GetRecord(ctx, ref.User, ref.App)
	if err != nil {
		return err
	}
	if !ok || record.User != ref.User || record.App != ref.App {
		return ErrForbidden
	}

	if record.Operation.Kind == "" {
		if !generationInRecord(record.Generations, ref.Gen) ||
			!sameHost(caller, record.HostID, record.HostInstanceID) {
			return ErrForbidden
		}
		switch action {
		case ActionPut, ActionGet, ActionHas, ActionMeta, ActionDelete:
			return nil
		default:
			return ErrForbidden
		}
	}
	if record.Operation.ID == "" || record.Operation.Sequence <= 0 {
		return ErrForbidden
	}

	now := time.Now()
	if a.Now != nil {
		now = a.Now()
	}
	if record.LeaseOwner == "" || record.LeaseUntilUnix <= now.UnixNano() {
		return ErrForbidden
	}
	switch record.Operation.Kind {
	case "stop":
		if record.Operation.SourceHost != record.HostID ||
			(record.HostInstanceID != "" &&
				record.Operation.SourceInstanceID != record.HostInstanceID) ||
			!generationInOperation(record.Operation.Generations, ref.Gen) ||
			!sameHost(
				caller,
				record.Operation.SourceHost,
				record.Operation.SourceInstanceID,
			) {
			return ErrForbidden
		}
		// Stop is the only journaled lifecycle operation permitted to remove a
		// current package. Its source name and immutable incarnation are pinned
		// before the agent crosses the termination/deletion boundary.
		switch action {
		case ActionHas, ActionMeta, ActionDelete:
			return nil
		default:
			return ErrForbidden
		}
	case "ensure":
		if record.HostID != "" && record.Operation.TargetHost != record.HostID {
			return ErrForbidden
		}
		if record.HostInstanceID != "" && record.Operation.TargetInstanceID != record.HostInstanceID {
			return ErrForbidden
		}
		if sameHost(caller, record.HostID, record.HostInstanceID) &&
			generationInRecord(record.Generations, ref.Gen) {
			switch action {
			case ActionPut, ActionGet, ActionHas, ActionMeta, ActionDelete:
				return nil
			default:
				return ErrForbidden
			}
		}
		if !generationInOperation(record.Operation.Generations, ref.Gen) {
			return ErrForbidden
		}
		if !sameHost(caller, record.Operation.TargetHost, record.Operation.TargetInstanceID) {
			return ErrForbidden
		}
		switch action {
		case ActionGet, ActionHas, ActionMeta, ActionDelete:
			return nil
		default:
			return ErrForbidden
		}
	case "migrate", "drain":
		if record.Operation.SourceHost != record.HostID ||
			(record.HostInstanceID != "" && record.Operation.SourceInstanceID != record.HostInstanceID) {
			return ErrForbidden
		}
		if !generationInOperation(record.Operation.Generations, ref.Gen) {
			return ErrForbidden
		}
		source := sameHost(caller, record.Operation.SourceHost, record.Operation.SourceInstanceID)
		target := sameHost(caller, record.Operation.TargetHost, record.Operation.TargetInstanceID)
		if !source && !target {
			return ErrForbidden
		}
		// Source writes the initial paused snapshot and may read it for
		// rollback. Target reads to adopt and may write a rollback snapshot.
		// Neither side may delete while the journal is live.
		switch action {
		case ActionPut, ActionGet, ActionHas, ActionMeta:
			return nil
		default:
			return ErrForbidden
		}
	default:
		return ErrForbidden
	}
}

func sameHost(caller controlauth.Identity, name, instanceID string) bool {
	return name != "" && instanceID != "" &&
		caller.InstanceName == name && caller.InstanceID == instanceID
}

func generationInRecord(generations []placement.Generation, gen string) bool {
	if len(generations) == 0 {
		return gen == ""
	}
	for _, generation := range generations {
		if generation.Gen == gen {
			return true
		}
	}
	return false
}

func generationInOperation(generations []string, gen string) bool {
	for _, generation := range generations {
		if generation == gen {
			return true
		}
	}
	return false
}

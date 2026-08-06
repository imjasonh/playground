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

// Fence is the complete durable authorization decision that must still match
// immediately before an encrypted current-pointer publish or delete CAS.
type Fence struct {
	Ref                snapshot.Ref
	RecordRevision     int64
	OperationID        string
	OperationSequence  int64
	OperationKind      string
	CallerInstanceName string
	CallerInstanceID   string
	Action             Action
}

// Authorize binds every package operation to a complete placement reference
// and one exact GCE VM incarnation.
func (a *Authorizer) Authorize(
	ctx context.Context,
	caller controlauth.Identity,
	ref snapshot.Ref,
	action Action,
) (Fence, error) {
	if a == nil || a.Placement == nil {
		return Fence{}, fmt.Errorf("%w: placement store is unavailable", ErrForbidden)
	}
	if err := ref.Validate(); err != nil {
		return Fence{}, err
	}
	if caller.InstanceName == "" || caller.InstanceID == "" {
		return Fence{}, fmt.Errorf("%w: caller has no verified GCE instance identity", ErrForbidden)
	}
	record, ok, err := a.Placement.GetRecord(ctx, ref.User, ref.App)
	if err != nil {
		return Fence{}, err
	}
	if !ok || record.User != ref.User || record.App != ref.App {
		return Fence{}, ErrForbidden
	}
	if err := a.authorizeRecord(record, caller, ref, action); err != nil {
		return Fence{}, err
	}
	return fenceFor(record, caller, ref, action), nil
}

// Revalidate requires the exact record revision, operation ID/sequence, action,
// and caller incarnation captured before request staging.
func (a *Authorizer) Revalidate(ctx context.Context, fence Fence) error {
	if a == nil || a.Placement == nil {
		return fmt.Errorf("%w: placement store is unavailable", ErrForbidden)
	}
	if err := fence.Ref.Validate(); err != nil {
		return ErrForbidden
	}
	if fence.CallerInstanceName == "" || fence.CallerInstanceID == "" || fence.Action == "" {
		return ErrForbidden
	}
	record, ok, err := a.Placement.GetRecord(ctx, fence.Ref.User, fence.Ref.App)
	if err != nil {
		return err
	}
	if !ok || record.User != fence.Ref.User || record.App != fence.Ref.App ||
		record.Revision != fence.RecordRevision ||
		record.Operation.ID != fence.OperationID ||
		record.Operation.Sequence != fence.OperationSequence ||
		record.Operation.Kind != fence.OperationKind {
		return ErrForbidden
	}
	caller := controlauth.Identity{
		InstanceName: fence.CallerInstanceName,
		InstanceID:   fence.CallerInstanceID,
	}
	if err := a.authorizeRecord(record, caller, fence.Ref, fence.Action); err != nil {
		return err
	}
	if fenceFor(record, caller, fence.Ref, fence.Action) != fence {
		return ErrForbidden
	}
	return nil
}

func (a *Authorizer) authorizeRecord(
	record placement.Record,
	caller controlauth.Identity,
	ref snapshot.Ref,
	action Action,
) error {
	now := time.Now()
	if a.Now != nil {
		now = a.Now()
	}
	if record.Operation.Kind == "" {
		if record.LeaseOwner != "" && record.LeaseUntilUnix > now.UnixNano() {
			return ErrForbidden
		}
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

func fenceFor(
	record placement.Record,
	caller controlauth.Identity,
	ref snapshot.Ref,
	action Action,
) Fence {
	return Fence{
		Ref: ref, RecordRevision: record.Revision,
		OperationID: record.Operation.ID, OperationSequence: record.Operation.Sequence,
		OperationKind:      record.Operation.Kind,
		CallerInstanceName: caller.InstanceName, CallerInstanceID: caller.InstanceID,
		Action: action,
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

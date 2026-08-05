package snapshotd

import (
	"context"
	"errors"
	"testing"
	"time"

	"github.com/imjasonh/playground/sshcloud/internal/controlauth"
	"github.com/imjasonh/playground/sshcloud/internal/placement"
	"github.com/imjasonh/playground/sshcloud/internal/snapshot"
)

func TestAuthorizationFollowsCurrentPlacementAndExactInstance(t *testing.T) {
	t.Parallel()
	ctx := t.Context()
	now := time.Unix(1_800_000_000, 0)
	place := placement.NewMemory()
	ref := snapshot.Ref{User: "alice", App: "fortune", Gen: "g1"}
	setPlacement(t, place, ref, "source", "101", now)
	auth := &Authorizer{Placement: place, Now: func() time.Time { return now }}
	source := controlauth.Identity{InstanceName: "source", InstanceID: "101"}

	for _, action := range []Action{ActionPut, ActionGet, ActionHas, ActionMeta, ActionDelete} {
		if err := auth.Authorize(ctx, source, ref, action); err != nil {
			t.Fatalf("current host %s: %v", action, err)
		}
	}
	for _, caller := range []controlauth.Identity{
		{InstanceName: "source", InstanceID: "recreated"},
		{InstanceName: "other", InstanceID: "101"},
	} {
		if err := auth.Authorize(ctx, caller, ref, ActionGet); !errors.Is(err, ErrForbidden) {
			t.Fatalf("caller %+v authorized: %v", caller, err)
		}
	}
}

func TestMigrationFenceIsMethodSpecificAndCommitRevokesSource(t *testing.T) {
	t.Parallel()
	ctx := context.Background()
	now := time.Unix(1_800_000_000, 0)
	place := placement.NewMemory()
	ref := snapshot.Ref{User: "alice", App: "fortune", Gen: "g1"}
	setPlacement(t, place, ref, "source", "101", now)
	lease, err := place.Acquire(ctx, ref.User, ref.App, "move-1", time.Minute, now)
	if err != nil {
		t.Fatal(err)
	}
	operation := placement.Operation{
		ID: "move-1", Kind: "migrate", Phase: "adopting",
		SourceHost: "source", SourceInstanceID: "101",
		TargetHost: "target", TargetInstanceID: "202", Generations: []string{ref.Gen},
	}
	if err := place.Mark(ctx, lease, operation); err != nil {
		t.Fatal(err)
	}
	auth := &Authorizer{Placement: place, Now: func() time.Time { return now.Add(10 * time.Second) }}
	source := controlauth.Identity{InstanceName: "source", InstanceID: "101"}
	target := controlauth.Identity{InstanceName: "target", InstanceID: "202"}
	for _, caller := range []controlauth.Identity{source, target} {
		for _, action := range []Action{ActionPut, ActionGet, ActionHas, ActionMeta} {
			if err := auth.Authorize(ctx, caller, ref, action); err != nil {
				t.Fatalf("%s caller=%+v: %v", action, caller, err)
			}
		}
		if err := auth.Authorize(ctx, caller, ref, ActionDelete); !errors.Is(err, ErrForbidden) {
			t.Fatalf("journal participant deleted snapshot: %v", err)
		}
	}
	otherGen := snapshot.Ref{User: ref.User, App: ref.App, Gen: "g2"}
	if err := auth.Authorize(ctx, target, otherGen, ActionGet); !errors.Is(err, ErrForbidden) {
		t.Fatalf("target crossed generation fence: %v", err)
	}
	if err := place.CommitStateIdentity(
		ctx, lease, "target", "202",
		[]placement.Generation{{Gen: ref.Gen, State: "running"}}, now.Add(20*time.Second),
	); err != nil {
		t.Fatal(err)
	}
	if err := auth.Authorize(ctx, source, ref, ActionGet); !errors.Is(err, ErrForbidden) {
		t.Fatalf("stale source retained access after commit: %v", err)
	}
	if err := auth.Authorize(ctx, target, ref, ActionDelete); err != nil {
		t.Fatalf("new current target could not delete: %v", err)
	}
}

func TestEnsureFenceOnlyGrantsTargetRestoreMethodsForExactGeneration(t *testing.T) {
	t.Parallel()
	ctx := t.Context()
	now := time.Unix(1_800_000_000, 0)
	place := placement.NewMemory()
	currentRef := snapshot.Ref{User: "alice", App: "fortune", Gen: "g1"}
	targetRef := snapshot.Ref{User: "alice", App: "fortune", Gen: "g2"}
	setPlacement(t, place, currentRef, "source", "101", now)
	lease, err := place.Acquire(ctx, currentRef.User, currentRef.App, "ensure-1", time.Minute, now)
	if err != nil {
		t.Fatal(err)
	}
	if err := place.Mark(ctx, lease, placement.Operation{
		ID: "ensure-1", Kind: "ensure", Phase: "ensuring",
		TargetHost: "source", TargetInstanceID: "101", Generations: []string{targetRef.Gen},
	}); err != nil {
		t.Fatal(err)
	}
	auth := &Authorizer{Placement: place, Now: func() time.Time { return now.Add(10 * time.Second) }}
	source := controlauth.Identity{InstanceName: "source", InstanceID: "101"}
	target := source

	if err := auth.Authorize(ctx, source, currentRef, ActionPut); err != nil {
		t.Fatalf("current source lost its existing generation: %v", err)
	}
	for _, action := range []Action{ActionGet, ActionHas, ActionMeta, ActionDelete} {
		if err := auth.Authorize(ctx, target, targetRef, action); err != nil {
			t.Fatalf("ensure target %s: %v", action, err)
		}
	}
	if err := auth.Authorize(ctx, target, targetRef, ActionPut); !errors.Is(err, ErrForbidden) {
		t.Fatalf("ensure target published before placement: %v", err)
	}
	other := controlauth.Identity{InstanceName: "target", InstanceID: "202"}
	if err := auth.Authorize(ctx, other, targetRef, ActionGet); !errors.Is(err, ErrForbidden) {
		t.Fatalf("unfenced ensure host gained access: %v", err)
	}
}

func TestExpiredOperationFenceDeniesBothParticipants(t *testing.T) {
	t.Parallel()
	ctx := context.Background()
	now := time.Unix(1_800_000_000, 0)
	place := placement.NewMemory()
	ref := snapshot.Ref{User: "alice", App: "fortune", Gen: "g1"}
	setPlacement(t, place, ref, "source", "101", now)
	lease, err := place.Acquire(ctx, ref.User, ref.App, "drain-1", time.Second, now)
	if err != nil {
		t.Fatal(err)
	}
	if err := place.Mark(ctx, lease, placement.Operation{
		ID: "drain-1", Kind: "drain", Phase: "moving:g1",
		SourceHost: "source", SourceInstanceID: "101",
		TargetHost: "target", TargetInstanceID: "202", Generations: []string{ref.Gen},
	}); err != nil {
		t.Fatal(err)
	}
	auth := &Authorizer{Placement: place, Now: func() time.Time { return now.Add(2 * time.Second) }}
	for _, caller := range []controlauth.Identity{
		{InstanceName: "source", InstanceID: "101"},
		{InstanceName: "target", InstanceID: "202"},
	} {
		if err := auth.Authorize(ctx, caller, ref, ActionGet); !errors.Is(err, ErrForbidden) {
			t.Fatalf("expired fence authorized %+v: %v", caller, err)
		}
	}
}

func setPlacement(t *testing.T, place *placement.Memory, ref snapshot.Ref, host, instanceID string, now time.Time) {
	t.Helper()
	if err := place.SetIdentity(t.Context(), ref.User, ref.App, host, instanceID); err != nil {
		t.Fatal(err)
	}
	lease, err := place.Acquire(t.Context(), ref.User, ref.App, "inventory", time.Minute, now)
	if err != nil {
		t.Fatal(err)
	}
	if err := place.CommitStateIdentity(
		t.Context(), lease, host, instanceID,
		[]placement.Generation{{Gen: ref.Gen, State: "running"}}, now.Add(time.Second),
	); err != nil {
		t.Fatal(err)
	}
}

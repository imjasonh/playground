package placement

import (
	"context"
	"errors"
	"testing"
	"time"
)

func TestMemoryRoundTrip(t *testing.T) {
	m := NewMemory()
	ctx := context.Background()
	if _, ok, err := m.Get(ctx, "a", "b"); err != nil || ok {
		t.Fatalf("empty get: ok=%v err=%v", ok, err)
	}
	if err := m.SetIdentity(ctx, "a", "b", "host-1", "instance-1"); err != nil {
		t.Fatal(err)
	}
	h, ok, err := m.Get(ctx, "a", "b")
	if err != nil || !ok || h != "host-1" {
		t.Fatalf("got %q ok=%v err=%v", h, ok, err)
	}
	if err := m.Delete(ctx, "a", "b"); err != nil {
		t.Fatal(err)
	}
	if _, ok, _ := m.Get(ctx, "a", "b"); ok {
		t.Fatal("expected deleted")
	}
}

func TestMemoryLeaseFencesPlacement(t *testing.T) {
	t.Parallel()
	ctx := context.Background()
	m := NewMemory()
	now := time.Now()
	first, err := m.Acquire(ctx, "alice", "fortune", "wake-1", time.Minute, now)
	if err != nil {
		t.Fatal(err)
	}
	if _, err := m.Acquire(ctx, "alice", "fortune", "wake-2", time.Minute, now); err == nil {
		t.Fatal("concurrent owner acquired a live placement lease")
	} else {
		var held ErrLeaseHeld
		if !errors.As(err, &held) {
			t.Fatalf("error %T, want ErrLeaseHeld", err)
		}
	}
	if err := m.SetIdentity(ctx, "alice", "fortune", "host-b", "instance-b"); err == nil {
		t.Fatal("unfenced SetIdentity changed a leased placement")
	}
	if err := m.Mark(ctx, first, Operation{Kind: "migrate", SourceHost: "host-a", TargetHost: "host-b"}); err != nil {
		t.Fatal(err)
	}
	if err := m.CommitStateIdentity(ctx, first, "host-a", "instance-a", nil, now.Add(time.Second)); err != nil {
		t.Fatal(err)
	}
	host, ok, err := m.Get(ctx, "alice", "fortune")
	if err != nil || !ok || host != "host-a" {
		t.Fatalf("host=%q ok=%v err=%v", host, ok, err)
	}
	record, _, _ := m.GetRecord(ctx, "alice", "fortune")
	if record.Operation.Kind != "" {
		t.Fatalf("commit did not clear operation: %+v", record)
	}
	if err := m.CommitStateIdentity(ctx, first, "host-b", "instance-b", nil, now.Add(2*time.Second)); err == nil {
		t.Fatal("stale lease committed twice")
	}

	expired, err := m.Acquire(ctx, "alice", "fortune", "wake-3", time.Second, now.Add(3*time.Second))
	if err != nil {
		t.Fatal(err)
	}
	replacement, err := m.Acquire(ctx, "alice", "fortune", "wake-4", time.Minute, now.Add(5*time.Second))
	if err != nil {
		t.Fatal(err)
	}
	if replacement.Revision == expired.Revision {
		t.Fatal("expired lease takeover did not fence the old owner")
	}
	if err := m.CommitStateIdentity(ctx, expired, "wrong-host", "wrong-instance", nil, now.Add(5*time.Second)); err == nil {
		t.Fatal("expired owner committed after takeover")
	}
}

func TestGuardCancelsAtLocalLeaseExpiry(t *testing.T) {
	t.Parallel()
	guard, err := AcquireGuard(context.Background(), NewMemory(), "alice", "fortune", "test", 30*time.Millisecond)
	if err != nil {
		t.Fatal(err)
	}
	select {
	case <-guard.Context().Done():
	case <-time.After(time.Second):
		t.Fatal("guard continued after local lease expiry")
	}
	var lost ErrLeaseLost
	if !errors.As(guard.Err(), &lost) {
		t.Fatalf("guard error %v, want ErrLeaseLost", guard.Err())
	}
}

func TestOperationJournalRequiresExactRecoveryClaim(t *testing.T) {
	t.Parallel()
	ctx := context.Background()
	store := NewMemory()
	now := time.Now().Add(-time.Minute)
	lease, err := store.Acquire(ctx, "alice", "fortune", "crashed", time.Second, now)
	if err != nil {
		t.Fatal(err)
	}
	if err := store.Mark(ctx, lease, Operation{ID: "op-1", Kind: "drain"}); err != nil {
		t.Fatal(err)
	}
	if _, err := store.Acquire(ctx, "alice", "fortune", "normal", time.Minute, time.Now()); err == nil {
		t.Fatal("normal operation erased abandoned journal")
	} else {
		var recovery ErrRecoveryRequired
		if !errors.As(err, &recovery) {
			t.Fatalf("error %T, want ErrRecoveryRequired", err)
		}
	}
	record, _, _ := store.GetRecord(ctx, "alice", "fortune")
	recoveryLease, err := store.AcquireRecovery(ctx, record, "reconciler", time.Minute, time.Now())
	if err != nil {
		t.Fatal(err)
	}
	if err := store.Release(ctx, recoveryLease); err != nil {
		t.Fatal(err)
	}
}

func TestMemoryDeepCopiesPlacementSlicesAndRequiresHostIdentity(t *testing.T) {
	t.Parallel()
	store := NewMemory()
	now := time.Now()
	lease, err := store.Acquire(
		t.Context(), "alice", "app", "owner", time.Minute, now,
	)
	if err != nil {
		t.Fatal(err)
	}
	operation := Operation{
		Kind: "ensure", Generations: []string{"g1"},
		Desired: []Generation{{Gen: "g1", State: "running"}},
	}
	if err := store.Mark(t.Context(), lease, operation); err != nil {
		t.Fatal(err)
	}
	operation.Generations[0] = "mutated-ingress"
	operation.Desired[0].Gen = "mutated-ingress"
	record, _, _ := store.GetRecord(t.Context(), "alice", "app")
	if record.Operation.Generations[0] != "g1" || record.Operation.Desired[0].Gen != "g1" {
		t.Fatalf("Mark retained caller slices: %+v", record.Operation)
	}
	record.Operation.Generations[0] = "mutated-get"
	record.Operation.Desired[0].Gen = "mutated-get"
	records, _ := store.ListRecords(t.Context())
	records[0].Operation.Generations[0] = "mutated-list"
	record, _, _ = store.GetRecord(t.Context(), "alice", "app")
	if record.Operation.Generations[0] != "g1" || record.Operation.Desired[0].Gen != "g1" {
		t.Fatalf("record egress exposed stored slices: %+v", record.Operation)
	}

	generations := []Generation{{Gen: "g1", State: "running"}}
	if err := store.CommitStateIdentity(
		t.Context(), lease, "host-a", "", generations, now.Add(time.Second),
	); err == nil {
		t.Fatal("placement commit accepted an empty immutable host identity")
	}
	if err := store.CommitStateIdentity(
		t.Context(), lease, "host-a", "instance-a", generations, now.Add(time.Second),
	); err != nil {
		t.Fatal(err)
	}
	generations[0].Gen = "mutated-commit"
	record, _, _ = store.GetRecord(t.Context(), "alice", "app")
	if record.Generations[0].Gen != "g1" {
		t.Fatalf("commit retained caller generations: %+v", record.Generations)
	}
	record.Generations[0].Gen = "mutated-get"
	record, _, _ = store.GetRecord(t.Context(), "alice", "app")
	if record.Generations[0].Gen != "g1" {
		t.Fatalf("GetRecord exposed generations: %+v", record.Generations)
	}
	if err := store.SetIdentity(t.Context(), "bob", "app", "host-b", ""); err == nil {
		t.Fatal("SetIdentity accepted an empty immutable host identity")
	}
}

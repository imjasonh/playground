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
	if err := m.Set(ctx, "a", "b", "host-1"); err != nil {
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
	if err := m.Set(ctx, "alice", "fortune", "host-b"); err == nil {
		t.Fatal("unfenced Set changed a leased placement")
	}
	if err := m.Mark(ctx, first, Operation{Kind: "migrate", SourceHost: "host-a", TargetHost: "host-b"}); err != nil {
		t.Fatal(err)
	}
	if err := m.Commit(ctx, first, "host-a", now.Add(time.Second)); err != nil {
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
	if err := m.Commit(ctx, first, "host-b", now.Add(2*time.Second)); err == nil {
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
	if err := m.Commit(ctx, expired, "wrong-host", now.Add(5*time.Second)); err == nil {
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

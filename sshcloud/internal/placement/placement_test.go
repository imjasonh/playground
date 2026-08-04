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
	if err := m.Commit(ctx, first, "host-a", now.Add(time.Second)); err != nil {
		t.Fatal(err)
	}
	host, ok, err := m.Get(ctx, "alice", "fortune")
	if err != nil || !ok || host != "host-a" {
		t.Fatalf("host=%q ok=%v err=%v", host, ok, err)
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

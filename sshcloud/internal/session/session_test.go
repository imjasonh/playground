package session

import (
	"context"
	"errors"
	"testing"
)

func TestAdmitRejectsSecondSameGen(t *testing.T) {
	t.Parallel()
	r := NewRegistry()
	id, err := r.Admit("alice", "fortune", "")
	if err != nil {
		t.Fatal(err)
	}
	_, err = r.Admit("alice", "fortune", "")
	var busy ErrBusy
	if !errors.As(err, &busy) {
		t.Fatalf("got %v, want ErrBusy", err)
	}
	if !r.Active("alice", "fortune") {
		t.Fatal("expected active")
	}

	if _, err := r.Admit("alice", "myapp", ""); err != nil {
		t.Fatal(err)
	}
	if _, err := r.Admit("bob", "fortune", ""); err != nil {
		t.Fatal(err)
	}

	r.Release(id)
	if r.Active("alice", "fortune") {
		t.Fatal("expected released")
	}
	if _, err := r.Admit("alice", "fortune", ""); err != nil {
		t.Fatal(err)
	}
}

func TestAdmitDrainAllowsOtherGen(t *testing.T) {
	t.Parallel()
	r := NewRegistry()
	old, err := r.Admit("alice", "myapp", "g1")
	if err != nil {
		t.Fatal(err)
	}
	newID, err := r.Admit("alice", "myapp", "g2")
	if err != nil {
		t.Fatal(err)
	}
	if _, err := r.Admit("alice", "myapp", "g3"); err == nil {
		t.Fatal("expected busy at 2 slots")
	}
	if !r.ActiveGen("alice", "myapp", "g1") || !r.ActiveGen("alice", "myapp", "g2") {
		t.Fatal("both gens should be active")
	}
	r.Release(old)
	r.Release(newID)
}

func TestKickCancels(t *testing.T) {
	t.Parallel()
	r := NewRegistry()
	id, err := r.Admit("alice", "myapp", "g1")
	if err != nil {
		t.Fatal(err)
	}
	ctx, cancel := context.WithCancel(context.Background())
	r.BindCancel(id, cancel)
	if n := r.Kick("alice", "myapp", "g1"); n != 1 {
		t.Fatalf("kick count %d", n)
	}
	select {
	case <-ctx.Done():
	default:
		t.Fatal("expected cancel")
	}
	r.Release(id)
}

func TestReleaseUnknownID(t *testing.T) {
	t.Parallel()
	r := NewRegistry()
	r.Release("nope")
}

func TestInfo(t *testing.T) {
	t.Parallel()
	r := NewRegistry()
	id, err := r.Admit("alice", "myapp", "g1")
	if err != nil {
		t.Fatal(err)
	}
	user, app, gen, ok := r.Info(id)
	if !ok || user != "alice" || app != "myapp" || gen != "g1" {
		t.Fatalf("info %s %s %s ok=%v", user, app, gen, ok)
	}
	if _, _, _, ok := r.Info("missing"); ok {
		t.Fatal("expected missing")
	}
	r.Release(id)
}

package session

import (
	"context"
	"errors"
	"testing"
	"time"
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

func TestKickBeforeBindCancelsWhenBound(t *testing.T) {
	t.Parallel()
	r := NewRegistry()
	id, err := r.Admit("alice", "myapp", "g1")
	if err != nil {
		t.Fatal(err)
	}
	if n := r.Kick("alice", "myapp", "g1"); n != 1 {
		t.Fatalf("kick count %d", n)
	}
	ctx, cancel := context.WithCancel(context.Background())
	r.BindCancel(id, cancel)
	select {
	case <-ctx.Done():
	default:
		t.Fatal("late-bound session did not observe pending kick")
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

func TestFreezeThawMigrationCommands(t *testing.T) {
	t.Parallel()
	r := NewRegistry()
	id, err := r.Admit("alice", "myapp", "g1")
	if err != nil {
		t.Fatal(err)
	}
	commands := make(chan MigrationCommand)
	if frozen := r.BindMigration(id, commands); frozen {
		t.Fatal("new session unexpectedly frozen")
	}
	seen := make(chan string, 2)
	go func() {
		for command := range commands {
			seen <- command.Kind
			command.Ack <- nil
		}
	}()
	ctx, cancel := context.WithTimeout(context.Background(), time.Second)
	defer cancel()
	if count, err := r.Freeze(ctx, "alice", "myapp", "g1"); err != nil || count != 1 {
		t.Fatalf("freeze count=%d err=%v", count, err)
	}
	if count, err := r.Thaw(ctx, "alice", "myapp", "g1"); err != nil || count != 1 {
		t.Fatalf("thaw count=%d err=%v", count, err)
	}
	if first, second := <-seen, <-seen; first != MigrationFreeze || second != MigrationThaw {
		t.Fatalf("commands %q %q", first, second)
	}
	r.Release(id)
	close(commands)
}

func TestFreezeBeforeProxyBind(t *testing.T) {
	t.Parallel()
	r := NewRegistry()
	id, err := r.Admit("alice", "myapp", "g1")
	if err != nil {
		t.Fatal(err)
	}
	if count, err := r.Freeze(context.Background(), "alice", "myapp", "g1"); err != nil || count != 1 {
		t.Fatalf("freeze count=%d err=%v", count, err)
	}
	if frozen := r.BindMigration(id, make(chan MigrationCommand)); !frozen {
		t.Fatal("late-bound proxy did not inherit freeze")
	}
	r.Release(id)
}

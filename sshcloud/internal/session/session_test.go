package session

import (
	"errors"
	"testing"
)

func TestAdmitRejectsSecond(t *testing.T) {
	t.Parallel()
	r := NewRegistry()
	id, err := r.Admit("alice", "fortune")
	if err != nil {
		t.Fatal(err)
	}
	_, err = r.Admit("alice", "fortune")
	var busy ErrBusy
	if !errors.As(err, &busy) {
		t.Fatalf("got %v, want ErrBusy", err)
	}
	if !r.Active("alice", "fortune") {
		t.Fatal("expected active")
	}

	// Different app OK.
	if _, err := r.Admit("alice", "myapp"); err != nil {
		t.Fatal(err)
	}
	// Different user OK.
	if _, err := r.Admit("bob", "fortune"); err != nil {
		t.Fatal(err)
	}

	r.Release(id)
	if r.Active("alice", "fortune") {
		t.Fatal("expected released")
	}
	if _, err := r.Admit("alice", "fortune"); err != nil {
		t.Fatal(err)
	}
}

func TestReleaseUnknownID(t *testing.T) {
	t.Parallel()
	r := NewRegistry()
	r.Release("nope") // must not panic
}

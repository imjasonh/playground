package honk

import (
	"testing"
	"time"
)

func TestNotifyReachesEverySubscriber(t *testing.T) {
	ctx := t.Context()
	ext, err := Extension(ctx, "", t.TempDir())
	if err != nil {
		t.Fatal(err)
	}
	h, err := Open(ctx, t.TempDir()+"/honker.db", ext)
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { h.Close() })

	a, unsubA := h.Subscribe()
	defer unsubA()
	b, unsubB := h.Subscribe()
	defer unsubB()

	if err := h.NotifyClick(1); err != nil {
		t.Fatal(err)
	}
	if err := h.NotifyClick(2); err != nil {
		t.Fatal(err)
	}
	for _, ch := range []<-chan Click{a, b} {
		first := recvClick(t, ch)
		second := recvClick(t, ch)
		if first.Count != 1 || second.Count != 2 {
			t.Fatalf("counts = %d, %d; ids %d, %d", first.Count, second.Count, first.ID, second.ID)
		}
		if second.ID <= first.ID {
			t.Fatalf("notification ids went backwards: %d then %d", first.ID, second.ID)
		}
	}
}

func recvClick(t *testing.T, ch <-chan Click) Click {
	t.Helper()
	select {
	case c, ok := <-ch:
		if !ok {
			t.Fatal("subscription closed")
		}
		return c
	case <-time.After(5 * time.Second):
		t.Fatal("timed out waiting for a notification")
	}
	return Click{}
}

package fanout

import (
	"testing"
	"time"
)

func TestNotifyReachesEverySubscriber(t *testing.T) {
	h := New()
	t.Cleanup(h.Close)

	a, unsubA := h.Subscribe()
	defer unsubA()
	b, unsubB := h.Subscribe()
	defer unsubB()

	h.NotifyClick(1)
	h.NotifyClick(2)
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

func TestUnsubscribeStopsDelivery(t *testing.T) {
	h := New()
	t.Cleanup(h.Close)

	ch, unsub := h.Subscribe()
	unsub()
	if _, ok := <-ch; ok {
		t.Fatal("channel should be closed after unsubscribe")
	}
	// A notification after unsubscribe must not panic or block.
	h.NotifyClick(1)
}

func TestCloseClosesEverySubscription(t *testing.T) {
	h := New()
	ch, unsub := h.Subscribe()
	defer unsub()

	h.Close()
	select {
	case _, ok := <-ch:
		if ok {
			t.Fatal("channel should be closed")
		}
	case <-time.After(time.Second):
		t.Fatal("channel never closed")
	}

	// A subscription after Close returns an already-closed channel.
	ch2, unsub2 := h.Subscribe()
	defer unsub2()
	if _, ok := <-ch2; ok {
		t.Fatal("subscribe after close should return a closed channel")
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

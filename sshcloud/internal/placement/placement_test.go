package placement

import (
	"context"
	"testing"
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

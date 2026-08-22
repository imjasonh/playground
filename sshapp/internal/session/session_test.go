package session_test

import (
	"context"
	"errors"
	"testing"

	"github.com/imjasonh/playground/sshapp/internal/session"
)

func TestMemoryStoreRoundTrip(t *testing.T) {
	t.Parallel()
	store := session.NewMemoryStore()
	ctx := context.Background()

	if err := store.Put(ctx, "sess-1", []byte("blob")); err != nil {
		t.Fatal(err)
	}
	got, err := store.Get(ctx, "sess-1")
	if err != nil || string(got) != "blob" {
		t.Fatalf("Get = %q, %v", got, err)
	}
	_, err = store.Get(ctx, "missing")
	if !errors.Is(err, session.ErrNotFound) {
		t.Fatalf("missing err = %v, want ErrNotFound", err)
	}
}

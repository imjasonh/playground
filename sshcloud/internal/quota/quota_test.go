package quota

import (
	"context"
	"errors"
	"sync"
	"testing"
	"time"
)

func TestMemoryRollingWindowAndIdempotency(t *testing.T) {
	t.Parallel()
	store := NewMemory()
	ctx := context.Background()
	now := time.Unix(100, 0)
	limit := Limit{Max: 2, Window: time.Minute}
	for _, id := range []string{"a", "b"} {
		if err := store.Take(ctx, Request{Kind: "deploy", Subject: "alice", EventID: id, At: now, Limit: limit}); err != nil {
			t.Fatal(err)
		}
	}
	if err := store.Take(ctx, Request{Kind: "deploy", Subject: "alice", EventID: "a", At: now, Limit: limit}); err != nil {
		t.Fatalf("idempotent event: %v", err)
	}
	err := store.Take(ctx, Request{Kind: "deploy", Subject: "alice", EventID: "c", At: now.Add(time.Minute - time.Nanosecond), Limit: limit})
	var exceeded ErrExceeded
	if !errors.As(err, &exceeded) {
		t.Fatalf("error %v, want ErrExceeded", err)
	}
	if err := store.Take(ctx, Request{Kind: "deploy", Subject: "alice", EventID: "c", At: now.Add(time.Minute), Limit: limit}); err != nil {
		t.Fatalf("exact boundary: %v", err)
	}
}

func TestMemoryConcurrentEventChargedOnce(t *testing.T) {
	t.Parallel()
	store := NewMemory()
	req := Request{
		Kind: "wake", Subject: "alice", EventID: "same", At: time.Now(),
		Limit: Limit{Max: 1, Window: time.Hour},
	}
	var wg sync.WaitGroup
	errs := make(chan error, 20)
	for range 20 {
		wg.Add(1)
		go func() {
			defer wg.Done()
			errs <- store.Take(context.Background(), req)
		}()
	}
	wg.Wait()
	close(errs)
	for err := range errs {
		if err != nil {
			t.Fatal(err)
		}
	}
}

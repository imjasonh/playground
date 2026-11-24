package a

import (
	"context"
	"time"
)

func f(ctx context.Context, ch chan int, done chan struct{}) error {
	// Good: select outside loop
	select {
	case <-time.After(time.Second):
	case <-ch:
	}

	// Bad: 2-case select (other case with body, time.After second) — auto-fixed
	for i := 0; i < 10; i++ {
		select { // want "time.After in a for-select loop will leak memory"
		case <-ctx.Done():
			return ctx.Err()
		case <-time.After(time.Second):
		}
	}

	// Bad: 2-case select (time.After first, empty other case) — auto-fixed
	for i := 0; i < 10; i++ {
		select { // want "time.After in a for-select loop will leak memory"
		case <-time.After(time.Second):
		case <-ch:
		}
	}

	// Bad: 3-case select — diagnose-only
	for i := 0; i < 10; i++ {
		select {
		case <-ctx.Done():
			return ctx.Err()
		case <-done:
		case <-time.After(time.Second): // want "time.After in a for-select loop will leak memory"
		}
	}
	return nil
}

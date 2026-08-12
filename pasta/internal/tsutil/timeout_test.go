package tsutil

import (
	"context"
	"errors"
	"sync/atomic"
	"testing"
	"time"

	"github.com/imjasonh/pasta/internal/tswasm"
)

func TestParseWithOptions_Timeout(t *testing.T) {
	// A tiny timeout against a non-trivial file should surface
	// ErrParseTimeout (or succeed extremely quickly on a tiny stub —
	// pad the source so pure-Go parsing has work to do).
	src := []byte("package p\n\n")
	for i := 0; i < 2000; i++ {
		src = append(src, []byte("func F"+itoa(i)+"() { var x int; _ = x }\n")...)
	}
	_, _, err := ParseWithOptions(context.Background(), &tswasm.Language{Grammar: "go"}, src, "big.go", ParseOptions{
		Timeout: time.Microsecond, // clamps to 1µs
	})
	if err == nil {
		t.Skip("parse finished within 1µs; machine too fast to assert timeout")
	}
	if !errors.Is(err, ErrParseTimeout) {
		t.Fatalf("err = %v, want ErrParseTimeout", err)
	}
}

func TestParseWithOptions_CancelRace(t *testing.T) {
	src := []byte("package p\n\n")
	for i := 0; i < 4000; i++ {
		src = append(src, []byte("func F"+itoa(i)+"() { var x int; _ = x }\n")...)
	}

	// Cancel almost immediately so AfterFunc races with the parser's
	// atomic loads of the cancellation flag. Under -race this used to
	// fail with a data race on a plain store.
	ctx, cancel := context.WithCancel(context.Background())
	var started atomic.Bool
	go func() {
		for !started.Load() {
			time.Sleep(time.Microsecond)
		}
		cancel()
	}()
	started.Store(true)
	_, _, err := ParseWithOptions(ctx, &tswasm.Language{Grammar: "go"}, src, "big.go", ParseOptions{
		Timeout: 2 * time.Second,
	})
	if err == nil {
		// Cancellation can lose the race to a finished parse on a
		// very fast machine; that's fine — the point is -race clean.
		return
	}
	if !errors.Is(err, context.Canceled) && !errors.Is(err, ErrParseTimeout) {
		t.Fatalf("err = %v, want canceled or timeout", err)
	}
}

func itoa(n int) string {
	if n == 0 {
		return "0"
	}
	var b [12]byte
	i := len(b)
	for n > 0 {
		i--
		b[i] = byte('0' + n%10)
		n /= 10
	}
	return string(b[i:])
}

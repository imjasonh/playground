package queue

import (
	"testing"
	"testing/synctest"
	"time"
)

func newQ(t *testing.T) *Queue[string] {
	t.Helper()
	q := New[string](Options{Jitter: -1})
	t.Cleanup(q.ShutDown)
	return q
}

// tryGet returns the next ready key without blocking the test forever.
func tryGet(t *testing.T, q *Queue[string]) (string, bool) {
	t.Helper()
	got := make(chan string, 1)
	go func() {
		if k, ok := q.Get(); ok {
			got <- k
		}
	}()
	synctest.Wait()
	select {
	case k := <-got:
		return k, true
	default:
		// Unblock the goroutine so the bubble can exit.
		q.Add("\x00unblock", Low)
		synctest.Wait()
		if k := <-got; k != "\x00unblock" {
			return k, true
		}
		q.Done("\x00unblock")
		return "", false
	}
}

func TestDeduplicates(t *testing.T) {
	synctest.Test(t, func(t *testing.T) {
		q := newQ(t)
		for range 3 {
			q.Add("a", Low)
		}
		q.Add("b", Low)
		if h, l := q.Len(); h != 0 || l != 2 {
			t.Fatalf("Len = %d, %d; want 0, 2", h, l)
		}
		if k, _ := q.Get(); k != "a" {
			t.Fatalf("Get = %q", k)
		}
		if k, _ := q.Get(); k != "b" {
			t.Fatalf("Get = %q", k)
		}
	})
}

func TestOneWorkerPerKey(t *testing.T) {
	synctest.Test(t, func(t *testing.T) {
		q := newQ(t)
		q.Add("a", High)
		k, _ := q.Get()
		q.Add("a", High) // Arrives while "a" is processing.
		if k, ok := tryGet(t, q); ok {
			t.Fatalf("Get returned %q while a was processing", k)
		}
		q.Done(k)
		if k, ok := tryGet(t, q); !ok || k != "a" {
			t.Fatalf("after Done, Get = %q, %v; want a", k, ok)
		}
	})
}

func TestPriority(t *testing.T) {
	synctest.Test(t, func(t *testing.T) {
		q := newQ(t)
		q.Add("low-1", Low)
		q.Add("low-2", Low)
		q.Add("high-1", High)
		q.Add("low-2", High) // Upgrades an already queued key.
		var got []string
		for range 3 {
			k, _ := q.Get()
			got = append(got, k)
		}
		if want := []string{"high-1", "low-2", "low-1"}; !equal(got, want) {
			t.Errorf("order = %v, want %v", got, want)
		}
	})
}

func TestDirtyKeepsHighestPriority(t *testing.T) {
	synctest.Test(t, func(t *testing.T) {
		q := newQ(t)
		q.Add("a", Low)
		k, _ := q.Get()
		q.Add("a", Low)
		q.Add("a", High)
		q.Add("a", Low)
		q.Add("b", Low)
		q.Done(k)
		if k, _ := q.Get(); k != "a" {
			t.Errorf("Get = %q, want a re-queued at high priority", k)
		}
	})
}

func TestAddAfter(t *testing.T) {
	synctest.Test(t, func(t *testing.T) {
		q := newQ(t)
		start := time.Now()
		q.AddAfter("a", High, 10*time.Second)
		q.AddAfter("a", High, time.Second) // The earlier time wins.
		q.AddAfter("a", High, time.Minute)
		if q.Waiting() != 1 {
			t.Fatalf("Waiting = %d", q.Waiting())
		}
		k, _ := q.Get()
		if k != "a" || time.Since(start) != time.Second {
			t.Errorf("got %q after %v, want a after 1s", k, time.Since(start))
		}
	})
}

func TestRetryBacksOff(t *testing.T) {
	synctest.Test(t, func(t *testing.T) {
		q := newQ(t)
		var delays []time.Duration
		for range 4 {
			delays = append(delays, q.Retry("a", High))
			start := time.Now()
			k, _ := q.Get()
			if waited := time.Since(start); waited != delays[len(delays)-1] {
				t.Errorf("waited %v, want %v", waited, delays[len(delays)-1])
			}
			q.Done(k)
		}
		want := []time.Duration{50 * time.Millisecond, 100 * time.Millisecond, 200 * time.Millisecond, 400 * time.Millisecond}
		if !equal(delays, want) {
			t.Errorf("delays = %v, want %v", delays, want)
		}
		if q.Failures("a") != 4 {
			t.Errorf("Failures = %d", q.Failures("a"))
		}
		q.Forget("a")
		if d := q.Retry("a", High); d != 50*time.Millisecond {
			t.Errorf("after Forget, delay = %v", d)
		}
	})
}

func TestRetryCapsDelay(t *testing.T) {
	synctest.Test(t, func(t *testing.T) {
		q := New[string](Options{BaseDelay: time.Second, MaxDelay: 5 * time.Second, Jitter: -1})
		defer q.ShutDown()
		var last time.Duration
		for range 10 {
			last = q.Retry("a", Low)
		}
		if last != 5*time.Second {
			t.Errorf("delay = %v, want the 5s cap", last)
		}
	})
}

func TestShutDownUnblocksGet(t *testing.T) {
	synctest.Test(t, func(t *testing.T) {
		q := New[string](Options{})
		done := make(chan bool)
		go func() {
			_, ok := q.Get()
			done <- ok
		}()
		synctest.Wait()
		q.ShutDown()
		if <-done {
			t.Error("Get returned ok after ShutDown")
		}
		q.Add("a", High)
		q.AddAfter("a", High, time.Second)
		if _, ok := q.Get(); ok {
			t.Error("Get after ShutDown returned ok")
		}
	})
}

func equal[T comparable](a, b []T) bool {
	if len(a) != len(b) {
		return false
	}
	for i := range a {
		if a[i] != b[i] {
			return false
		}
	}
	return true
}

package caller

import (
	"context"
	"errors"
	"maps"
	"sync"
	"testing"
	"testing/synctest"
	"time"

	"github.com/imjasonh/playground/kube"
	"github.com/imjasonh/playground/kube/k8s"
)

func checksConfigMap(data map[string]string) *k8s.ConfigMap {
	cm := &k8s.ConfigMap{Object: kube.Meta(ChecksConfigMap, nil), Data: data}
	cm.Namespace = ChecksNamespace
	return cm
}

func TestChecksEntries(t *testing.T) {
	cm := checksConfigMap(map[string]string{"checks.bot": "bot"})
	for _, tc := range []struct {
		name  string
		world []any
		want  map[string]string
	}{
		{name: "without the ConfigMap"},
		{name: "with the ConfigMap", world: []any{cm}, want: cm.Data},
	} {
		t.Run(tc.name, func(t *testing.T) {
			ctx, _ := kube.FakeRequest(t.Context(), tc.world...)
			var c *Checks
			if got, err := c.Entries(ctx); err != nil || !maps.Equal(got, tc.want) {
				t.Errorf("(*Checks)(nil).Entries = %v, %v; want %v", got, err, tc.want)
			}
			if got, err := new(Checks).Entries(ctx); err != nil || !maps.Equal(got, tc.want) {
				t.Errorf("new(Checks).Entries = %v, %v; want %v", got, err, tc.want)
			}
		})
	}
}

// fakeConfigMap stands in for the API server in tests of Checks. Each read
// takes delay, and returns the entries and the error that the fake had when
// the read started.
type fakeConfigMap struct {
	delay time.Duration
	start time.Time

	mu      sync.Mutex
	entries map[string]string
	err     error
	reads   int
}

func newFakeConfigMap(delay time.Duration, entries map[string]string, err error) *fakeConfigMap {
	return &fakeConfigMap{delay: delay, start: time.Now(), entries: entries, err: err}
}

func (f *fakeConfigMap) set(entries map[string]string, err error) {
	f.mu.Lock()
	defer f.mu.Unlock()
	f.entries, f.err = entries, err
}

func (f *fakeConfigMap) fetch(ctx context.Context) (map[string]string, error) {
	f.mu.Lock()
	f.reads++
	entries, err := f.entries, f.err
	f.mu.Unlock()
	if f.delay == 0 {
		return entries, err
	}
	select {
	case <-time.After(f.delay):
		return entries, err
	case <-ctx.Done():
		return nil, ctx.Err()
	}
}

func (f *fakeConfigMap) readCount() int {
	f.mu.Lock()
	defer f.mu.Unlock()
	return f.reads
}

func (f *fakeConfigMap) since() time.Duration { return time.Since(f.start) }

// want calls c.Entries and checks that it returns want, and that the fake
// has had reads reads by the time it returns.
func (f *fakeConfigMap) want(t *testing.T, c *Checks, want map[string]string, reads int) {
	t.Helper()
	if got, err := c.Entries(t.Context()); err != nil || !maps.Equal(got, want) {
		t.Errorf("after %v, Entries = %v, %v; want %v", f.since(), got, err, want)
	}
	if n := f.readCount(); n != reads {
		t.Errorf("after %v, the ConfigMap had %d reads; want %d", f.since(), n, reads)
	}
}

// TestChecksTTL checks that Checks reads the ConfigMap again for a call that
// comes checksTTL after the last read started, and not for one before.
func TestChecksTTL(t *testing.T) {
	synctest.Test(t, func(t *testing.T) {
		old, changed := map[string]string{"checks.bot": "bot"}, map[string]string{"checks.bot": "other"}
		f := newFakeConfigMap(time.Second, old, nil)
		c := &Checks{fetch: f.fetch}
		f.want(t, c, old, 1)
		f.set(changed, nil)
		time.Sleep(checksTTL - f.since() - time.Nanosecond)
		f.want(t, c, old, 1)
		time.Sleep(time.Nanosecond)
		f.want(t, c, changed, 2)
	})
}

// TestChecksSharedRead checks that calls during a read wait for it, and that
// a call that comes checksTTL after a slow read started waits for the next
// read instead.
func TestChecksSharedRead(t *testing.T) {
	synctest.Test(t, func(t *testing.T) {
		old, changed := map[string]string{"checks.bot": "bot"}, map[string]string{"checks.bot": "other"}
		f := newFakeConfigMap(2*checksTTL, old, nil)
		c := &Checks{fetch: f.fetch}
		get := func(want map[string]string) {
			if got, err := c.Entries(t.Context()); err != nil || !maps.Equal(got, want) {
				t.Errorf("after %v, Entries = %v, %v; want %v", f.since(), got, err, want)
			}
		}
		var wg sync.WaitGroup
		for range 10 {
			wg.Go(func() { get(old) })
		}
		synctest.Wait()
		if n := f.readCount(); n != 1 {
			t.Errorf("10 calls at once read the ConfigMap %d times; want 1", n)
		}
		f.set(changed, nil)
		time.Sleep(checksTTL)
		wg.Go(func() { get(changed) })
		wg.Wait()
		if n := f.readCount(); n != 2 {
			t.Errorf("the ConfigMap had %d reads; want 2", n)
		}
	})
}

// TestChecksStaleOnError checks that after a read fails, Checks returns the
// entries that it read last until checksMaxAge after that read started, and
// reads again only checksRetry after a read fails.
func TestChecksStaleOnError(t *testing.T) {
	synctest.Test(t, func(t *testing.T) {
		old := map[string]string{"checks.bot": "bot"}
		f := newFakeConfigMap(0, old, nil)
		c := &Checks{fetch: f.fetch}
		f.want(t, c, old, 1)
		down := errors.New("the API server is down")
		f.set(nil, down)
		time.Sleep(checksTTL)
		f.want(t, c, old, 2)
		time.Sleep(checksRetry - time.Nanosecond)
		f.want(t, c, old, 2)
		time.Sleep(time.Nanosecond)
		f.want(t, c, old, 3)
		time.Sleep(checksMaxAge - f.since() - time.Nanosecond)
		f.want(t, c, old, 4)
		time.Sleep(time.Nanosecond)
		if got, err := c.Entries(t.Context()); !errors.Is(err, down) || got != nil {
			t.Errorf("checksMaxAge after the last read that succeeded, Entries = %v, %v; want the read's error", got, err)
		}
		if n := f.readCount(); n != 4 {
			t.Errorf("the ConfigMap had %d reads; want 4", n)
		}
		recovered := map[string]string{"checks.bot": "other"}
		f.set(recovered, nil)
		time.Sleep(checksRetry)
		f.want(t, c, recovered, 5)
	})
}

// TestChecksFirstReadFails checks that Checks returns the error of a read
// that fails when it has no entries, and reads again only checksRetry later.
func TestChecksFirstReadFails(t *testing.T) {
	synctest.Test(t, func(t *testing.T) {
		down := errors.New("the API server is down")
		f := newFakeConfigMap(0, nil, down)
		c := &Checks{fetch: f.fetch}
		for range 2 {
			if got, err := c.Entries(t.Context()); !errors.Is(err, down) || got != nil {
				t.Errorf("Entries = %v, %v; want the read's error", got, err)
			}
		}
		if n := f.readCount(); n != 1 {
			t.Errorf("the ConfigMap had %d reads; want 1", n)
		}
		entries := map[string]string{"checks.bot": "bot"}
		f.set(entries, nil)
		time.Sleep(checksRetry)
		f.want(t, c, entries, 2)
	})
}

// TestChecksEmptiedEntry checks that a service account whose entry is
// emptied stops being a check checksTTL after the read that saw its entry.
func TestChecksEmptiedEntry(t *testing.T) {
	synctest.Test(t, func(t *testing.T) {
		bot := Caller{Namespace: "checks", Name: "bot"}
		before, _ := kube.FakeRequest(t.Context(), checksConfigMap(map[string]string{"checks.bot": "bot"}))
		emptied, _ := kube.FakeRequest(t.Context(), checksConfigMap(map[string]string{"checks.bot": ""}))
		c := &Checks{}
		start := time.Now()
		isCheck := func(ctx context.Context, want bool) {
			t.Helper()
			entries, err := c.Entries(ctx)
			if err != nil {
				t.Fatalf("Entries: %v", err)
			}
			if check, ok := bot.Check(entries); ok != want {
				t.Errorf("after %v, %v.Check(%v) = %q, %v; want %v", time.Since(start), bot, entries, check, ok, want)
			}
		}
		isCheck(before, true)
		time.Sleep(checksTTL - time.Nanosecond)
		isCheck(emptied, true)
		time.Sleep(time.Nanosecond)
		isCheck(emptied, false)
	})
}

// TestChecksCanceled checks that a call stops waiting for a read when its
// context is done, and that a read whose caller gives up isn't a failure
// that keeps the next call from reading.
func TestChecksCanceled(t *testing.T) {
	synctest.Test(t, func(t *testing.T) {
		entries := map[string]string{"checks.bot": "bot"}
		f := newFakeConfigMap(time.Minute, entries, nil)
		c := &Checks{fetch: f.fetch}
		readCtx, cancelRead := context.WithCancel(t.Context())
		read := make(chan error)
		go func() {
			_, err := c.Entries(readCtx)
			read <- err
		}()
		synctest.Wait()
		waitCtx, cancel := context.WithTimeout(t.Context(), time.Second)
		defer cancel()
		if _, err := c.Entries(waitCtx); !errors.Is(err, context.DeadlineExceeded) || f.since() != time.Second {
			t.Errorf("after %v, Entries = %v; want %v after 1s", f.since(), err, context.DeadlineExceeded)
		}
		cancelRead()
		if err := <-read; !errors.Is(err, context.Canceled) {
			t.Errorf("Entries = %v; want %v", err, context.Canceled)
		}
		f.want(t, c, entries, 2)
	})
}

// TestChecksReadPanics checks that a read that panics doesn't keep later
// calls from reading.
func TestChecksReadPanics(t *testing.T) {
	entries := map[string]string{"checks.bot": "bot"}
	panics := true
	c := &Checks{fetch: func(context.Context) (map[string]string, error) {
		if panics {
			panic("the read failed")
		}
		return entries, nil
	}}
	func() {
		defer func() {
			if recover() == nil {
				t.Error("Entries didn't panic")
			}
		}()
		_, _ = c.Entries(t.Context())
	}()
	panics = false
	if got, err := c.Entries(t.Context()); err != nil || !maps.Equal(got, entries) {
		t.Errorf("after a read panicked, Entries = %v, %v; want %v", got, err, entries)
	}
}

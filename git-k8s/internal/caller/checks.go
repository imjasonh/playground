package caller

import (
	"context"
	"log/slog"
	"sync"
	"time"

	"github.com/imjasonh/playground/kube"
	"github.com/imjasonh/playground/kube/k8s"
)

// A Checks reads the ConfigMap again for a call that comes checksTTL or more
// after the last read that succeeded started, so a change to an entry takes
// effect within checksTTL. After a read fails, it returns the entries that it
// read last until checksMaxAge after that read started, and doesn't read
// again for checksRetry. The README states these durations.
const (
	checksTTL    = 5 * time.Second
	checksMaxAge = 30 * time.Second
	checksRetry  = time.Second
)

// Checks holds the entries of the git-k8s-checks ConfigMap for callers that
// need them for every request, such as the mirror and the results endpoint,
// so that a burst of requests reads the ConfigMap once. Its methods are safe
// for concurrent use, and calls that come during a read wait for it. A nil
// *Checks reads the ConfigMap on every call.
type Checks struct {
	// fetch reads the entries in tests. Nil means fetchChecks.
	fetch func(context.Context) (map[string]string, error)

	mu sync.Mutex
	// entries are from the last read that succeeded, which started at
	// readAt. readAt is zero until a read succeeds.
	entries map[string]string
	readAt  time.Time
	// err is the error of the last read, which ended at failedAt, or nil if
	// the last read succeeded.
	err      error
	failedAt time.Time
	// reading is closed when the read in progress ends, and is nil while no
	// read is in progress.
	reading chan struct{}
}

// Entries returns the entries of the git-k8s-checks ConfigMap, which
// Caller.Check takes, or no entries if the ConfigMap doesn't exist. Callers
// share the map, so they must not change it.
func (c *Checks) Entries(ctx context.Context) (map[string]string, error) {
	if c == nil {
		return fetchChecks(ctx)
	}
	c.mu.Lock()
	defer c.mu.Unlock()
	called := time.Now()
	for {
		if !c.readAt.IsZero() && called.Sub(c.readAt) < checksTTL {
			return c.entries, nil
		}
		if c.reading == nil {
			break
		}
		if err := c.wait(ctx); err != nil {
			return nil, err
		}
	}
	if c.err == nil || time.Since(c.failedAt) >= checksRetry {
		start := time.Now()
		entries, err := c.read(ctx)
		switch {
		case err == nil:
			c.entries, c.readAt, c.err = entries, start, nil
			return entries, nil
		case ctx.Err() != nil:
			// The caller gave up, which says nothing about the API server.
			return nil, err
		}
		c.err, c.failedAt = err, time.Now()
		if c.usable() {
			slog.Warn("reading the git-k8s-checks ConfigMap failed, so the entries read earlier stay in use", "err", err, "age", time.Since(c.readAt))
		}
	}
	if c.usable() {
		return c.entries, nil
	}
	return nil, c.err
}

// usable reports whether the entries may stand in for a read that failed.
func (c *Checks) usable() bool {
	return !c.readAt.IsZero() && time.Since(c.readAt) < checksMaxAge
}

// read reads the entries with c.mu unlocked, while other calls wait for it.
func (c *Checks) read(ctx context.Context) (map[string]string, error) {
	reading := make(chan struct{})
	c.reading = reading
	c.mu.Unlock()
	defer func() {
		c.mu.Lock()
		c.reading = nil
		close(reading)
	}()
	if c.fetch != nil {
		return c.fetch(ctx)
	}
	return fetchChecks(ctx)
}

// wait waits, with c.mu unlocked, until the read in progress ends or ctx is
// done.
func (c *Checks) wait(ctx context.Context) error {
	reading := c.reading
	c.mu.Unlock()
	defer c.mu.Lock()
	select {
	case <-reading:
		return nil
	case <-ctx.Done():
		return ctx.Err()
	}
}

// fetchChecks reads the git-k8s-checks ConfigMap. generate grants get on
// that ConfigMap alone because the call passes constants as its namespace
// and name.
func fetchChecks(ctx context.Context) (map[string]string, error) {
	cm, err := kube.Fetch[k8s.ConfigMap](ctx, ChecksNamespace, ChecksConfigMap)
	if err != nil || cm == nil {
		return nil, err
	}
	return cm.Data, nil
}

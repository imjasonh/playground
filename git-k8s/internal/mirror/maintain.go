package mirror

import (
	"cmp"
	"context"
	"log/slog"
	"slices"
	"time"

	"github.com/imjasonh/playground/git-k8s/internal/git"
)

// Maintain runs git's maintenance on the copies that syncs queue, one copy
// at a time, until ctx ends, and returns once the maintenance that it was
// running has stopped. Maintenance packs a copy's objects when the copy
// needs that. It runs beside the copy's syncs, fetches, and pushes, which
// don't wait for it, and stops when the copy is deleted, replaced, or
// switched to a new URL. Each run takes at most MaintenanceTimeout. After a
// run fails or times out, Maintain skips the copy for 6 hours, because the
// next run would most likely fail the same way.
//
// Maintain reads the Mirror's exported fields only after a sync queues a
// copy, so it can start before they're set.
func (m *Mirror) Maintain(ctx context.Context) {
	for m.maintainNext(ctx) {
	}
}

// maintainNext waits for a queued copy and maintains it. It reports false
// once ctx ends.
func (m *Mirror) maintainNext(ctx context.Context) bool {
	m.mu.Lock()
	for len(m.queue) == 0 {
		wake := m.wakeChan()
		m.mu.Unlock()
		select {
		case <-ctx.Done():
			return false
		case <-wake:
		}
		m.mu.Lock()
	}
	e := m.queue[0]
	m.queue = m.queue[1:]
	e.queued = false
	mctx, stop := context.WithCancel(ctx)
	defer stop()
	m.maintaining, m.stopMaintaining = e, stop
	g := m.maintenanceGit()
	retry := cmp.Or(m.maintenanceRetry, 6*time.Hour)
	m.mu.Unlock()

	err := maintain(mctx, g, e)

	m.mu.Lock()
	m.maintaining, m.stopMaintaining = nil, nil
	// Maintenance that was stopped didn't fail.
	failed := err != nil && mctx.Err() == nil
	if failed {
		e.maintainAfter = time.Now().Add(retry)
	}
	m.mu.Unlock()
	if failed {
		slog.Warn("maintaining a copy failed", "path", e.dir, "retry", retry, "err", err)
	}
	return ctx.Err() == nil
}

// maintain runs git's maintenance on e's copy, if e holds one.
func maintain(ctx context.Context, g *git.Git, e *entry) error {
	e.mu.RLock()
	defer e.mu.RUnlock()
	if e.repo == nil {
		return nil
	}
	r, err := g.Open(ctx, e.dir)
	if err != nil {
		return err
	}
	return r.Maintain(ctx)
}

// queueMaintenance queues e's copy for Maintain, unless it's queued
// already, a change holds its maintenance, or its last maintenance failed
// less than maintenanceRetry ago.
func (m *Mirror) queueMaintenance(e *entry) {
	m.mu.Lock()
	defer m.mu.Unlock()
	if e.queued || e.held > 0 || time.Now().Before(e.maintainAfter) {
		return
	}
	e.queued = true
	m.queue = append(m.queue, e)
	select {
	case m.wakeChan() <- struct{}{}:
	default:
	}
}

// holdMaintenance stops the maintenance of e's copy if it's running, and
// keeps it from running until release is called, so that a change to the
// copy, which takes e.mu for writing, doesn't wait for it.
func (m *Mirror) holdMaintenance(e *entry) (release func()) {
	m.mu.Lock()
	defer m.mu.Unlock()
	e.held++
	if e.queued {
		m.queue = slices.DeleteFunc(m.queue, func(q *entry) bool { return q == e })
		e.queued = false
	}
	if m.maintaining == e {
		m.stopMaintaining()
	}
	return func() {
		m.mu.Lock()
		defer m.mu.Unlock()
		e.held--
	}
}

// wakeChan returns m.wake, making it first if needed. m.mu must be held.
func (m *Mirror) wakeChan() chan struct{} {
	if m.wake == nil {
		m.wake = make(chan struct{}, 1)
	}
	return m.wake
}

// maintenanceGit returns the Git that runs maintenance.
func (m *Mirror) maintenanceGit() *git.Git {
	return &git.Git{Bin: m.Git.Bin, Timeout: cmp.Or(m.MaintenanceTimeout, time.Hour)}
}

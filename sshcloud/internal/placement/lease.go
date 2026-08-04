package placement

import (
	"context"
	"fmt"
	"sync"
	"time"
)

const DefaultLeaseTTL = 30 * time.Second

// Guard keeps an exclusive placement lease alive for a control-plane operation.
type Guard struct {
	store Store
	lease Lease
	ttl   time.Duration

	ctx    context.Context
	cancel context.CancelFunc
	stop   chan struct{}
	done   chan struct{}
	once   sync.Once

	mu  sync.Mutex
	err error
}

// AcquireGuard acquires a lease and starts its renewal heartbeat.
func AcquireGuard(ctx context.Context, store Store, user, app, prefix string, ttl time.Duration) (*Guard, error) {
	if store == nil {
		return nil, fmt.Errorf("placement store required")
	}
	if ttl <= 0 {
		ttl = DefaultLeaseTTL
	}
	lease, err := store.Acquire(ctx, user, app, NewLeaseOwner(prefix), ttl, time.Now())
	if err != nil {
		return nil, err
	}
	guardCtx, cancel := context.WithCancel(ctx)
	g := &Guard{
		store: store, lease: lease, ttl: ttl, ctx: guardCtx, cancel: cancel,
		stop: make(chan struct{}), done: make(chan struct{}),
	}
	go g.heartbeat()
	return g, nil
}

func (g *Guard) heartbeat() {
	defer close(g.done)
	interval := g.ttl / 3
	if interval < time.Second {
		interval = time.Second
	}
	ticker := time.NewTicker(interval)
	defer ticker.Stop()
	expiry := time.NewTimer(time.Until(g.current().Until()))
	defer expiry.Stop()
	for {
		select {
		case <-g.ctx.Done():
			return
		case <-g.stop:
			return
		case <-expiry.C:
			g.mu.Lock()
			g.err = ErrLeaseLost{User: g.lease.User, App: g.lease.App}
			g.mu.Unlock()
			g.cancel()
			return
		case <-ticker.C:
			current := g.current()
			margin := g.ttl / 5
			if margin < 100*time.Millisecond {
				margin = 100 * time.Millisecond
			}
			renewDeadline := current.Until().Add(-margin)
			renewCtx, cancel := context.WithDeadline(g.ctx, renewDeadline)
			renewed, err := g.store.Renew(renewCtx, current, g.ttl, time.Now())
			cancel()
			if err != nil {
				g.mu.Lock()
				g.err = err
				g.mu.Unlock()
				g.cancel()
				return
			}
			g.mu.Lock()
			g.lease = renewed
			g.mu.Unlock()
			if !expiry.Stop() {
				select {
				case <-expiry.C:
				default:
				}
			}
			expiry.Reset(time.Until(renewed.Until()))
		}
	}
}

// Context is canceled when the caller cancels or lease renewal fails.
func (g *Guard) Context() context.Context { return g.ctx }

// HostID is the placement observed when the lease was acquired.
func (g *Guard) HostID() string { return g.current().HostID }

// Err reports a renewal failure, if any.
func (g *Guard) Err() error {
	g.mu.Lock()
	defer g.mu.Unlock()
	return g.err
}

// Mark persists recovery context under the current fencing lease.
func (g *Guard) Mark(ctx context.Context, operation Operation) error {
	if err := g.Err(); err != nil {
		return err
	}
	return g.store.Mark(ctx, g.current(), operation)
}

// Commit atomically updates placement and releases the lease.
func (g *Guard) Commit(ctx context.Context, hostID string) error {
	g.stopHeartbeat()
	if err := g.Err(); err != nil {
		return err
	}
	if err := g.store.Commit(ctx, g.current(), hostID, time.Now()); err != nil {
		return err
	}
	g.cancel()
	return nil
}

// Release gives up the lease without changing host ownership.
func (g *Guard) Release(ctx context.Context) error {
	g.stopHeartbeat()
	err := g.store.Release(ctx, g.current())
	g.cancel()
	return err
}

// Abandon leaves operation metadata and the expiring lease for reconciliation.
func (g *Guard) Abandon() {
	g.stopHeartbeat()
	g.cancel()
}

func (g *Guard) current() Lease {
	g.mu.Lock()
	defer g.mu.Unlock()
	return g.lease
}

func (g *Guard) stopHeartbeat() {
	g.once.Do(func() {
		close(g.stop)
		<-g.done
	})
}

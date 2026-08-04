// Package placement tracks which host agent owns each user/app instance.
package placement

import (
	"context"
	"crypto/rand"
	"encoding/hex"
	"fmt"
	"sync"
	"time"
)

// Store maps (user, app) → host ID.
type Store interface {
	Get(ctx context.Context, user, app string) (hostID string, ok bool, err error)
	Set(ctx context.Context, user, app, hostID string) error
	Delete(ctx context.Context, user, app string) error
	GetRecord(ctx context.Context, user, app string) (Record, bool, error)
	ListRecords(ctx context.Context) ([]Record, error)
	Acquire(ctx context.Context, user, app, owner string, ttl time.Duration, now time.Time) (Lease, error)
	Renew(ctx context.Context, lease Lease, ttl time.Duration, now time.Time) (Lease, error)
	Commit(ctx context.Context, lease Lease, hostID string, now time.Time) error
	Release(ctx context.Context, lease Lease) error
}

// Record is the durable owner and operation fence for one app.
type Record struct {
	User           string
	App            string
	HostID         string
	Revision       int64
	LeaseOwner     string
	LeaseUntilUnix int64
}

// Lease is an exclusive, expiring mutation right for one placement record.
type Lease struct {
	User      string
	App       string
	HostID    string
	Owner     string
	Revision  int64
	UntilUnix int64
}

func (l Lease) Until() time.Time { return time.Unix(0, l.UntilUnix) }

// ErrLeaseHeld means another live operation owns the app placement.
type ErrLeaseHeld struct {
	User  string
	App   string
	Owner string
	Until time.Time
}

func (e ErrLeaseHeld) Error() string {
	return fmt.Sprintf("placement lease for %s/%s is held by %s until %s", e.User, e.App, e.Owner, e.Until.UTC().Format(time.RFC3339))
}

// ErrLeaseLost means an operation no longer owns the record it is mutating.
type ErrLeaseLost struct{ User, App string }

func (e ErrLeaseLost) Error() string {
	return fmt.Sprintf("placement lease for %s/%s was lost", e.User, e.App)
}

// NewLeaseOwner returns an opaque operation owner ID.
func NewLeaseOwner(prefix string) string {
	var b [12]byte
	if _, err := rand.Read(b[:]); err != nil {
		return fmt.Sprintf("%s-%d", prefix, time.Now().UnixNano())
	}
	return prefix + "-" + hex.EncodeToString(b[:])
}

// Memory is an in-memory placement store.
type Memory struct {
	mu      sync.Mutex
	records map[string]Record // "user/app" → record
}

// NewMemory returns an empty placement store.
func NewMemory() *Memory {
	return &Memory{records: make(map[string]Record)}
}

func key(user, app string) string { return user + "/" + app }

func (m *Memory) Get(_ context.Context, user, app string) (string, bool, error) {
	m.mu.Lock()
	defer m.mu.Unlock()
	r, ok := m.records[key(user, app)]
	return r.HostID, ok && r.HostID != "", nil
}

func (m *Memory) Set(_ context.Context, user, app, hostID string) error {
	if user == "" || app == "" || hostID == "" {
		return fmt.Errorf("user, app, and hostID required")
	}
	m.mu.Lock()
	defer m.mu.Unlock()
	k := key(user, app)
	r := m.records[k]
	if leaseActive(r, time.Now()) {
		return ErrLeaseHeld{User: user, App: app, Owner: r.LeaseOwner, Until: time.Unix(0, r.LeaseUntilUnix)}
	}
	r.User, r.App, r.HostID = user, app, hostID
	r.Revision++
	r.LeaseOwner, r.LeaseUntilUnix = "", 0
	m.records[k] = r
	return nil
}

func (m *Memory) Delete(_ context.Context, user, app string) error {
	m.mu.Lock()
	defer m.mu.Unlock()
	k := key(user, app)
	if r, ok := m.records[k]; ok && leaseActive(r, time.Now()) {
		return ErrLeaseHeld{User: user, App: app, Owner: r.LeaseOwner, Until: time.Unix(0, r.LeaseUntilUnix)}
	}
	delete(m.records, k)
	return nil
}

func (m *Memory) GetRecord(_ context.Context, user, app string) (Record, bool, error) {
	m.mu.Lock()
	defer m.mu.Unlock()
	r, ok := m.records[key(user, app)]
	return r, ok, nil
}

func (m *Memory) ListRecords(context.Context) ([]Record, error) {
	m.mu.Lock()
	defer m.mu.Unlock()
	out := make([]Record, 0, len(m.records))
	for _, r := range m.records {
		out = append(out, r)
	}
	return out, nil
}

func (m *Memory) Acquire(_ context.Context, user, app, owner string, ttl time.Duration, now time.Time) (Lease, error) {
	if user == "" || app == "" || owner == "" || ttl <= 0 {
		return Lease{}, fmt.Errorf("user, app, owner, and positive ttl required")
	}
	m.mu.Lock()
	defer m.mu.Unlock()
	k := key(user, app)
	r := m.records[k]
	if leaseActive(r, now) && r.LeaseOwner != owner {
		return Lease{}, ErrLeaseHeld{User: user, App: app, Owner: r.LeaseOwner, Until: time.Unix(0, r.LeaseUntilUnix)}
	}
	r.User, r.App = user, app
	r.Revision++
	r.LeaseOwner = owner
	r.LeaseUntilUnix = now.Add(ttl).UnixNano()
	m.records[k] = r
	return leaseFromRecord(r), nil
}

func (m *Memory) Renew(_ context.Context, lease Lease, ttl time.Duration, now time.Time) (Lease, error) {
	if ttl <= 0 {
		return Lease{}, fmt.Errorf("positive ttl required")
	}
	m.mu.Lock()
	defer m.mu.Unlock()
	k := key(lease.User, lease.App)
	r, ok := m.records[k]
	if !ok || !leaseMatches(r, lease) || !leaseActive(r, now) {
		return Lease{}, ErrLeaseLost{User: lease.User, App: lease.App}
	}
	r.LeaseUntilUnix = now.Add(ttl).UnixNano()
	m.records[k] = r
	return leaseFromRecord(r), nil
}

func (m *Memory) Commit(_ context.Context, lease Lease, hostID string, now time.Time) error {
	if hostID == "" {
		return fmt.Errorf("hostID required")
	}
	m.mu.Lock()
	defer m.mu.Unlock()
	k := key(lease.User, lease.App)
	r, ok := m.records[k]
	if !ok || !leaseMatches(r, lease) || !leaseActive(r, now) {
		return ErrLeaseLost{User: lease.User, App: lease.App}
	}
	r.HostID = hostID
	r.Revision++
	r.LeaseOwner, r.LeaseUntilUnix = "", 0
	m.records[k] = r
	return nil
}

func (m *Memory) Release(_ context.Context, lease Lease) error {
	m.mu.Lock()
	defer m.mu.Unlock()
	k := key(lease.User, lease.App)
	r, ok := m.records[k]
	if !ok {
		return nil
	}
	if !leaseMatches(r, lease) {
		return ErrLeaseLost{User: lease.User, App: lease.App}
	}
	r.Revision++
	r.LeaseOwner, r.LeaseUntilUnix = "", 0
	m.records[k] = r
	return nil
}

func leaseActive(r Record, now time.Time) bool {
	return r.LeaseOwner != "" && r.LeaseUntilUnix > now.UnixNano()
}

func leaseMatches(r Record, lease Lease) bool {
	return r.Revision == lease.Revision && r.LeaseOwner == lease.Owner
}

func leaseFromRecord(r Record) Lease {
	return Lease{
		User: r.User, App: r.App, HostID: r.HostID, Owner: r.LeaseOwner,
		Revision: r.Revision, UntilUnix: r.LeaseUntilUnix,
	}
}

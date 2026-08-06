// Package quota provides small, idempotent rolling-window admission counters.
package quota

import (
	"context"
	"crypto/rand"
	"encoding/hex"
	"fmt"
	"sort"
	"sync"
	"time"
)

type Limit struct {
	Max    int
	Window time.Duration
}

type Request struct {
	Kind, Subject, EventID string
	At                     time.Time
	Limit                  Limit
}

// NewEventID returns one opaque admission-operation ID. Callers create it once
// and reuse it across transport retries; separate user operations get distinct
// IDs even when their image/generation inputs are identical.
func NewEventID(prefix string) string {
	var value [12]byte
	if _, err := rand.Read(value[:]); err != nil {
		return fmt.Sprintf("%s-%d", prefix, time.Now().UnixNano())
	}
	return prefix + "-" + hex.EncodeToString(value[:])
}

type Store interface {
	Take(context.Context, Request) error
	Close() error
}

type ErrExceeded struct {
	Kind    string
	Limit   int
	RetryAt time.Time
}

func (e ErrExceeded) Error() string {
	if e.RetryAt.IsZero() {
		return fmt.Sprintf("%s quota exceeded (%d)", e.Kind, e.Limit)
	}
	return fmt.Sprintf("%s quota exceeded (%d); retry after %s", e.Kind, e.Limit, e.RetryAt.UTC().Format(time.RFC3339))
}

type event struct {
	ID string
	At time.Time
}

type Memory struct {
	mu      sync.Mutex
	windows map[string][]event
}

func NewMemory() *Memory { return &Memory{windows: make(map[string][]event)} }

func (m *Memory) Take(_ context.Context, req Request) error {
	if err := validate(req); err != nil {
		return err
	}
	m.mu.Lock()
	defer m.mu.Unlock()
	key := req.Kind + "\x00" + req.Subject
	events := compact(m.windows[key], req.At.Add(-req.Limit.Window))
	for _, existing := range events {
		if existing.ID == req.EventID {
			m.windows[key] = events
			return nil
		}
	}
	if len(events) >= req.Limit.Max {
		return ErrExceeded{
			Kind: req.Kind, Limit: req.Limit.Max,
			RetryAt: events[0].At.Add(req.Limit.Window),
		}
	}
	m.windows[key] = append(events, event{ID: req.EventID, At: req.At})
	return nil
}

func (*Memory) Close() error { return nil }

func validate(req Request) error {
	if req.Kind == "" || req.Subject == "" || req.EventID == "" {
		return fmt.Errorf("quota kind, subject, and event ID required")
	}
	if req.At.IsZero() || req.Limit.Max <= 0 || req.Limit.Window <= 0 {
		return fmt.Errorf("quota time and positive limit/window required")
	}
	return nil
}

func compact(events []event, cutoff time.Time) []event {
	out := make([]event, 0, len(events))
	for _, existing := range events {
		if existing.At.After(cutoff) {
			out = append(out, existing)
		}
	}
	sort.Slice(out, func(i, j int) bool { return out[i].At.Before(out[j].At) })
	return out
}

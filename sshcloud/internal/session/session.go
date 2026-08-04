// Package session tracks admitted SSH sessions and enforces concurrency.
package session

import (
	"context"
	"fmt"
	"sync"
	"time"
)

// ID uniquely identifies an admitted session.
type ID string

// Key is the admission key: user × app (generations share the key).
type Key struct {
	User string
	App  string
}

func (k Key) String() string { return k.User + "/" + k.App }

type slot struct {
	ID        ID
	Gen       string
	cancel    context.CancelFunc
	kicked    bool
	migration chan MigrationCommand
	frozen    bool
}

// MigrationCommand coordinates the outer SSH session while its VM moves.
type MigrationCommand struct {
	Kind string
	Ack  chan error
}

const (
	MigrationFreeze = "freeze"
	MigrationThaw   = "thaw"
)

// Registry is an in-memory session table for the gateway.
type Registry struct {
	mu      sync.Mutex
	slots   map[Key][]slot
	byID    map[ID]Key
	nextSeq uint64
}

// NewRegistry returns an empty session registry.
func NewRegistry() *Registry {
	return &Registry{
		slots: make(map[Key][]slot),
		byID:  make(map[ID]Key),
	}
}

// ErrBusy is returned when the user already has a session on that generation
// (or two generations are already occupied during drain).
type ErrBusy struct {
	Key Key
}

func (e ErrBusy) Error() string {
	return fmt.Sprintf("session busy for %s: disconnect the other session first", e.Key)
}

// Admit tries to open a session pinned to gen (empty gen is the legacy singleton).
// During drain, one session per distinct gen is allowed (max two).
func (r *Registry) Admit(user, app, gen string) (ID, error) {
	if user == "" || app == "" {
		return "", fmt.Errorf("user and app are required")
	}
	k := Key{User: user, App: app}

	r.mu.Lock()
	defer r.mu.Unlock()
	cur := r.slots[k]
	for _, s := range cur {
		if s.Gen == gen {
			return "", ErrBusy{Key: k}
		}
	}
	if len(cur) >= 2 {
		return "", ErrBusy{Key: k}
	}
	r.nextSeq++
	id := ID(fmt.Sprintf("sess-%d", r.nextSeq))
	r.slots[k] = append(cur, slot{ID: id, Gen: gen})
	r.byID[id] = k
	return id, nil
}

// BindCancel registers a cancel func invoked by Kick (session proxy abort).
func (r *Registry) BindCancel(id ID, cancel context.CancelFunc) {
	if id == "" || cancel == nil {
		return
	}
	r.mu.Lock()
	k, ok := r.byID[id]
	if !ok {
		r.mu.Unlock()
		return
	}
	slots := r.slots[k]
	for i := range slots {
		if slots[i].ID == id {
			slots[i].cancel = cancel
			kicked := slots[i].kicked
			r.slots[k] = slots
			r.mu.Unlock()
			if kicked {
				cancel()
			}
			return
		}
	}
	r.mu.Unlock()
}

// BindMigration attaches the live proxy's migration command channel and
// reports whether a freeze arrived before the proxy bound.
func (r *Registry) BindMigration(id ID, commands chan MigrationCommand) (frozen bool) {
	if id == "" || commands == nil {
		return false
	}
	r.mu.Lock()
	defer r.mu.Unlock()
	k, ok := r.byID[id]
	if !ok {
		return false
	}
	slots := r.slots[k]
	for i := range slots {
		if slots[i].ID == id {
			slots[i].migration = commands
			frozen = slots[i].frozen
			r.slots[k] = slots
			return frozen
		}
	}
	return false
}

// Freeze asks matching proxies to disconnect from their backend while keeping
// the outer client SSH channel open. A not-yet-bound proxy remembers the state.
func (r *Registry) Freeze(ctx context.Context, user, app, gen string) (int, error) {
	ids := r.MatchingIDs(user, app, gen)
	if err := r.FreezeIDs(ctx, ids); err != nil {
		return len(ids), err
	}
	return len(ids), nil
}

// Thaw lets matching proxies reconnect to the newly placed backend.
func (r *Registry) Thaw(ctx context.Context, user, app, gen string) (int, error) {
	ids := r.MatchingIDs(user, app, gen)
	if err := r.ThawIDs(ctx, ids); err != nil {
		return len(ids), err
	}
	return len(ids), nil
}

// MatchingIDs snapshots exact sessions so migration tokens cannot affect a
// later reconnect that happens to share user/app/gen.
func (r *Registry) MatchingIDs(user, app, gen string) []ID {
	k := Key{User: user, App: app}
	r.mu.Lock()
	defer r.mu.Unlock()
	var ids []ID
	for _, slot := range r.slots[k] {
		if slot.Gen == gen {
			ids = append(ids, slot.ID)
		}
	}
	return ids
}

// FreezeIDs freezes exact sessions transactionally. Successfully frozen
// sessions are thawed if a later session fails.
func (r *Registry) FreezeIDs(ctx context.Context, ids []ID) error {
	var frozen []ID
	for _, id := range ids {
		if err := r.migrateSession(ctx, id, MigrationFreeze, true); err != nil {
			rollbackCtx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
			_ = r.ThawIDs(rollbackCtx, frozen)
			cancel()
			return err
		}
		frozen = append(frozen, id)
	}
	return nil
}

// ThawIDs thaws exact sessions; it is safe when a session has disconnected.
func (r *Registry) ThawIDs(ctx context.Context, ids []ID) error {
	for _, id := range ids {
		if err := r.migrateSession(ctx, id, MigrationThaw, false); err != nil {
			return err
		}
	}
	return nil
}

func (r *Registry) migrateSession(ctx context.Context, id ID, kind string, frozen bool) error {
	r.mu.Lock()
	k, ok := r.byID[id]
	if !ok {
		r.mu.Unlock()
		return nil
	}
	var commands chan MigrationCommand
	for _, slot := range r.slots[k] {
		if slot.ID == id {
			commands = slot.migration
			break
		}
	}
	r.mu.Unlock()

	if commands != nil {
		ack := make(chan error, 1)
		select {
		case commands <- MigrationCommand{Kind: kind, Ack: ack}:
		case <-ctx.Done():
			return ctx.Err()
		}
		select {
		case err := <-ack:
			if err != nil {
				return err
			}
		case <-ctx.Done():
			return ctx.Err()
		}
	}

	r.mu.Lock()
	defer r.mu.Unlock()
	k, ok = r.byID[id]
	if !ok {
		return nil
	}
	slots := r.slots[k]
	for i := range slots {
		if slots[i].ID == id {
			slots[i].frozen = frozen
			r.slots[k] = slots
			return nil
		}
	}
	return nil
}

// KickIDs cancels exact sessions and never a later reconnect.
func (r *Registry) KickIDs(ids []ID) int {
	r.mu.Lock()
	var cancels []context.CancelFunc
	n := 0
	for _, id := range ids {
		k, ok := r.byID[id]
		if !ok {
			continue
		}
		slots := r.slots[k]
		for i := range slots {
			if slots[i].ID == id {
				slots[i].kicked = true
				if slots[i].cancel != nil {
					cancels = append(cancels, slots[i].cancel)
				}
				n++
				break
			}
		}
		r.slots[k] = slots
	}
	r.mu.Unlock()
	for _, cancel := range cancels {
		cancel()
	}
	return n
}

// Kick cancels sessions for user/app/gen (empty gen matches only empty-gen slots).
// Sessions stay registered until Release; the proxy should exit and Release.
func (r *Registry) Kick(user, app, gen string) int {
	k := Key{User: user, App: app}
	r.mu.Lock()
	n := 0
	var cancels []context.CancelFunc
	slots := r.slots[k]
	for i := range slots {
		if slots[i].Gen == gen {
			slots[i].kicked = true
			if slots[i].cancel != nil {
				cancels = append(cancels, slots[i].cancel)
			}
			n++
		}
	}
	r.slots[k] = slots
	r.mu.Unlock()
	for _, cancel := range cancels {
		cancel()
	}
	return n
}

// GenOf returns the generation bound to a session id.
func (r *Registry) GenOf(id ID) (string, bool) {
	_, _, gen, ok := r.Info(id)
	return gen, ok
}

// Info returns user, app, and generation for an admitted session.
func (r *Registry) Info(id ID) (user, app, gen string, ok bool) {
	r.mu.Lock()
	defer r.mu.Unlock()
	k, ok := r.byID[id]
	if !ok {
		return "", "", "", false
	}
	for _, s := range r.slots[k] {
		if s.ID == id {
			return k.User, k.App, s.Gen, true
		}
	}
	return k.User, k.App, "", true
}

// Release frees a session slot. Unknown IDs are ignored.
func (r *Registry) Release(id ID) {
	if id == "" {
		return
	}
	r.mu.Lock()
	defer r.mu.Unlock()
	k, ok := r.byID[id]
	if !ok {
		return
	}
	delete(r.byID, id)
	cur := r.slots[k]
	out := cur[:0]
	for _, s := range cur {
		if s.ID == id {
			continue
		}
		out = append(out, s)
	}
	if len(out) == 0 {
		delete(r.slots, k)
	} else {
		r.slots[k] = out
	}
}

// Active reports whether user×app currently has any session.
func (r *Registry) Active(user, app string) bool {
	r.mu.Lock()
	defer r.mu.Unlock()
	return len(r.slots[Key{User: user, App: app}]) > 0
}

// ActiveGen reports whether a specific generation has a session.
func (r *Registry) ActiveGen(user, app, gen string) bool {
	r.mu.Lock()
	defer r.mu.Unlock()
	for _, s := range r.slots[Key{User: user, App: app}] {
		if s.Gen == gen {
			return true
		}
	}
	return false
}

// Count returns the number of active sessions.
func (r *Registry) Count() int {
	r.mu.Lock()
	defer r.mu.Unlock()
	return len(r.byID)
}

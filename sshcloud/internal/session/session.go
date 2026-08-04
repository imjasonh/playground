// Package session tracks admitted SSH sessions and enforces concurrency.
package session

import (
	"context"
	"fmt"
	"sync"
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
	ID     ID
	Gen    string
	cancel context.CancelFunc
}

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
	defer r.mu.Unlock()
	k, ok := r.byID[id]
	if !ok {
		return
	}
	slots := r.slots[k]
	for i := range slots {
		if slots[i].ID == id {
			slots[i].cancel = cancel
			r.slots[k] = slots
			return
		}
	}
}

// Kick cancels sessions for user/app/gen (empty gen matches only empty-gen slots).
// Sessions stay registered until Release; the proxy should exit and Release.
func (r *Registry) Kick(user, app, gen string) int {
	k := Key{User: user, App: app}
	r.mu.Lock()
	defer r.mu.Unlock()
	n := 0
	for _, s := range r.slots[k] {
		if s.Gen == gen && s.cancel != nil {
			s.cancel()
			n++
		}
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

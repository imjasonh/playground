// Package session tracks admitted SSH sessions and enforces max-one per user×app.
package session

import (
	"fmt"
	"sync"
)

// ID uniquely identifies an admitted session.
type ID string

// Key is the admission key: one active session per user per app.
type Key struct {
	User string
	App  string
}

func (k Key) String() string { return k.User + "/" + k.App }

// Registry is an in-memory session table for the gateway.
type Registry struct {
	mu      sync.Mutex
	active  map[Key]ID
	byID    map[ID]Key
	nextSeq uint64
}

// NewRegistry returns an empty session registry.
func NewRegistry() *Registry {
	return &Registry{
		active: make(map[Key]ID),
		byID:   make(map[ID]Key),
	}
}

// ErrBusy is returned when the user already has a session on the app.
type ErrBusy struct {
	Key Key
}

func (e ErrBusy) Error() string {
	return fmt.Sprintf("session busy for %s: disconnect the other session first", e.Key)
}

// Admit tries to open a session. On success it returns a session ID that must
// be Released when the SSH connection ends.
func (r *Registry) Admit(user, app string) (ID, error) {
	if user == "" || app == "" {
		return "", fmt.Errorf("user and app are required")
	}
	k := Key{User: user, App: app}

	r.mu.Lock()
	defer r.mu.Unlock()
	if _, ok := r.active[k]; ok {
		return "", ErrBusy{Key: k}
	}
	r.nextSeq++
	id := ID(fmt.Sprintf("sess-%d", r.nextSeq))
	r.active[k] = id
	r.byID[id] = k
	return id, nil
}

// Release frees a session slot. Unknown IDs are ignored.
func (r *Registry) Release(id ID) {
	r.mu.Lock()
	defer r.mu.Unlock()
	k, ok := r.byID[id]
	if !ok {
		return
	}
	delete(r.byID, id)
	if r.active[k] == id {
		delete(r.active, k)
	}
}

// Active reports whether user×app currently has a session.
func (r *Registry) Active(user, app string) bool {
	r.mu.Lock()
	defer r.mu.Unlock()
	_, ok := r.active[Key{User: user, App: app}]
	return ok
}

// Count returns the number of active sessions.
func (r *Registry) Count() int {
	r.mu.Lock()
	defer r.mu.Unlock()
	return len(r.active)
}

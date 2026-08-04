// Package store defines persistence for users, keys, and apps.
// The memory implementation is for tests and early gateway wiring; Firestore later.
package store

import (
	"context"
	"fmt"
	"sync"
)

// User is a registered platform identity (from join).
type User struct {
	ID string // e.g. "alice"
}

// App is an app in a user's namespace.
type App struct {
	Owner  string
	Name   string
	Image  string // digest-pinned reference; empty for lazy platform demos until first wake
	Tier   string // "tiny" | "small"
	Demo   bool   // platform demo (e.g. fortune) — may lazy-create
}

// Store is the control-plane persistence surface used by the gateway.
type Store interface {
	LookupUserByKey(ctx context.Context, keyFingerprint string) (*User, error)
	CreateUser(ctx context.Context, id, keyFingerprint string) error
	AddKey(ctx context.Context, userID, keyFingerprint string) error
	HasApp(ctx context.Context, userID, app string) (bool, error)
	EnsureDemoApp(ctx context.Context, userID, app string) error
	ListApps(ctx context.Context, userID string) ([]App, error)
}

// Memory is an in-memory Store.
type Memory struct {
	mu      sync.Mutex
	users   map[string]*User            // id → user
	keyToID map[string]string           // fingerprint → user id
	apps    map[string]map[string]*App  // user id → app name → app
}

// NewMemory returns an empty memory store.
func NewMemory() *Memory {
	return &Memory{
		users:   make(map[string]*User),
		keyToID: make(map[string]string),
		apps:    make(map[string]map[string]*App),
	}
}

func (m *Memory) LookupUserByKey(_ context.Context, keyFingerprint string) (*User, error) {
	m.mu.Lock()
	defer m.mu.Unlock()
	id, ok := m.keyToID[keyFingerprint]
	if !ok {
		return nil, nil
	}
	u := *m.users[id]
	return &u, nil
}

func (m *Memory) CreateUser(_ context.Context, id, keyFingerprint string) error {
	m.mu.Lock()
	defer m.mu.Unlock()
	if _, ok := m.users[id]; ok {
		return fmt.Errorf("user %q already exists", id)
	}
	if _, ok := m.keyToID[keyFingerprint]; ok {
		return fmt.Errorf("key already registered")
	}
	m.users[id] = &User{ID: id}
	m.keyToID[keyFingerprint] = id
	m.apps[id] = make(map[string]*App)
	return nil
}

func (m *Memory) AddKey(_ context.Context, userID, keyFingerprint string) error {
	m.mu.Lock()
	defer m.mu.Unlock()
	if _, ok := m.users[userID]; !ok {
		return fmt.Errorf("unknown user %q", userID)
	}
	if _, ok := m.keyToID[keyFingerprint]; ok {
		return fmt.Errorf("key already registered")
	}
	m.keyToID[keyFingerprint] = userID
	return nil
}

func (m *Memory) HasApp(_ context.Context, userID, app string) (bool, error) {
	m.mu.Lock()
	defer m.mu.Unlock()
	_, ok := m.apps[userID][app]
	return ok, nil
}

// EnsureDemoApp creates a lazy platform demo app record if missing.
func (m *Memory) EnsureDemoApp(_ context.Context, userID, app string) error {
	m.mu.Lock()
	defer m.mu.Unlock()
	if _, ok := m.users[userID]; !ok {
		return fmt.Errorf("unknown user %q", userID)
	}
	if m.apps[userID] == nil {
		m.apps[userID] = make(map[string]*App)
	}
	if _, ok := m.apps[userID][app]; ok {
		return nil
	}
	m.apps[userID][app] = &App{
		Owner: userID,
		Name:  app,
		Tier:  "tiny",
		Demo:  true,
	}
	return nil
}

func (m *Memory) ListApps(_ context.Context, userID string) ([]App, error) {
	m.mu.Lock()
	defer m.mu.Unlock()
	out := make([]App, 0, len(m.apps[userID]))
	for _, a := range m.apps[userID] {
		out = append(out, *a)
	}
	return out, nil
}

// PlatformDemos are app names the menu always offers (lazy-created on connect).
var PlatformDemos = map[string]struct{}{
	"fortune": {},
}

// IsPlatformDemo reports whether name is a lazy platform demo.
func IsPlatformDemo(name string) bool {
	_, ok := PlatformDemos[name]
	return ok
}

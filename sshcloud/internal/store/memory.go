package store

import (
	"context"
	"fmt"
	"sync"
)

// Memory is an in-memory Store.
type Memory struct {
	mu      sync.Mutex
	users   map[string]*User           // id → user
	keyToID map[string]string          // fingerprint → user id
	apps    map[string]map[string]*App // user id → app name → app
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

func (m *Memory) GetApp(_ context.Context, userID, app string) (*App, error) {
	m.mu.Lock()
	defer m.mu.Unlock()
	a, ok := m.apps[userID][app]
	if !ok {
		return nil, nil
	}
	cp := *a
	return &cp, nil
}

// UpsertApp creates or updates an app record.
func (m *Memory) UpsertApp(_ context.Context, app App) error {
	m.mu.Lock()
	defer m.mu.Unlock()
	if _, ok := m.users[app.Owner]; !ok {
		return fmt.Errorf("unknown user %q", app.Owner)
	}
	if app.Name == "" {
		return fmt.Errorf("app name required")
	}
	if m.apps[app.Owner] == nil {
		m.apps[app.Owner] = make(map[string]*App)
	}
	cp := app
	if cp.Tier == "" {
		cp.Tier = "tiny"
	}
	if cp.SessionStrategy == "" {
		cp.SessionStrategy = StrategyDrain
	}
	m.apps[app.Owner][app.Name] = &cp
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

func (m *Memory) ListAllApps(context.Context) ([]App, error) {
	m.mu.Lock()
	defer m.mu.Unlock()
	var out []App
	for _, apps := range m.apps {
		for _, app := range apps {
			out = append(out, *app)
		}
	}
	return out, nil
}

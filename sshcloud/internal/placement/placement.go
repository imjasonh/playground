// Package placement tracks which host agent owns each user/app instance.
package placement

import (
	"context"
	"fmt"
	"sync"
)

// Store maps (user, app) → host ID.
type Store interface {
	Get(ctx context.Context, user, app string) (hostID string, ok bool, err error)
	Set(ctx context.Context, user, app, hostID string) error
	Delete(ctx context.Context, user, app string) error
}

// Memory is an in-memory placement store.
type Memory struct {
	mu   sync.Mutex
	host map[string]string // "user/app" → hostID
}

// NewMemory returns an empty placement store.
func NewMemory() *Memory {
	return &Memory{host: make(map[string]string)}
}

func key(user, app string) string { return user + "/" + app }

func (m *Memory) Get(_ context.Context, user, app string) (string, bool, error) {
	m.mu.Lock()
	defer m.mu.Unlock()
	h, ok := m.host[key(user, app)]
	return h, ok, nil
}

func (m *Memory) Set(_ context.Context, user, app, hostID string) error {
	if user == "" || app == "" || hostID == "" {
		return fmt.Errorf("user, app, and hostID required")
	}
	m.mu.Lock()
	defer m.mu.Unlock()
	m.host[key(user, app)] = hostID
	return nil
}

func (m *Memory) Delete(_ context.Context, user, app string) error {
	m.mu.Lock()
	defer m.mu.Unlock()
	delete(m.host, key(user, app))
	return nil
}

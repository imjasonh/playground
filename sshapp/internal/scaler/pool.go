package scaler

import (
	"context"
	"fmt"
	"sync"
)

// Pool scales many app Deployments and tracks per-app connection counts.
type Pool struct {
	mu      sync.Mutex
	scalers map[string]*DeploymentScaler
	active  map[string]int
	newApp  func(app string) (*DeploymentScaler, error)
	known   map[string]struct{}
}

// NewPool returns a Pool that builds DeploymentScalers via newApp.
// If apps is non-empty, only those names are allowed.
func NewPool(apps []string, newApp func(app string) (*DeploymentScaler, error)) *Pool {
	known := make(map[string]struct{}, len(apps))
	for _, a := range apps {
		known[a] = struct{}{}
	}
	return &Pool{
		scalers: make(map[string]*DeploymentScaler),
		active:  make(map[string]int),
		newApp:  newApp,
		known:   known,
	}
}

// EnsureReady scales app up if needed and returns a dial address.
func (p *Pool) EnsureReady(ctx context.Context, app string) (string, error) {
	s, err := p.scaler(app)
	if err != nil {
		return "", err
	}
	return s.EnsureReady(ctx)
}

// Acquire notes a new session for app (cancels idle scale-down).
func (p *Pool) Acquire(app string) {
	s, err := p.scaler(app)
	if err != nil {
		return
	}
	p.mu.Lock()
	p.active[app]++
	n := p.active[app]
	p.mu.Unlock()
	s.SetActiveConnections(n)
}

// Release notes a session ended for app (may start idle scale-down).
func (p *Pool) Release(app string) {
	s, err := p.scaler(app)
	if err != nil {
		return
	}
	p.mu.Lock()
	p.active[app]--
	if p.active[app] < 0 {
		p.active[app] = 0
	}
	n := p.active[app]
	p.mu.Unlock()
	s.SetActiveConnections(n)
}

func (p *Pool) scaler(app string) (*DeploymentScaler, error) {
	p.mu.Lock()
	defer p.mu.Unlock()
	if len(p.known) > 0 {
		if _, ok := p.known[app]; !ok {
			return nil, fmt.Errorf("unknown app %q", app)
		}
	}
	if s, ok := p.scalers[app]; ok {
		return s, nil
	}
	s, err := p.newApp(app)
	if err != nil {
		return nil, err
	}
	p.scalers[app] = s
	return s, nil
}

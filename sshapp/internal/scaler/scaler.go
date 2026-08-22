// Package scaler scales a Kubernetes Deployment between zero and warm replicas
// based on activator connection count.
package scaler

import (
	"context"
	"fmt"
	"sync"
	"time"
)

// DeploymentScaler scales one Deployment and resolves a backend address.
type DeploymentScaler struct {
	// ScaleUp sets replicas to WarmReplicas when the app is cold.
	ScaleUp func(ctx context.Context, replicas int32) error
	// ScaleDown sets replicas to 0.
	ScaleDown func(ctx context.Context) error
	// ReadyAddr blocks until a backend pod is ready and returns host:port.
	ReadyAddr func(ctx context.Context) (string, error)

	WarmReplicas int32
	IdleAfter    time.Duration

	mu        sync.Mutex
	active    int
	idleTimer *time.Timer
	scaled    bool
}

// EnsureReady implements proxy.Backend.
func (s *DeploymentScaler) EnsureReady(ctx context.Context) (string, error) {
	if s.WarmReplicas <= 0 {
		s.WarmReplicas = 1
	}

	s.mu.Lock()
	if s.idleTimer != nil {
		s.idleTimer.Stop()
		s.idleTimer = nil
	}
	needScale := !s.scaled
	s.mu.Unlock()

	if needScale {
		if err := s.ScaleUp(ctx, s.WarmReplicas); err != nil {
			return "", fmt.Errorf("scale up: %w", err)
		}
		s.mu.Lock()
		s.scaled = true
		s.mu.Unlock()
	}
	return s.ReadyAddr(ctx)
}

// SetActiveConnections implements proxy.Backend.
func (s *DeploymentScaler) SetActiveConnections(n int) {
	s.mu.Lock()
	defer s.mu.Unlock()
	s.active = n
	if n > 0 {
		if s.idleTimer != nil {
			s.idleTimer.Stop()
			s.idleTimer = nil
		}
		return
	}
	if !s.scaled {
		return
	}
	idleAfter := s.IdleAfter
	if idleAfter <= 0 {
		idleAfter = 5 * time.Minute
	}
	if s.idleTimer != nil {
		s.idleTimer.Stop()
	}
	s.idleTimer = time.AfterFunc(idleAfter, func() {
		s.mu.Lock()
		if s.active != 0 {
			s.mu.Unlock()
			return
		}
		s.mu.Unlock()
		ctx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
		defer cancel()
		if err := s.ScaleDown(ctx); err == nil {
			s.mu.Lock()
			s.scaled = false
			s.mu.Unlock()
		}
	})
}

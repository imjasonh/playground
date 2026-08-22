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
	// ScaleToZero enables idle scale-down. When false, EnsureReady may still
	// scale up to WarmReplicas if the Deployment is at zero, but never down.
	ScaleToZero bool

	mu        sync.Mutex
	active    int
	idleTimer *time.Timer
	scaled    bool
	// gen bumps on every EnsureReady so a concurrent ScaleDown can detect a race.
	gen uint64
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
	s.gen++
	needScale := !s.scaled
	if needScale {
		// Claim warm before releasing the lock so an idle ScaleDown that is
		// already past its active check still sees a newer gen and re-scales up.
		s.scaled = true
	}
	gen := s.gen
	s.mu.Unlock()

	if needScale {
		if err := s.ScaleUp(ctx, s.WarmReplicas); err != nil {
			s.mu.Lock()
			if s.gen == gen {
				s.scaled = false
			}
			s.mu.Unlock()
			return "", fmt.Errorf("scale up: %w", err)
		}
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
	if !s.ScaleToZero || !s.scaled {
		return
	}
	idleAfter := s.IdleAfter
	if idleAfter <= 0 {
		idleAfter = 5 * time.Minute
	}
	if s.idleTimer != nil {
		s.idleTimer.Stop()
	}
	startGen := s.gen
	s.idleTimer = time.AfterFunc(idleAfter, func() {
		s.scaleDownIfIdle(startGen)
	})
}

func (s *DeploymentScaler) scaleDownIfIdle(startGen uint64) {
	s.mu.Lock()
	if s.active != 0 || !s.ScaleToZero || s.gen != startGen {
		s.mu.Unlock()
		return
	}
	// Mark cold before the API call so a concurrent EnsureReady will ScaleUp.
	s.scaled = false
	gen := s.gen
	s.mu.Unlock()

	ctx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
	defer cancel()
	if err := s.ScaleDown(ctx); err != nil {
		s.mu.Lock()
		if s.gen == gen {
			s.scaled = true
		}
		s.mu.Unlock()
		return
	}

	s.mu.Lock()
	raced := s.active != 0 || s.gen != gen
	if raced {
		s.scaled = true
	}
	s.mu.Unlock()
	if !raced {
		return
	}
	// A session arrived during ScaleDown; put replicas back.
	upCtx, upCancel := context.WithTimeout(context.Background(), 30*time.Second)
	defer upCancel()
	_ = s.ScaleUp(upCtx, s.WarmReplicas)
}

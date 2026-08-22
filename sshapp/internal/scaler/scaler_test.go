package scaler_test

import (
	"context"
	"sync/atomic"
	"testing"
	"time"

	"github.com/imjasonh/playground/sshapp/internal/scaler"
)

func TestEnsureReadyScalesUpOnce(t *testing.T) {
	t.Parallel()

	var ups atomic.Int32
	s := &scaler.DeploymentScaler{
		WarmReplicas: 1,
		IdleAfter:    time.Hour,
		ScaleToZero:  true,
		ScaleUp: func(ctx context.Context, replicas int32) error {
			ups.Add(1)
			return nil
		},
		ScaleDown: func(ctx context.Context) error { return nil },
		ReadyAddr: func(ctx context.Context) (string, error) {
			return "127.0.0.1:2222", nil
		},
	}

	addr, err := s.EnsureReady(t.Context())
	if err != nil || addr != "127.0.0.1:2222" {
		t.Fatalf("EnsureReady = %q, %v", addr, err)
	}
	_, _ = s.EnsureReady(t.Context())
	if ups.Load() != 1 {
		t.Fatalf("ScaleUp called %d times, want 1", ups.Load())
	}
}

func TestIdleScalesDown(t *testing.T) {
	t.Parallel()

	down := make(chan struct{}, 1)
	s := &scaler.DeploymentScaler{
		WarmReplicas: 1,
		IdleAfter:    40 * time.Millisecond,
		ScaleToZero:  true,
		ScaleUp:      func(ctx context.Context, replicas int32) error { return nil },
		ScaleDown: func(ctx context.Context) error {
			down <- struct{}{}
			return nil
		},
		ReadyAddr: func(ctx context.Context) (string, error) {
			return "127.0.0.1:2222", nil
		},
	}

	if _, err := s.EnsureReady(t.Context()); err != nil {
		t.Fatal(err)
	}
	s.SetActiveConnections(1)
	s.SetActiveConnections(0)

	select {
	case <-down:
	case <-time.After(time.Second):
		t.Fatal("expected scale down after idle")
	}
}

func TestScaleToZeroFalseNeverScalesDown(t *testing.T) {
	t.Parallel()

	var downs atomic.Int32
	s := &scaler.DeploymentScaler{
		WarmReplicas: 2,
		IdleAfter:    20 * time.Millisecond,
		ScaleToZero:  false,
		ScaleUp:      func(ctx context.Context, replicas int32) error { return nil },
		ScaleDown: func(ctx context.Context) error {
			downs.Add(1)
			return nil
		},
		ReadyAddr: func(ctx context.Context) (string, error) {
			return "127.0.0.1:2222", nil
		},
	}
	if _, err := s.EnsureReady(t.Context()); err != nil {
		t.Fatal(err)
	}
	s.SetActiveConnections(1)
	s.SetActiveConnections(0)
	time.Sleep(80 * time.Millisecond)
	if downs.Load() != 0 {
		t.Fatalf("ScaleDown called %d times", downs.Load())
	}
}

func TestIdleScaleDownRacesEnsureReady(t *testing.T) {
	t.Parallel()

	var ups atomic.Int32
	downStarted := make(chan struct{})
	blockDown := make(chan struct{})
	s := &scaler.DeploymentScaler{
		WarmReplicas: 1,
		IdleAfter:    20 * time.Millisecond,
		ScaleToZero:  true,
		ScaleUp: func(ctx context.Context, replicas int32) error {
			ups.Add(1)
			return nil
		},
		ScaleDown: func(ctx context.Context) error {
			close(downStarted)
			<-blockDown
			return nil
		},
		ReadyAddr: func(ctx context.Context) (string, error) {
			return "127.0.0.1:2222", nil
		},
	}

	if _, err := s.EnsureReady(t.Context()); err != nil {
		t.Fatal(err)
	}
	ups.Store(0)
	s.SetActiveConnections(0)

	select {
	case <-downStarted:
	case <-time.After(time.Second):
		t.Fatal("expected ScaleDown to start")
	}

	// New session while ScaleDown is in flight.
	if _, err := s.EnsureReady(t.Context()); err != nil {
		t.Fatal(err)
	}
	close(blockDown)
	time.Sleep(50 * time.Millisecond)

	if ups.Load() < 1 {
		t.Fatalf("expected ScaleUp after race, got %d", ups.Load())
	}
}

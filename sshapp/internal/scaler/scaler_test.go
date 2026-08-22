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
		ScaleUp: func(ctx context.Context, replicas int32) error {
			ups.Add(1)
			return nil
		},
		ScaleDown: func(ctx context.Context) error { return nil },
		ReadyAddr: func(ctx context.Context) (string, error) {
			return "127.0.0.1:2222", nil
		},
	}

	addr, err := s.EnsureReady(context.Background())
	if err != nil || addr != "127.0.0.1:2222" {
		t.Fatalf("EnsureReady = %q, %v", addr, err)
	}
	_, _ = s.EnsureReady(context.Background())
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
		ScaleUp:      func(ctx context.Context, replicas int32) error { return nil },
		ScaleDown: func(ctx context.Context) error {
			down <- struct{}{}
			return nil
		},
		ReadyAddr: func(ctx context.Context) (string, error) {
			return "127.0.0.1:2222", nil
		},
	}

	if _, err := s.EnsureReady(context.Background()); err != nil {
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

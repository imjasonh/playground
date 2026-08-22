package scaler_test

import (
	"context"
	"testing"
	"time"

	"github.com/imjasonh/playground/sshapp/internal/scaler"
)

func TestPoolUnknownApp(t *testing.T) {
	t.Parallel()
	p := scaler.NewPool([]string{"hello"}, func(app string) (*scaler.DeploymentScaler, error) {
		return &scaler.DeploymentScaler{
			WarmReplicas: 1,
			IdleAfter:    time.Hour,
			ScaleUp:      func(context.Context, int32) error { return nil },
			ScaleDown:    func(context.Context) error { return nil },
			ReadyAddr:    func(context.Context) (string, error) { return "127.0.0.1:1", nil },
		}, nil
	})
	if _, err := p.EnsureReady(t.Context(), "nope"); err == nil {
		t.Fatal("expected unknown app error")
	}
}

func TestPoolEnsureReady(t *testing.T) {
	t.Parallel()
	p := scaler.NewPool([]string{"hello"}, func(app string) (*scaler.DeploymentScaler, error) {
		return &scaler.DeploymentScaler{
			WarmReplicas: 1,
			IdleAfter:    time.Hour,
			ScaleUp:      func(context.Context, int32) error { return nil },
			ScaleDown:    func(context.Context) error { return nil },
			ReadyAddr:    func(context.Context) (string, error) { return "127.0.0.1:2222", nil },
		}, nil
	})
	addr, err := p.EnsureReady(t.Context(), "hello")
	if err != nil || addr != "127.0.0.1:2222" {
		t.Fatalf("EnsureReady = %q, %v", addr, err)
	}
	p.Acquire("hello")
	p.Release("hello")
}

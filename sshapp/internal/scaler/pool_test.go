package scaler_test

import (
	"context"
	"testing"
	"time"

	"github.com/imjasonh/playground/sshapp/internal/scaler"
)

func TestPoolUnknownApp(t *testing.T) {
	t.Parallel()
	p := scaler.NewPool(map[string]scaler.AppSpec{
		"hello": {Replicas: 1, ScaleToZero: true},
	}, func(app string) (*scaler.DeploymentScaler, error) {
		return &scaler.DeploymentScaler{
			WarmReplicas: 1,
			IdleAfter:    time.Hour,
			ScaleToZero:  true,
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
	p := scaler.NewPool(map[string]scaler.AppSpec{
		"hello": {Replicas: 1, ScaleToZero: true},
	}, func(app string) (*scaler.DeploymentScaler, error) {
		return &scaler.DeploymentScaler{
			WarmReplicas: 1,
			IdleAfter:    time.Hour,
			ScaleToZero:  true,
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

func TestPoolPassesPerAppSpec(t *testing.T) {
	t.Parallel()
	var gotReplicas int32
	var gotScaleToZero bool
	p := scaler.NewPool(map[string]scaler.AppSpec{
		"hello": {Replicas: 3, ScaleToZero: false},
	}, func(app string) (*scaler.DeploymentScaler, error) {
		return &scaler.DeploymentScaler{
			WarmReplicas: 3,
			ScaleToZero:  false,
			IdleAfter:    time.Hour,
			ScaleUp: func(_ context.Context, replicas int32) error {
				gotReplicas = replicas
				return nil
			},
			ScaleDown: func(context.Context) error {
				gotScaleToZero = true
				return nil
			},
			ReadyAddr: func(context.Context) (string, error) { return "127.0.0.1:2222", nil },
		}, nil
	})
	if _, err := p.EnsureReady(t.Context(), "hello"); err != nil {
		t.Fatal(err)
	}
	p.Acquire("hello")
	p.Release("hello")
	time.Sleep(30 * time.Millisecond)
	if gotReplicas != 3 {
		t.Fatalf("replicas = %d", gotReplicas)
	}
	if gotScaleToZero {
		t.Fatal("ScaleDown should not run when ScaleToZero is false")
	}
}

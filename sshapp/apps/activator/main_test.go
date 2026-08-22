package main

import (
	"os"
	"testing"
	"time"
)

func TestConfigFromEnv(t *testing.T) {
	t.Setenv("SSHAPP_APP", "hello")
	t.Setenv("SSHAPP_NAMESPACE", "sshapps")
	t.Setenv("SSHAPP_WARM_REPLICAS", "1")
	t.Setenv("SSHAPP_IDLE_AFTER", "30s")
	t.Setenv("SSHAPP_WARM_TIMEOUT", "1m")
	t.Setenv("SSHAPP_BACKEND_PORT", "2222")

	cfg, err := configFromEnv()
	if err != nil {
		t.Fatal(err)
	}
	if cfg.Deployment != "hello" || cfg.Service != "hello" {
		t.Fatalf("deployment/service = %q/%q", cfg.Deployment, cfg.Service)
	}
	if cfg.WarmReplicas != 1 || cfg.IdleAfter != 30*time.Second || cfg.WarmTimeout != time.Minute {
		t.Fatalf("warm/idle/timeout = %+v", cfg)
	}
}

func TestConfigRequiresApp(t *testing.T) {
	_ = os.Unsetenv("SSHAPP_APP")
	t.Setenv("SSHAPP_APP", "")
	if _, err := configFromEnv(); err == nil {
		t.Fatal("expected error when SSHAPP_APP is empty")
	}
}

package main

import (
	"os"
	"testing"
)

func TestMuxConfigFromEnv(t *testing.T) {
	t.Setenv("SSHAPP_APPS", "hello,other")
	t.Setenv("SSHAPP_IDLE_AFTER", "1m")
	cfg, err := muxConfigFromEnv()
	if err != nil {
		t.Fatal(err)
	}
	if len(cfg.Apps) != 2 || cfg.Apps[0] != "hello" {
		t.Fatalf("apps = %#v", cfg.Apps)
	}
	if cfg.IdleAfter.Minutes() != 1 {
		t.Fatalf("idle = %v", cfg.IdleAfter)
	}
}

func TestMuxConfigRequiresApps(t *testing.T) {
	_ = os.Unsetenv("SSHAPP_APPS")
	if _, err := muxConfigFromEnv(); err == nil {
		t.Fatal("expected error")
	}
}

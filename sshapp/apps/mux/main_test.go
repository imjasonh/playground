package main

import (
	"os"
	"testing"
)

func TestMuxConfigFromAppConfig(t *testing.T) {
	t.Setenv("SSHAPP_APP_CONFIG", `{"hello":{"replicas":2,"scale_to_zero":false},"other":{"replicas":1,"scale_to_zero":true}}`)
	t.Setenv("SSHAPP_IDLE_AFTER", "1m")
	_ = os.Unsetenv("SSHAPP_APPS")
	cfg, err := muxConfigFromEnv()
	if err != nil {
		t.Fatal(err)
	}
	hello, ok := cfg.Apps["hello"]
	if !ok || hello.Replicas != 2 || hello.ScaleToZero {
		t.Fatalf("hello = %+v", hello)
	}
	other, ok := cfg.Apps["other"]
	if !ok || other.Replicas != 1 || !other.ScaleToZero {
		t.Fatalf("other = %+v", other)
	}
	if cfg.IdleAfter.Minutes() != 1 {
		t.Fatalf("idle = %v", cfg.IdleAfter)
	}
}

func TestMuxConfigLegacyAppsCSV(t *testing.T) {
	_ = os.Unsetenv("SSHAPP_APP_CONFIG")
	t.Setenv("SSHAPP_APPS", "hello,other")
	cfg, err := muxConfigFromEnv()
	if err != nil {
		t.Fatal(err)
	}
	if len(cfg.Apps) != 2 || !cfg.Apps["hello"].ScaleToZero {
		t.Fatalf("apps = %#v", cfg.Apps)
	}
}

func TestMuxConfigRequiresApps(t *testing.T) {
	_ = os.Unsetenv("SSHAPP_APP_CONFIG")
	_ = os.Unsetenv("SSHAPP_APPS")
	if _, err := muxConfigFromEnv(); err == nil {
		t.Fatal("expected error")
	}
}

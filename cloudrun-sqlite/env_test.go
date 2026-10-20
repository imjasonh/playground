package main

import (
	"log/slog"
	"path/filepath"
	"testing"
	"time"

	"github.com/imjasonh/playground/cloudrun-sqlite/internal/store"
)

func TestLoadServeEnv(t *testing.T) {
	def := store.DefaultConfig()
	env, err := loadServeEnv()
	if err != nil {
		t.Fatal(err)
	}
	if env.Port != "8080" {
		t.Errorf("port = %q, want 8080", env.Port)
	}
	if env.Durable != def.Durable || env.CacheSize != def.CacheSize || env.SnapshotPlanLen != def.SnapshotPlanLen || env.PollInterval != def.PollInterval {
		t.Errorf("defaults = durable %v cache %d plan %d poll %s, want durable %v cache %d plan %d poll %s",
			env.Durable, env.CacheSize, env.SnapshotPlanLen, env.PollInterval,
			def.Durable, def.CacheSize, def.SnapshotPlanLen, def.PollInterval)
	}
	if env.VFSLogLevel != slog.LevelWarn {
		t.Errorf("vfs level = %s, want WARN", env.VFSLogLevel)
	}
	if filepath.Base(env.Dir) != "cloudrun-sqlite" {
		t.Errorf("dir = %q, want it to end in cloudrun-sqlite", env.Dir)
	}
	if env.Hydrate {
		t.Error("hydrate default is true")
	}
}

func TestLoadServeEnvOverrides(t *testing.T) {
	t.Setenv("REPLICA_URL", "file:///tmp/replica")
	t.Setenv("DATA_DIR", "/tmp/data")
	t.Setenv("DURABLE", "false")
	t.Setenv("HYDRATE", "true")
	t.Setenv("CACHE_SIZE", "1024")
	t.Setenv("SNAPSHOT_PLAN_LEN", "8")
	t.Setenv("POLL_INTERVAL", "1s")
	t.Setenv("PORT", "9090")
	t.Setenv("VFS_LOG_LEVEL", "debug")
	t.Setenv("ADMIN_TOKEN", "secret")

	env, err := loadServeEnv()
	if err != nil {
		t.Fatal(err)
	}
	if env.ReplicaURL != "file:///tmp/replica" || env.Dir != "/tmp/data" || env.Durable || !env.Hydrate {
		t.Errorf("replica %q dir %q durable %v hydrate %v", env.ReplicaURL, env.Dir, env.Durable, env.Hydrate)
	}
	if env.CacheSize != 1024 || env.SnapshotPlanLen != 8 || env.PollInterval != time.Second {
		t.Errorf("cache %d plan %d poll %s", env.CacheSize, env.SnapshotPlanLen, env.PollInterval)
	}
	if env.Port != "9090" || env.VFSLogLevel != slog.LevelDebug || env.AdminToken != "secret" {
		t.Errorf("port %q vfs %s token %q", env.Port, env.VFSLogLevel, env.AdminToken)
	}
}

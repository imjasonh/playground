package config_test

import (
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/imjasonh/playground/node-image/internal/config"
)

func TestLoadDefaultsNODE_ENV(t *testing.T) {
	dir := t.TempDir()
	writePJ(t, dir, `{"name":"x","main":"index.js"}`)
	cfg, _, err := config.Load(dir)
	if err != nil {
		t.Fatal(err)
	}
	env := cfg.EnvList()
	if !containsKV(env, "NODE_ENV=production") {
		t.Fatalf("expected NODE_ENV=production, got %v", env)
	}
}

func TestLoadEnvOverrideNODE_ENV(t *testing.T) {
	dir := t.TempDir()
	writePJ(t, dir, `{
		"name":"x","main":"index.js",
		"node-image":{"env":{"NODE_ENV":"development","FOO":"bar"}}
	}`)
	cfg, _, err := config.Load(dir)
	if err != nil {
		t.Fatal(err)
	}
	env := cfg.EnvList()
	if !containsKV(env, "NODE_ENV=development") {
		t.Fatalf("expected NODE_ENV=development, got %v", env)
	}
	if !containsKV(env, "FOO=bar") {
		t.Fatalf("expected FOO=bar, got %v", env)
	}
}

func TestResolveMainPrefersDistOverTS(t *testing.T) {
	dir := t.TempDir()
	if err := os.MkdirAll(filepath.Join(dir, "dist"), 0o755); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(filepath.Join(dir, "dist", "index.js"), []byte("ok"), 0o644); err != nil {
		t.Fatal(err)
	}
	got, err := config.ResolveMain(dir, "index.ts", true)
	if err != nil {
		t.Fatal(err)
	}
	if got != "dist/index.js" {
		t.Fatalf("got %q", got)
	}
}

func TestResolveMainFailsOnTSWithoutBuild(t *testing.T) {
	dir := t.TempDir()
	_, err := config.ResolveMain(dir, "index.ts", false)
	if err == nil {
		t.Fatal("expected error")
	}
	if !strings.Contains(err.Error(), "TypeScript") {
		t.Fatalf("unexpected: %v", err)
	}
}

func TestResolveMainExplicitNodeImageMain(t *testing.T) {
	dir := t.TempDir()
	if err := os.MkdirAll(filepath.Join(dir, "dist"), 0o755); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(filepath.Join(dir, "dist", "server.js"), []byte("ok"), 0o644); err != nil {
		t.Fatal(err)
	}
	got, err := config.ResolveMain(dir, "dist/server.js", true)
	if err != nil {
		t.Fatal(err)
	}
	if got != "dist/server.js" {
		t.Fatalf("got %q", got)
	}
}

func TestCmdUsesWorkdir(t *testing.T) {
	cfg := &config.Config{Workdir: "/app", Main: "dist/index.js"}
	cmd := cfg.Cmd()
	if len(cmd) != 1 || cmd[0] != "/app/dist/index.js" {
		t.Fatalf("got %v", cmd)
	}
}

func writePJ(t *testing.T, dir, body string) {
	t.Helper()
	if err := os.WriteFile(filepath.Join(dir, "package.json"), []byte(body), 0o644); err != nil {
		t.Fatal(err)
	}
}

func containsKV(env []string, want string) bool {
	for _, e := range env {
		if e == want {
			return true
		}
	}
	return false
}

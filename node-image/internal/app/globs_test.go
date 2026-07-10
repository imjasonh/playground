package app_test

import (
	"os"
	"path/filepath"
	"testing"

	"github.com/imjasonh/playground/node-image/internal/app"
)

func TestCollectOutputsGlobs(t *testing.T) {
	dir := t.TempDir()
	if err := os.MkdirAll(filepath.Join(dir, "build", "scripts"), 0o755); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(filepath.Join(dir, "build", "index.js"), []byte("ok"), 0o644); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(filepath.Join(dir, "build", "scripts", "x.lua"), []byte("x"), 0o644); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(filepath.Join(dir, "build", "index.js.map"), []byte("map"), 0o644); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(filepath.Join(dir, "package.json"), []byte(`{"name":"x"}`), 0o644); err != nil {
		t.Fatal(err)
	}
	outs, err := app.CollectOutputsOpts(dir, app.CollectOptions{
		Include: []string{"build/**", "package.json"},
		Exclude: []string{"**/*.map"},
	})
	if err != nil {
		t.Fatal(err)
	}
	if _, ok := outs["build/scripts/x.lua"]; !ok {
		t.Fatalf("missing lua: %#v", outs)
	}
	if _, ok := outs["build/index.js.map"]; ok {
		t.Fatal("map should be excluded")
	}
}

func TestCollectOutputsPrefersBuild(t *testing.T) {
	dir := t.TempDir()
	if err := os.MkdirAll(filepath.Join(dir, "build"), 0o755); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(filepath.Join(dir, "build", "index.js"), []byte("ok"), 0o644); err != nil {
		t.Fatal(err)
	}
	outs, err := app.CollectOutputs(dir)
	if err != nil {
		t.Fatal(err)
	}
	if _, ok := outs["build/index.js"]; !ok {
		t.Fatalf("%#v", outs)
	}
}

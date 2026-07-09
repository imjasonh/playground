package app_test

import (
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/imjasonh/playground/node-image/internal/app"
)

func TestRequireMainMissing(t *testing.T) {
	dir := t.TempDir()
	if err := os.WriteFile(filepath.Join(dir, "package.json"), []byte(`{"main":"dist/index.js"}`), 0o644); err != nil {
		t.Fatal(err)
	}
	outputs, err := app.CollectOutputs(dir)
	if err != nil {
		t.Fatal(err)
	}
	err = app.RequireMain(dir, "dist/index.js", outputs)
	if err == nil {
		t.Fatal("expected missing main to fail")
	}
	if !strings.Contains(err.Error(), "dist/index.js") {
		t.Fatalf("got %v", err)
	}
}

func TestRequireMainPresent(t *testing.T) {
	dir := t.TempDir()
	if err := os.MkdirAll(filepath.Join(dir, "dist"), 0o755); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(filepath.Join(dir, "package.json"), []byte(`{"main":"dist/index.js"}`), 0o644); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(filepath.Join(dir, "dist", "index.js"), []byte("console.log(1)"), 0o644); err != nil {
		t.Fatal(err)
	}
	outputs, err := app.CollectOutputs(dir)
	if err != nil {
		t.Fatal(err)
	}
	if err := app.RequireMain(dir, "dist/index.js", outputs); err != nil {
		t.Fatal(err)
	}
}

func TestCollectOutputsRejectsSymlink(t *testing.T) {
	dir := t.TempDir()
	if err := os.MkdirAll(filepath.Join(dir, "dist"), 0o755); err != nil {
		t.Fatal(err)
	}
	outside := filepath.Join(dir, "secret")
	if err := os.WriteFile(outside, []byte("secret"), 0o644); err != nil {
		t.Fatal(err)
	}
	if err := os.Symlink(outside, filepath.Join(dir, "dist", "index.js")); err != nil {
		t.Fatal(err)
	}
	_, err := app.CollectOutputs(dir)
	if err == nil || !strings.Contains(err.Error(), "symlink") {
		t.Fatalf("expected symlink rejection, got %v", err)
	}
}

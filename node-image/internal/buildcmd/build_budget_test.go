package buildcmd_test

import (
	"bytes"
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/imjasonh/playground/node-image/internal/buildcmd"
)

func TestBuildWithTinyLayerBudgetBuckets(t *testing.T) {
	fixture, err := filepath.Abs(filepath.Join("..", "..", "testdata", "pure-js"))
	if err != nil {
		t.Fatal(err)
	}
	out := t.TempDir()
	var stdout, stderr bytes.Buffer
	_, err = buildcmd.Run(buildcmd.Options{
		Dir:       fixture,
		NoPush:    true,
		OCIDir:    out,
		EmptyBase: true,
		SkipBuild: true,
		Platforms: []string{"linux/amd64"},
		MaxLayers: 3, // base 0 + store slots 1 + symlink + app => 1 store bucket
		Stdout:    &stdout,
		Stderr:    &stderr,
	})
	if err != nil {
		t.Fatalf("%v\nstderr=%s", err, stderr.String())
	}
	// With only one package, no budget message required; ensure layers file exists.
	b, err := os.ReadFile(filepath.Join(out, "layers"))
	if err != nil {
		t.Fatal(err)
	}
	lines := strings.Split(strings.TrimSpace(string(b)), "\n")
	// empty base + 1 store + symlink + app = 3 layers
	if len(lines) != 3 {
		t.Fatalf("want 3 layers, got %d:\n%s\nstderr=%s", len(lines), b, stderr.String())
	}
}

func TestRejectMuslBase(t *testing.T) {
	fixture, err := filepath.Abs(filepath.Join("..", "..", "testdata", "pure-js"))
	if err != nil {
		t.Fatal(err)
	}
	// Use a well-known alpine tag; Inspect needs network. Skip if pull fails.
	var stdout, stderr bytes.Buffer
	_, err = buildcmd.Run(buildcmd.Options{
		Dir:       fixture,
		Base:      "node:22-alpine",
		NoPush:    true,
		OCIDir:    t.TempDir(),
		SkipBuild: true,
		Platforms: []string{"linux/amd64"},
		Stdout:    &stdout,
		Stderr:    &stderr,
	})
	if err == nil {
		t.Fatal("expected musl base to fail")
	}
	if !strings.Contains(err.Error(), "musl") {
		if strings.Contains(err.Error(), "pull base") {
			t.Skipf("network/pull unavailable: %v", err)
		}
		t.Fatalf("expected musl error, got: %v", err)
	}
}

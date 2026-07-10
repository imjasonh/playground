package buildcmd_test

import (
	"bytes"
	"path/filepath"
	"strings"
	"testing"

	"github.com/imjasonh/playground/node-image/internal/buildcmd"
)

func TestBuildShortCircuitNoOp(t *testing.T) {
	dir := fixtureDir(t, "pure-js")
	cache := t.TempDir()
	var out1, err1 bytes.Buffer
	ref1, err := buildcmd.Run(buildcmd.Options{
		Dir:       dir,
		NoPush:    true,
		OCIDir:    t.TempDir(),
		EmptyBase: true,
		SkipBuild: true,
		Platforms: []string{"linux/amd64"},
		CacheDir:  cache,
		Stdout:    &out1,
		Stderr:    &err1,
	})
	if err != nil {
		t.Fatalf("first build: %v\n%s", err, err1.String())
	}

	var out2, err2 bytes.Buffer
	ref2, err := buildcmd.Run(buildcmd.Options{
		Dir:       dir,
		NoPush:    true,
		OCIDir:    t.TempDir(),
		EmptyBase: true,
		SkipBuild: true,
		Platforms: []string{"linux/amd64"},
		CacheDir:  cache,
		Stdout:    &out2,
		Stderr:    &err2,
	})
	if err != nil {
		t.Fatalf("second build: %v\n%s", err, err2.String())
	}
	if ref1 != ref2 {
		t.Fatalf("refs differ: %q vs %q", ref1, ref2)
	}
	if !strings.Contains(err2.String(), "cache hit") {
		t.Fatalf("expected cache hit on second build, stderr=%s", err2.String())
	}
	// Build record should exist under cache/builds
	entries, _ := filepath.Glob(filepath.Join(cache, "builds", "*.json"))
	if len(entries) == 0 {
		t.Fatal("expected build fingerprint record")
	}
}

package buildcmd_test

import (
	"bytes"
	"os"
	"path/filepath"
	"strings"
	"testing"
	"time"

	"github.com/imjasonh/playground/node-image/internal/buildcmd"
)

// TestBuildWarmCacheReusesDigestQuickly asserts successive identical builds
// with a shared --cache-dir hit the image fingerprint short-circuit, return
// the same digest, and finish the second build quickly.
func TestBuildWarmCacheReusesDigestQuickly(t *testing.T) {
	dir := fixtureDir(t, "pure-js")
	cache := t.TempDir()
	opts := func(oci string, stdout, stderr *bytes.Buffer) buildcmd.Options {
		return buildcmd.Options{
			Dir:       dir,
			NoPush:    true,
			OCIDir:    oci,
			EmptyBase: true,
			SkipBuild: true,
			Platforms: []string{"linux/amd64"},
			CacheDir:  cache,
			Stdout:    stdout,
			Stderr:    stderr,
		}
	}

	var out1, err1 bytes.Buffer
	start1 := time.Now()
	ref1, err := buildcmd.Run(opts(t.TempDir(), &out1, &err1))
	cold := time.Since(start1)
	if err != nil {
		t.Fatalf("cold build: %v\n%s", err, err1.String())
	}
	if !strings.HasPrefix(ref1, "sha256:") {
		t.Fatalf("cold ref %q", ref1)
	}

	var out2, err2 bytes.Buffer
	start2 := time.Now()
	ref2, err := buildcmd.Run(opts(t.TempDir(), &out2, &err2))
	warm := time.Since(start2)
	if err != nil {
		t.Fatalf("warm build: %v\n%s", err, err2.String())
	}
	if ref1 != ref2 {
		t.Fatalf("warm digest changed: cold=%s warm=%s", ref1, ref2)
	}
	if !strings.Contains(err2.String(), "cache hit") {
		t.Fatalf("expected fingerprint cache hit, stderr=%s", err2.String())
	}
	entries, _ := filepath.Glob(filepath.Join(cache, "builds", "*.json"))
	if len(entries) == 0 {
		t.Fatal("expected builds/ fingerprint record")
	}

	// Warm path must be fast in absolute terms and clearly cheaper than cold.
	const warmBudget = 2 * time.Second
	if warm > warmBudget {
		t.Fatalf("warm build too slow: %v (budget %v); cold was %v\nstderr=%s", warm, warmBudget, cold, err2.String())
	}
	if cold > 500*time.Millisecond && warm*5 > cold {
		t.Fatalf("warm build not clearly faster than cold: warm=%v cold=%v", warm, cold)
	}
	t.Logf("cold=%v warm=%v digest=%s", cold, warm, ref1)

	var out3, err3 bytes.Buffer
	ref3, err := buildcmd.Run(opts(t.TempDir(), &out3, &err3))
	if err != nil {
		t.Fatalf("third build: %v\n%s", err, err3.String())
	}
	if ref3 != ref1 {
		t.Fatalf("third digest changed: %s vs %s", ref1, ref3)
	}
}

// TestBuildDeterministicWithoutCache asserts two builds with isolated empty
// cache dirs (no shared packages/spool/layers/builds) produce the same digest.
func TestBuildDeterministicWithoutCache(t *testing.T) {
	dir := fixtureDir(t, "pure-js")
	run := func(cache string) (string, error) {
		var stdout, stderr bytes.Buffer
		return buildcmd.Run(buildcmd.Options{
			Dir:       dir,
			NoPush:    true,
			OCIDir:    t.TempDir(),
			EmptyBase: true,
			SkipBuild: true,
			Platforms: []string{"linux/amd64"},
			CacheDir:  cache,
			Stdout:    &stdout,
			Stderr:    &stderr,
		})
	}

	ref1, err := run(t.TempDir())
	if err != nil {
		t.Fatalf("build 1: %v", err)
	}
	ref2, err := run(t.TempDir())
	if err != nil {
		t.Fatalf("build 2: %v", err)
	}
	if ref1 != ref2 {
		t.Fatalf("cache-less digests differ:\n  %s\n  %s", ref1, ref2)
	}
	if !strings.HasPrefix(ref1, "sha256:") {
		t.Fatalf("ref %q", ref1)
	}
}

// TestBuildLayerCacheSameDigestWithoutShortCircuit uses a shared layer/package
// cache but clears the builds/ fingerprint store between runs, so the second
// build still plans/assembles layers (warm blob cache) and must match digest.
func TestBuildLayerCacheSameDigestWithoutShortCircuit(t *testing.T) {
	dir := fixtureDir(t, "pure-js")
	cache := t.TempDir()
	run := func() (string, string, error) {
		var stdout, stderr bytes.Buffer
		ref, err := buildcmd.Run(buildcmd.Options{
			Dir:       dir,
			NoPush:    true,
			OCIDir:    t.TempDir(),
			EmptyBase: true,
			SkipBuild: true,
			Platforms: []string{"linux/amd64"},
			CacheDir:  cache,
			Stdout:    &stdout,
			Stderr:    &stderr,
		})
		return ref, stderr.String(), err
	}

	ref1, stderr1, err := run()
	if err != nil {
		t.Fatalf("first: %v\n%s", err, stderr1)
	}

	if err := os.RemoveAll(filepath.Join(cache, "builds")); err != nil {
		t.Fatal(err)
	}

	ref2, stderr2, err := run()
	if err != nil {
		t.Fatalf("second: %v\n%s", err, stderr2)
	}
	if strings.Contains(stderr2, "cache hit") {
		t.Fatalf("short-circuit should be disabled after clearing builds/: %s", stderr2)
	}
	if ref1 != ref2 {
		t.Fatalf("layer-cache digests differ:\n  %s\n  %s", ref1, ref2)
	}
}

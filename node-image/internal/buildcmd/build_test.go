package buildcmd_test

import (
	"bytes"
	"os"
	"path/filepath"
	"testing"

	"github.com/imjasonh/playground/node-image/internal/buildcmd"
)

func TestBuildNoPushEmptyBase(t *testing.T) {
	fixture, err := filepath.Abs(filepath.Join("..", "..", "testdata", "pure-js"))
	if err != nil {
		t.Fatal(err)
	}
	out := t.TempDir()
	var stdout, stderr bytes.Buffer
	ref, err := buildcmd.Run(buildcmd.Options{
		Dir:       fixture,
		NoPush:    true,
		OCIDir:    out,
		EmptyBase: true,
		SkipBuild: true,
		Platforms: []string{"linux/amd64"},
		Stdout:    &stdout,
		Stderr:    &stderr,
	})
	if err != nil {
		t.Fatalf("%v\nstderr=%s", err, stderr.String())
	}
	if ref == "" {
		t.Fatal("empty ref")
	}
	if _, err := os.Stat(filepath.Join(out, "digest")); err != nil {
		t.Fatal(err)
	}
	if _, err := os.Stat(filepath.Join(out, "layers")); err != nil {
		t.Fatal(err)
	}
	// Second build should be deterministic
	out2 := t.TempDir()
	ref2, err := buildcmd.Run(buildcmd.Options{
		Dir:       fixture,
		NoPush:    true,
		OCIDir:    out2,
		EmptyBase: true,
		SkipBuild: true,
		Platforms: []string{"linux/amd64"},
		Stdout:    &bytes.Buffer{},
		Stderr:    &bytes.Buffer{},
	})
	if err != nil {
		t.Fatal(err)
	}
	if ref != ref2 {
		t.Fatalf("not deterministic: %s vs %s", ref, ref2)
	}
}

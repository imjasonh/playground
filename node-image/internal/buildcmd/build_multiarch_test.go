package buildcmd_test

import (
	"bytes"
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/imjasonh/playground/node-image/internal/buildcmd"
)

func TestBuildMultiArchIndex(t *testing.T) {
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
		Platforms: []string{"linux/amd64", "linux/arm64"},
		Stdout:    &stdout,
		Stderr:    &stderr,
	})
	if err != nil {
		t.Fatalf("%v\nstderr=%s", err, stderr.String())
	}
	if ref == "" {
		t.Fatal("empty ref")
	}
	b, err := os.ReadFile(filepath.Join(out, "platforms"))
	if err != nil {
		t.Fatal(err)
	}
	text := string(b)
	if !strings.Contains(text, "linux/amd64") || !strings.Contains(text, "linux/arm64") {
		t.Fatalf("platforms file: %q", text)
	}
	lines := strings.Split(strings.TrimSpace(text), "\n")
	if len(lines) != 2 {
		t.Fatalf("want 2 platforms, got %d: %q", len(lines), text)
	}
	// Image digests differ by arch (config.Architecture), but both must be present.
	d1 := strings.Fields(lines[0])[1]
	d2 := strings.Fields(lines[1])[1]
	if d1 == "" || d2 == "" {
		t.Fatalf("missing digests: %q", text)
	}
	dig, err := os.ReadFile(filepath.Join(out, "digest"))
	if err != nil {
		t.Fatal(err)
	}
	if string(dig) != ref {
		t.Fatalf("digest file %q != returned %q", dig, ref)
	}
}

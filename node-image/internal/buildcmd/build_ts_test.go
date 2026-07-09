package buildcmd_test

import (
	"bytes"
	"os"
	"os/exec"
	"path/filepath"
	"testing"

	"github.com/imjasonh/playground/node-image/internal/buildcmd"
)

func TestBuildTSAppWithCompile(t *testing.T) {
	if _, err := exec.LookPath("pnpm"); err != nil {
		t.Skip("pnpm not on PATH")
	}
	fixture, err := filepath.Abs(filepath.Join("..", "..", "testdata", "ts-app"))
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
	if _, err := os.Stat(filepath.Join(fixture, "dist", "index.js")); err != nil {
		t.Fatalf("expected compile output: %v\nstderr=%s", err, stderr.String())
	}
	// package.json main is src/index.ts; builder should pick dist/index.js.
	if !bytes.Contains(stderr.Bytes(), []byte("entrypoint: using dist/index.js")) {
		t.Fatalf("expected entrypoint resolution message, stderr=%s", stderr.String())
	}
}

package kodata

import (
	"os"
	"path/filepath"
	"testing"
)

func TestFind(t *testing.T) {
	app := t.TempDir()
	pkg := filepath.Join(app, "cmd", "app")
	if err := os.MkdirAll(filepath.Join(pkg, "kodata"), 0o755); err != nil {
		t.Fatal(err)
	}
	got, err := Find(app, "./cmd/app")
	if err != nil {
		t.Fatal(err)
	}
	if got != filepath.Join(pkg, "kodata") {
		t.Fatalf("got %q", got)
	}
	missing, err := Find(app, ".")
	if err != nil {
		t.Fatal(err)
	}
	if missing != "" {
		t.Fatalf("expected empty, got %q", missing)
	}
}

func TestCopyTreeFollowsSymlink(t *testing.T) {
	srcRoot := t.TempDir()
	real := filepath.Join(srcRoot, "real")
	if err := os.MkdirAll(real, 0o755); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(filepath.Join(real, "a.txt"), []byte("hi"), 0o644); err != nil {
		t.Fatal(err)
	}
	kodataDir := filepath.Join(srcRoot, "kodata")
	if err := os.MkdirAll(kodataDir, 0o755); err != nil {
		t.Fatal(err)
	}
	if err := os.Symlink(real, filepath.Join(kodataDir, "linked")); err != nil {
		t.Fatal(err)
	}
	dest := filepath.Join(t.TempDir(), "out")
	if err := CopyTree(kodataDir, dest); err != nil {
		t.Fatal(err)
	}
	b, err := os.ReadFile(filepath.Join(dest, "linked", "a.txt"))
	if err != nil {
		t.Fatal(err)
	}
	if string(b) != "hi" {
		t.Fatalf("got %q", b)
	}
}

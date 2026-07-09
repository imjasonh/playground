package lock_test

import (
	"os"
	"path/filepath"
	"testing"

	"github.com/imjasonh/playground/node-image/internal/lock"
)

func TestParsePureJSFixture(t *testing.T) {
	path := filepath.Join("..", "..", "testdata", "pure-js", "pnpm-lock.yaml")
	l, err := lock.ParseFile(path)
	if err != nil {
		t.Fatal(err)
	}
	if l.LockfileVersion != "9.0" {
		t.Fatalf("version: %q", l.LockfileVersion)
	}
	imp := l.Importers["."]
	if imp == nil {
		t.Fatal("missing root importer")
	}
	dep, ok := imp.Dependencies["ms"]
	if !ok || dep.Version != "2.1.3" {
		t.Fatalf("ms dep: %+v", dep)
	}
	pkg := l.Packages["ms@2.1.3"]
	if pkg == nil || pkg.Resolution.Integrity == "" {
		t.Fatalf("ms package: %+v", pkg)
	}
	if _, ok := l.Snapshots["ms@2.1.3"]; !ok {
		t.Fatal("missing snapshot")
	}
}

func TestRejectOldLockfile(t *testing.T) {
	_, err := lock.Parse([]byte("lockfileVersion: '6.0'\nimporters: {}\npackages: {}\n"))
	if err == nil {
		t.Fatal("expected error")
	}
}

func TestPackageIDFromDepPath(t *testing.T) {
	cases := map[string]string{
		"foo@1.0.0":                    "foo@1.0.0",
		"foo@1.0.0(bar@2.0.0)":         "foo@1.0.0",
		"@scope/pkg@1.0.0(react@18.0.0)": "@scope/pkg@1.0.0",
	}
	for in, want := range cases {
		if got := lock.PackageIDFromDepPath(in); got != want {
			t.Fatalf("%q: got %q want %q", in, got, want)
		}
	}
}

func TestFindLockfile(t *testing.T) {
	root := t.TempDir()
	sub := filepath.Join(root, "apps", "api")
	if err := os.MkdirAll(sub, 0o755); err != nil {
		t.Fatal(err)
	}
	lockPath := filepath.Join(root, "pnpm-lock.yaml")
	if err := os.WriteFile(lockPath, []byte("lockfileVersion: '9.0'\nimporters: {}\npackages: {}\n"), 0o644); err != nil {
		t.Fatal(err)
	}
	got, lockRoot, err := lock.FindLockfile(sub)
	if err != nil {
		t.Fatal(err)
	}
	if got != lockPath || lockRoot != root {
		t.Fatalf("got %q root %q", got, lockRoot)
	}
	key, err := lock.ImporterKey(lockRoot, sub)
	if err != nil {
		t.Fatal(err)
	}
	if key != "apps/api" {
		t.Fatalf("importer key %q", key)
	}
}

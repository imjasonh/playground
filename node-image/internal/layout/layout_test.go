package layout_test

import (
	"os"
	"os/exec"
	"path/filepath"
	"testing"

	"github.com/imjasonh/playground/node-image/internal/fetch"
	"github.com/imjasonh/playground/node-image/internal/layout"
	"github.com/imjasonh/playground/node-image/internal/lock"
	"github.com/imjasonh/playground/node-image/internal/resolve"
)

func TestMaterializePureJSRequiresMS(t *testing.T) {
	fixture := filepath.Join("..", "..", "testdata", "pure-js")
	l, err := lock.ParseFile(filepath.Join(fixture, "pnpm-lock.yaml"))
	if err != nil {
		t.Fatal(err)
	}
	refs, err := resolve.Closure(l, ".", resolve.LinuxAmd64)
	if err != nil {
		t.Fatal(err)
	}
	cacheDir := t.TempDir()
	c := &fetch.Cache{Dir: cacheDir}
	tarballs := map[string]string{}
	for _, ref := range refs {
		path, err := c.Ensure(ref.Tarball, ref.Integrity)
		if err != nil {
			t.Skipf("network/fetch unavailable: %v", err)
		}
		tarballs[ref.PackageID] = path
	}
	root := t.TempDir()
	// copy package.json + index.js so node can run
	for _, name := range []string{"package.json", "index.js"} {
		b, err := os.ReadFile(filepath.Join(fixture, name))
		if err != nil {
			t.Fatal(err)
		}
		if err := os.WriteFile(filepath.Join(root, name), b, 0o644); err != nil {
			t.Fatal(err)
		}
	}
	if _, err := layout.Materialize(root, l, refs, tarballs, resolve.DirectNames(l, ".")); err != nil {
		t.Fatal(err)
	}
	msLink := filepath.Join(root, "node_modules", "ms")
	if _, err := os.Lstat(msLink); err != nil {
		t.Fatal(err)
	}
	target, err := os.Readlink(msLink)
	if err != nil {
		t.Fatal(err)
	}
	if target == "" {
		t.Fatal("empty symlink")
	}
	pkgJSON := filepath.Join(root, "node_modules", ".pnpm", "ms@2.1.3", "node_modules", "ms", "package.json")
	if _, err := os.Stat(pkgJSON); err != nil {
		t.Fatal(err)
	}
	if _, err := exec.LookPath("node"); err != nil {
		t.Skip("node not installed")
	}
	cmd := exec.Command("node", "index.js")
	cmd.Dir = root
	out, err := cmd.CombinedOutput()
	if err != nil {
		t.Fatalf("node: %v\n%s", err, out)
	}
	if got := string(out); got != "1m\n" && got != "1m\r\n" {
		t.Fatalf("unexpected output %q", got)
	}
}

func TestConformanceAgainstPnpm(t *testing.T) {
	if _, err := exec.LookPath("pnpm"); err != nil {
		t.Skip("pnpm not on PATH")
	}
	fixture := filepath.Join("..", "..", "testdata", "pure-js")
	oracle := t.TempDir()
	for _, name := range []string{"package.json", "pnpm-lock.yaml"} {
		b, _ := os.ReadFile(filepath.Join(fixture, name))
		_ = os.WriteFile(filepath.Join(oracle, name), b, 0o644)
	}
	cmd := exec.Command("pnpm", "install", "--ignore-scripts", "--prod", "--frozen-lockfile")
	cmd.Dir = oracle
	if out, err := cmd.CombinedOutput(); err != nil {
		t.Fatalf("pnpm: %v\n%s", err, out)
	}

	l, err := lock.ParseFile(filepath.Join(fixture, "pnpm-lock.yaml"))
	if err != nil {
		t.Fatal(err)
	}
	refs, err := resolve.Closure(l, ".", resolve.LinuxAmd64)
	if err != nil {
		t.Fatal(err)
	}
	c := &fetch.Cache{Dir: t.TempDir()}
	tarballs := map[string]string{}
	for _, ref := range refs {
		path, err := c.Ensure(ref.Tarball, ref.Integrity)
		if err != nil {
			t.Skipf("fetch: %v", err)
		}
		tarballs[ref.PackageID] = path
	}
	ours := t.TempDir()
	if _, err := layout.Materialize(ours, l, refs, tarballs, resolve.DirectNames(l, ".")); err != nil {
		t.Fatal(err)
	}

	// Compare extracted package file bytes for ms.
	oraclePkg := filepath.Join(oracle, "node_modules", ".pnpm", "ms@2.1.3", "node_modules", "ms", "package.json")
	oursPkg := filepath.Join(ours, "node_modules", ".pnpm", "ms@2.1.3", "node_modules", "ms", "package.json")
	ob, err := os.ReadFile(oraclePkg)
	if err != nil {
		t.Fatal(err)
	}
	ub, err := os.ReadFile(oursPkg)
	if err != nil {
		t.Fatal(err)
	}
	if string(ob) != string(ub) {
		t.Fatal("package.json mismatch vs pnpm oracle")
	}
	// Top-level symlink must exist in both.
	for _, root := range []string{oracle, ours} {
		if _, err := os.Lstat(filepath.Join(root, "node_modules", "ms")); err != nil {
			t.Fatalf("%s: %v", root, err)
		}
	}
}

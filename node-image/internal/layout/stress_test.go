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

func materializeFixture(t *testing.T, name string) (root string, refs []resolve.PackageRef) {
	t.Helper()
	fixture := filepath.Join("..", "..", "testdata", name)
	l, err := lock.ParseFile(filepath.Join(fixture, "pnpm-lock.yaml"))
	if err != nil {
		t.Fatal(err)
	}
	refs, err = resolve.Closure(l, ".", resolve.LinuxAmd64)
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
	root = t.TempDir()
	for _, name := range []string{"package.json", "index.js"} {
		b, err := os.ReadFile(filepath.Join(fixture, name))
		if err != nil {
			t.Fatal(err)
		}
		if err := os.WriteFile(filepath.Join(root, name), b, 0o644); err != nil {
			t.Fatal(err)
		}
	}
	if _, err := layout.Materialize(root, l, refs, tarballs, resolve.DirectDeps(l, ".")); err != nil {
		t.Fatal(err)
	}
	return root, refs
}

func TestNestedDepsLinksMSUnderDebug(t *testing.T) {
	root, _ := materializeFixture(t, "nested-deps")
	// Top-level should only have debug (direct), not ms.
	if _, err := os.Lstat(filepath.Join(root, "node_modules", "debug")); err != nil {
		t.Fatal(err)
	}
	if _, err := os.Lstat(filepath.Join(root, "node_modules", "ms")); err == nil {
		t.Fatal("ms should not be top-level linked (transitive only)")
	}
	// Nested link: debug's store node_modules/ms → ms package
	nested := filepath.Join(root, "node_modules", ".pnpm", "debug@4.3.4", "node_modules", "ms")
	if _, err := os.Lstat(nested); err != nil {
		t.Fatalf("nested ms link missing: %v", err)
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
	if got := string(out); got != "ok\n" && got != "ok\r\n" {
		t.Fatalf("unexpected output %q", got)
	}
}

func TestScopedDepVirtualStorePath(t *testing.T) {
	root, _ := materializeFixture(t, "scoped-dep")
	dir := filepath.Join(root, "node_modules", ".pnpm", "@sindresorhus+is@4.6.0")
	if st, err := os.Stat(dir); err != nil || !st.IsDir() {
		t.Fatalf("scoped virtual store dir missing: %v", err)
	}
	link := filepath.Join(root, "node_modules", "@sindresorhus", "is")
	if _, err := os.Lstat(link); err != nil {
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
	if got := string(out); got != "ok\n" && got != "ok\r\n" {
		t.Fatalf("unexpected output %q", got)
	}
}

func TestWithBinRootBin(t *testing.T) {
	root, _ := materializeFixture(t, "with-bin")
	bin := filepath.Join(root, "node_modules", ".bin", "rimraf")
	if _, err := os.Lstat(bin); err != nil {
		t.Fatalf("root .bin/rimraf missing: %v", err)
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
	if got := string(out); got != "ok\n" && got != "ok\r\n" {
		t.Fatalf("unexpected output %q", got)
	}
}

func TestOptionalPlatformFiltersArch(t *testing.T) {
	fixture := filepath.Join("..", "..", "testdata", "optional-platform")
	l, err := lock.ParseFile(filepath.Join(fixture, "pnpm-lock.yaml"))
	if err != nil {
		t.Fatal(err)
	}
	amd, err := resolve.Closure(l, ".", resolve.LinuxAmd64)
	if err != nil {
		t.Fatal(err)
	}
	arm, err := resolve.Closure(l, ".", resolve.LinuxArm64)
	if err != nil {
		t.Fatal(err)
	}
	has := func(refs []resolve.PackageRef, name string) bool {
		for _, r := range refs {
			if r.Name == name {
				return true
			}
		}
		return false
	}
	if !has(amd, "@esbuild/linux-x64") {
		t.Fatal("amd64 closure missing @esbuild/linux-x64")
	}
	if has(amd, "@esbuild/linux-arm64") {
		t.Fatal("amd64 closure should not include linux-arm64 optional")
	}
	if !has(arm, "@esbuild/linux-arm64") {
		t.Fatal("arm64 closure missing @esbuild/linux-arm64")
	}
	if has(arm, "@esbuild/linux-x64") {
		t.Fatal("arm64 closure should not include linux-x64 optional")
	}
}

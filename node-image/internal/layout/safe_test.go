package layout_test

import (
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/imjasonh/playground/node-image/internal/layout"
)

func TestValidNodeModulesName(t *testing.T) {
	ok := []string{"ms", "express", "@scope/pkg", "is-alias"}
	for _, n := range ok {
		if !layout.ValidNodeModulesNameForTest(n) {
			t.Fatalf("expected ok: %q", n)
		}
	}
	bad := []string{"", "..", "../evil", "a/b/c", "/abs", "foo/../bar", "@scope", "@scope/pkg/extra", "has space"}
	for _, n := range bad {
		if layout.ValidNodeModulesNameForTest(n) {
			t.Fatalf("expected reject: %q", n)
		}
	}
}

func TestSafeBinRel(t *testing.T) {
	if got, ok := layout.SafeBinRelForTest("./bin/cli.js"); !ok || got != "bin/cli.js" {
		t.Fatalf("got %q ok=%v", got, ok)
	}
	for _, bad := range []string{"../evil", "/etc/passwd", "..", ""} {
		if _, ok := layout.SafeBinRelForTest(bad); ok {
			t.Fatalf("expected reject: %q", bad)
		}
	}
}

func TestParseBinRejectsEscape(t *testing.T) {
	dir := t.TempDir()
	if err := os.WriteFile(filepath.Join(dir, "package.json"), []byte(`{
		"name": "evil",
		"version": "1.0.0",
		"bin": { "x": "../../../../etc/passwd" }
	}`), 0o644); err != nil {
		t.Fatal(err)
	}
	pj, err := layout.ReadPackageJSONForTest(dir)
	if err != nil {
		t.Fatal(err)
	}
	_, err = layout.ParseBinForTest(pj)
	if err == nil || !strings.Contains(err.Error(), "escapes") {
		t.Fatalf("expected escape error, got %v", err)
	}
}

func TestSpoolReverifyRejectsTamper(t *testing.T) {
	spool := t.TempDir()
	// Build a tiny fake tarball via extract path: use a real small package from cache if any,
	// otherwise skip.
	tgz := findAnyCachedTarball(t)
	if tgz == "" {
		t.Skip("no cached tarball")
	}
	key := "test-spool-key"
	pkgDir, err := layout.SpoolPackage(spool, key, tgz)
	if err != nil {
		t.Fatal(err)
	}
	// Tamper: rewrite meta with wrong hash
	meta := filepath.Join(pkgDir, ".node-image-spool.json")
	if err := os.WriteFile(meta, []byte(`{"integrityKey":"test-spool-key","tarballSHA512":"deadbeef","tarballSize":1}`+"\n"), 0o600); err != nil {
		t.Fatal(err)
	}
	// Hit should fail verification and re-extract (or succeed after rebuild).
	pkgDir2, err := layout.SpoolPackage(spool, key, tgz)
	if err != nil {
		t.Fatal(err)
	}
	b, err := os.ReadFile(filepath.Join(pkgDir2, ".node-image-spool.json"))
	if err != nil {
		t.Fatal(err)
	}
	if strings.Contains(string(b), "deadbeef") {
		t.Fatal("tampered meta was accepted")
	}
}

func findAnyCachedTarball(t *testing.T) string {
	t.Helper()
	home, err := os.UserHomeDir()
	if err != nil {
		return ""
	}
	dir := filepath.Join(home, ".cache", "node-image", "packages")
	entries, err := os.ReadDir(dir)
	if err != nil {
		return ""
	}
	for _, e := range entries {
		if strings.HasSuffix(e.Name(), ".tgz") {
			return filepath.Join(dir, e.Name())
		}
	}
	return ""
}

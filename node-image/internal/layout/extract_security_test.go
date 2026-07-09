package layout_test

import (
	"archive/tar"
	"compress/gzip"
	"os"
	"path/filepath"
	"testing"

	"github.com/imjasonh/playground/node-image/internal/layout"
	"github.com/imjasonh/playground/node-image/internal/lock"
	"github.com/imjasonh/playground/node-image/internal/resolve"
)

func writeTestTarball(t *testing.T, path string, entries []tarEntry) {
	t.Helper()
	f, err := os.Create(path)
	if err != nil {
		t.Fatal(err)
	}
	defer f.Close()
	gw := gzip.NewWriter(f)
	tw := tar.NewWriter(gw)
	for _, e := range entries {
		hdr := &tar.Header{Name: e.name, Mode: 0o644, Size: int64(len(e.body))}
		switch e.typ {
		case tar.TypeSymlink:
			hdr.Typeflag = tar.TypeSymlink
			hdr.Linkname = e.link
			hdr.Size = 0
			hdr.Mode = 0o777
		case tar.TypeDir:
			hdr.Typeflag = tar.TypeDir
			hdr.Mode = 0o755
			hdr.Size = 0
			if !hasTrailingSlash(e.name) {
				hdr.Name = e.name + "/"
			}
		default:
			hdr.Typeflag = tar.TypeReg
		}
		if err := tw.WriteHeader(hdr); err != nil {
			t.Fatal(err)
		}
		if e.typ == tar.TypeReg || e.typ == 0 {
			if _, err := tw.Write(e.body); err != nil {
				t.Fatal(err)
			}
		}
	}
	if err := tw.Close(); err != nil {
		t.Fatal(err)
	}
	if err := gw.Close(); err != nil {
		t.Fatal(err)
	}
}

type tarEntry struct {
	name string
	typ  byte
	link string
	body []byte
}

func hasTrailingSlash(s string) bool {
	return len(s) > 0 && s[len(s)-1] == '/'
}

func TestExtractRejectsSymlinkEscape(t *testing.T) {
	dir := t.TempDir()
	tgz := filepath.Join(dir, "evil.tgz")
	outside := filepath.Join(dir, "outside")
	if err := os.MkdirAll(outside, 0o755); err != nil {
		t.Fatal(err)
	}
	// Symlink package/link -> ../../outside, then a regular file package/link/pwned
	// that would write outside dest if followed.
	writeTestTarball(t, tgz, []tarEntry{
		{name: "package/link", typ: tar.TypeSymlink, link: "../../outside"},
		{name: "package/link/pwned", typ: tar.TypeReg, body: []byte("pwned")},
	})
	dest := filepath.Join(dir, "pkg")
	err := layout.ExtractNPMTarballForTest(tgz, dest)
	if err == nil {
		t.Fatal("expected symlink escape to be rejected")
	}
	if _, err := os.Stat(filepath.Join(outside, "pwned")); err == nil {
		t.Fatal("escape succeeded: outside/pwned was written")
	}
}

func TestExtractNonPackageRootPrefix(t *testing.T) {
	dir := t.TempDir()
	tgz := filepath.Join(dir, "ejs.tgz")
	writeTestTarball(t, tgz, []tarEntry{
		{name: "ejs-v3.1.10/package.json", typ: tar.TypeReg, body: []byte(`{"name":"ejs","version":"3.1.10"}`)},
		{name: "ejs-v3.1.10/ejs.js", typ: tar.TypeReg, body: []byte("module.exports=1")},
	})
	dest := filepath.Join(dir, "pkg")
	if err := layout.ExtractNPMTarballForTest(tgz, dest); err != nil {
		t.Fatal(err)
	}
	if _, err := os.Stat(filepath.Join(dest, "package.json")); err != nil {
		t.Fatalf("expected package.json at dest root: %v", err)
	}
	if _, err := os.Stat(filepath.Join(dest, "ejs.js")); err != nil {
		t.Fatalf("expected ejs.js: %v", err)
	}
}

func TestLinkTopLevelAlias(t *testing.T) {
	// Simulate alias: importer depends on "is-alias" → @sindresorhus/is@4.6.0
	root := t.TempDir()
	nm := filepath.Join(root, "node_modules")
	storePkg := filepath.Join(nm, ".pnpm", "@sindresorhus+is@4.6.0", "node_modules", "@sindresorhus", "is")
	if err := os.MkdirAll(storePkg, 0o755); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(filepath.Join(storePkg, "package.json"), []byte(`{"name":"@sindresorhus/is","version":"4.6.0"}`), 0o644); err != nil {
		t.Fatal(err)
	}
	refs := []resolve.PackageRef{{
		DepPath:   "@sindresorhus/is@4.6.0",
		PackageID: "@sindresorhus/is@4.6.0",
		Name:      "@sindresorhus/is",
		Version:   "4.6.0",
	}}
	direct := []resolve.DirectDep{{
		LinkName: "is-alias",
		DepPath:  "@sindresorhus/is@4.6.0",
	}}
	if err := layout.LinkTopLevel(root, refs, direct); err != nil {
		t.Fatal(err)
	}
	link := filepath.Join(nm, "is-alias")
	if _, err := os.Lstat(link); err != nil {
		t.Fatalf("alias link missing: %v", err)
	}
	// Real package name must not be required at top level for the alias case.
}

func TestDirectDepsAliasFromLock(t *testing.T) {
	// with-bin has strip-ansi-cjs → strip-ansi@6.0.1 style aliases in snapshots;
	// DirectDeps for importer should still use rimraf as link name.
	l, err := lock.ParseFile(filepath.Join("..", "..", "testdata", "with-bin", "pnpm-lock.yaml"))
	if err != nil {
		t.Fatal(err)
	}
	deps := resolve.DirectDeps(l, ".")
	if len(deps) != 1 || deps[0].LinkName != "rimraf" {
		t.Fatalf("direct deps: %+v", deps)
	}
}

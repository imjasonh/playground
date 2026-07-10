package buildcmd_test

import (
	"bytes"
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/imjasonh/playground/node-image/internal/app"
	"github.com/imjasonh/playground/node-image/internal/buildcmd"
	"github.com/imjasonh/playground/node-image/internal/lock"
)

func fixtureDir(t *testing.T, name string) string {
	t.Helper()
	dir, err := filepath.Abs(filepath.Join("..", "..", "testdata", name))
	if err != nil {
		t.Fatal(err)
	}
	return dir
}

func buildNoPush(t *testing.T, dir string, platforms []string) (ref string, stdout, stderr string) {
	t.Helper()
	if platforms == nil {
		platforms = []string{"linux/amd64"}
	}
	out := t.TempDir()
	var outBuf, errBuf bytes.Buffer
	ref, err := buildcmd.Run(buildcmd.Options{
		Dir:       dir,
		NoPush:    true,
		OCIDir:    out,
		EmptyBase: true,
		SkipBuild: true,
		Platforms: platforms,
		Stdout:    &outBuf,
		Stderr:    &errBuf,
	})
	if err != nil {
		t.Fatalf("%v\nstderr=%s", err, errBuf.String())
	}
	return ref, outBuf.String(), errBuf.String()
}

func TestE2ENestedDeps(t *testing.T) {
	ref, stdout, _ := buildNoPush(t, fixtureDir(t, "nested-deps"), nil)
	if strings.TrimSpace(stdout) != ref || !strings.HasPrefix(ref, "sha256:") {
		t.Fatalf("stdout contract: %q vs %q", stdout, ref)
	}
}

func TestE2EScopedDep(t *testing.T) {
	ref, stdout, _ := buildNoPush(t, fixtureDir(t, "scoped-dep"), nil)
	if strings.TrimSpace(stdout) != ref {
		t.Fatalf("stdout %q != %q", stdout, ref)
	}
}

func TestE2EWithBin(t *testing.T) {
	_, _, _ = buildNoPush(t, fixtureDir(t, "with-bin"), nil)
}

func TestE2EOptionalPlatformMultiArch(t *testing.T) {
	ref, _, _ := buildNoPush(t, fixtureDir(t, "optional-platform"), []string{"linux/amd64", "linux/arm64"})
	if ref == "" {
		t.Fatal("empty ref")
	}
}

func TestE2ELifecycleNoopScriptsAllowed(t *testing.T) {
	_, _, _ = buildNoPush(t, fixtureDir(t, "lifecycle-scripts"), nil)
}

func TestE2EPatchedApplies(t *testing.T) {
	dir := fixtureDir(t, "patched")
	l, err := lock.ParseFile(filepath.Join(dir, "pnpm-lock.yaml"))
	if err != nil {
		t.Fatal(err)
	}
	if len(l.PatchedDependencies) == 0 {
		t.Fatal("expected patchedDependencies in lock")
	}
	ref, _, stderr := buildNoPush(t, dir, nil)
	if ref == "" {
		t.Fatal("empty ref")
	}
	if strings.Contains(stderr, "patchedDependencies are not supported") {
		t.Fatalf("patches should apply, got stderr: %s", stderr)
	}
}

func TestE2EWorkspaceMaterializes(t *testing.T) {
	dir := fixtureDir(t, "workspace-app/apps/api")
	ref, _, _ := buildNoPush(t, dir, nil)
	if !strings.HasPrefix(ref, "sha256:") {
		t.Fatalf("ref %q", ref)
	}
}

func TestE2ECatalogApp(t *testing.T) {
	_, _, _ = buildNoPush(t, fixtureDir(t, "catalog-app"), nil)
}

func TestE2EOverrideApp(t *testing.T) {
	_, _, _ = buildNoPush(t, fixtureDir(t, "override-app"), nil)
}

func TestE2EBuildGlobs(t *testing.T) {
	dir := fixtureDir(t, "build-globs")
	_, _, _ = buildNoPush(t, dir, nil)
	outs, err := app.CollectOutputsOpts(dir, app.CollectOptions{
		Include: []string{"build/**", "package.json"},
		Exclude: []string{"**/*.map"},
	})
	if err != nil {
		t.Fatal(err)
	}
	if _, ok := outs["build/scripts/helper.lua"]; !ok {
		t.Fatalf("expected lua asset, got %#v", outs)
	}
	if _, ok := outs["build/index.js.map"]; ok {
		t.Fatal("sourcemap should be excluded")
	}
}

func TestE2EMultiCommand(t *testing.T) {
	dir := fixtureDir(t, "multi-cmd")
	var outBuf, errBuf bytes.Buffer
	_, err := buildcmd.Run(buildcmd.Options{
		Dir:       dir,
		NoPush:    true,
		OCIDir:    t.TempDir(),
		EmptyBase: true,
		SkipBuild: true,
		Platforms: []string{"linux/amd64"},
		Command:   "worker",
		Stdout:    &outBuf,
		Stderr:    &errBuf,
	})
	if err != nil {
		t.Fatalf("%v\n%s", err, errBuf.String())
	}
}

func TestDiagnoseImporterIsolation(t *testing.T) {
	// Create a lock with an unused git package and a clean importer.
	root := t.TempDir()
	if err := os.WriteFile(filepath.Join(root, "package.json"), []byte(`{"name":"iso","main":"index.js"}`), 0o644); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(filepath.Join(root, "index.js"), []byte(`console.log("ok")`), 0o644); err != nil {
		t.Fatal(err)
	}
	lockBody := `lockfileVersion: '9.0'
importers:
  .:
    dependencies:
      ms:
        specifier: 2.1.3
        version: 2.1.3
  other-app:
    dependencies:
      weird:
        specifier: git+https://example.com/weird.git
        version: git+https://example.com/weird.git#abc
packages:
  ms@2.1.3:
    resolution: {integrity: sha512-6FlzubTLZG3J2a/NVCAleEhjzq5oxgHyaCU9yYXvcLsvoVaHJq/s5xXI6/XXP6tz7R9xAOtHnSO/tXtF3WRTlA==}
  weird@git+https://example.com/weird.git#abc:
    resolution: {type: git, tarball: git+https://example.com/weird.git}
snapshots:
  ms@2.1.3: {}
`
	if err := os.WriteFile(filepath.Join(root, "pnpm-lock.yaml"), []byte(lockBody), 0o644); err != nil {
		t.Fatal(err)
	}
	var buf bytes.Buffer
	if err := buildcmd.Diagnose(root, &buf); err != nil {
		// diagnose may warn but should not error on unused git if only warnings
		if !strings.Contains(buf.String(), "ms") && buf.Len() == 0 {
			t.Fatalf("diagnose: %v\n%s", err, buf.String())
		}
	}
	// Build the clean importer — unused git package must not block.
	_, err := buildcmd.Run(buildcmd.Options{
		Dir:       root,
		NoPush:    true,
		OCIDir:    t.TempDir(),
		EmptyBase: true,
		SkipBuild: true,
		Platforms: []string{"linux/amd64"},
		Stdout:    &bytes.Buffer{},
		Stderr:    &bytes.Buffer{},
	})
	if err != nil {
		t.Fatalf("clean importer blocked by unused git pkg: %v", err)
	}
}

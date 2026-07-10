package lock_test

import (
	"path/filepath"
	"strings"
	"testing"

	"github.com/imjasonh/playground/node-image/internal/lock"
)

func TestDiagnosePatchedIsWarning(t *testing.T) {
	path := filepath.Join("..", "..", "testdata", "patched", "pnpm-lock.yaml")
	l, err := lock.ParseFile(path)
	if err != nil {
		t.Fatal(err)
	}
	r := l.Diagnose(lock.DiagnoseOptions{ImporterKey: "."})
	if r.HasErrors() {
		t.Fatalf("patched should be warning, got errors: %s", r)
	}
	found := false
	for _, f := range r.Findings {
		if f.Code == "patched-dependencies" {
			found = true
		}
	}
	if !found {
		t.Fatalf("expected patched-dependencies finding: %s", r)
	}
}

func TestDiagnoseUnusedGitNotErrorForCleanImporter(t *testing.T) {
	body := []byte(`lockfileVersion: '9.0'
importers:
  .:
    dependencies:
      ms:
        specifier: 2.1.3
        version: 2.1.3
  other:
    dependencies:
      weird:
        specifier: git
        version: weird@1.0.0
packages:
  ms@2.1.3:
    resolution: {integrity: sha512-6FlzubTLZG3J2a/NVCAleEhjzq5oxgHyaCU9yYXvcLsvoVaHJq/s5xXI6/XXP6tz7R9xAOtHnSO/tXtF3WRTlA==}
  weird@1.0.0:
    resolution: {type: git, tarball: 'git+https://example.com/x.git', integrity: sha512-aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa}
snapshots:
  ms@2.1.3: {}
`)
	l, err := lock.Parse(body)
	if err != nil {
		t.Fatal(err)
	}
	r := l.Diagnose(lock.DiagnoseOptions{ImporterKey: "."})
	for _, f := range r.Findings {
		if f.Code == "git-dependency" && strings.Contains(f.Message, "weird") {
			t.Fatalf("unused git package should not appear for importer .: %s", r)
		}
	}
}

func TestPatchedLookup(t *testing.T) {
	path := filepath.Join("..", "..", "testdata", "patched", "pnpm-lock.yaml")
	l, err := lock.ParseFile(path)
	if err != nil {
		t.Fatal(err)
	}
	e, ok := l.PatchedLookup("ms@2.1.3")
	if !ok || e.Path != "patches/ms.patch" || e.Hash == "" {
		t.Fatalf("lookup: %+v ok=%v", e, ok)
	}
}

package layout_test

import (
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/imjasonh/playground/node-image/internal/layout"
	"github.com/imjasonh/playground/node-image/internal/resolve"
)

func TestCheckScriptsAllowsTelemetryPostinstall(t *testing.T) {
	dir := t.TempDir()
	if err := os.WriteFile(filepath.Join(dir, "package.json"), []byte(`{
		"name": "@scarf/scarf",
		"version": "1.4.0",
		"scripts": { "postinstall": "node ./report.js" }
	}`), 0o644); err != nil {
		t.Fatal(err)
	}
	pj, err := layout.ReadPackageJSONForTest(dir)
	if err != nil {
		t.Fatal(err)
	}
	ref := resolve.PackageRef{PackageID: "@scarf/scarf@1.4.0", Name: "@scarf/scarf"}
	if err := layout.CheckScriptsInDir(ref, dir, pj); err != nil {
		t.Fatalf("telemetry postinstall should be allowed: %v", err)
	}
}

func TestCheckScriptsAllowsNonStringScriptEntries(t *testing.T) {
	dir := t.TempDir()
	// alce@1.2.0 stores an object under scripts.blanket — must not fail JSON parse.
	if err := os.WriteFile(filepath.Join(dir, "package.json"), []byte(`{
		"name": "alce",
		"version": "1.2.0",
		"scripts": {
			"blanket": {"pattern": "x"},
			"test": "mocha"
		}
	}`), 0o644); err != nil {
		t.Fatal(err)
	}
	pj, err := layout.ReadPackageJSONForTest(dir)
	if err != nil {
		t.Fatal(err)
	}
	ref := resolve.PackageRef{PackageID: "alce@1.2.0", Name: "alce"}
	if err := layout.CheckScriptsInDir(ref, dir, pj); err != nil {
		t.Fatalf("non-string scripts should be ignored: %v", err)
	}
}

func TestCheckScriptsRejectsBindingGyp(t *testing.T) {
	dir := t.TempDir()
	if err := os.WriteFile(filepath.Join(dir, "package.json"), []byte(`{
		"name": "native-addon",
		"version": "1.0.0",
		"scripts": { "install": "node-gyp rebuild" }
	}`), 0o644); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(filepath.Join(dir, "binding.gyp"), []byte("{}"), 0o644); err != nil {
		t.Fatal(err)
	}
	pj, err := layout.ReadPackageJSONForTest(dir)
	if err != nil {
		t.Fatal(err)
	}
	ref := resolve.PackageRef{PackageID: "native-addon@1.0.0", Name: "native-addon"}
	err = layout.CheckScriptsInDir(ref, dir, pj)
	if err == nil {
		t.Fatal("expected native build rejection")
	}
	if !strings.Contains(err.Error(), "native build") {
		t.Fatalf("got %v", err)
	}
}

package config

import (
	"os"
	"path/filepath"
	"testing"
)

func TestLoadDefaults(t *testing.T) {
	dir := t.TempDir()
	eff, err := Load(dir, nil)
	if err != nil {
		t.Fatal(err)
	}
	if eff.Main != "." {
		t.Fatalf("main: got %q", eff.Main)
	}
	if eff.CGOEnabled != "0" {
		t.Fatalf("cgo: got %q", eff.CGOEnabled)
	}
	if !eff.Trimpath {
		t.Fatal("expected trimpath")
	}
	if len(eff.Ldflags) != 2 || eff.Ldflags[0] != "-s" {
		t.Fatalf("ldflags: %#v", eff.Ldflags)
	}
}

func TestLoadKoYAML(t *testing.T) {
	dir := t.TempDir()
	yaml := `
defaultBaseImage: cgr.dev/chainguard/static
defaultLdflags:
  - -X main.version=dev
builds:
  - id: app
    main: ./cmd/app
    flags:
      - -tags
      - netgo
    env:
      - FOO=bar
  - id: other
    main: ./cmd/other
`
	if err := os.WriteFile(filepath.Join(dir, ".ko.yaml"), []byte(yaml), 0o644); err != nil {
		t.Fatal(err)
	}
	eff, err := Load(dir, nil)
	if err != nil {
		t.Fatal(err)
	}
	if eff.Main != "./cmd/app" {
		t.Fatalf("main: got %q", eff.Main)
	}
	if eff.DefaultBaseImage != "cgr.dev/chainguard/static" {
		t.Fatalf("base: got %q", eff.DefaultBaseImage)
	}
	if got := join(eff.Flags); got != "-tags netgo" {
		t.Fatalf("flags: %q", got)
	}
	if got := join(eff.Ldflags); got != "-X main.version=dev" {
		t.Fatalf("ldflags: %q", got)
	}
}

func TestPlatformOverrides(t *testing.T) {
	dir := t.TempDir()
	eff, err := Load(dir, map[string]string{
		"BP_GO_TARGETS":  "./cmd/server ./cmd/worker",
		"CGO_ENABLED":    "1",
		"BP_GO_TRIMPATH": "false",
	})
	if err != nil {
		t.Fatal(err)
	}
	if eff.Main != "./cmd/server" {
		t.Fatalf("main: got %q", eff.Main)
	}
	if eff.CGOEnabled != "1" {
		t.Fatalf("cgo: got %q", eff.CGOEnabled)
	}
	if eff.Trimpath {
		t.Fatal("trimpath should be off")
	}
}

func TestSelectBuildByID(t *testing.T) {
	dir := t.TempDir()
	yaml := `
builds:
  - id: a
    main: ./a
  - id: b
    main: ./b
`
	if err := os.WriteFile(filepath.Join(dir, ".ko.yaml"), []byte(yaml), 0o644); err != nil {
		t.Fatal(err)
	}
	t.Setenv("KO_BUILD_ID", "b")
	eff, err := Load(dir, nil)
	if err != nil {
		t.Fatal(err)
	}
	if eff.Main != "./b" {
		t.Fatalf("main: got %q", eff.Main)
	}
}

func join(ss []string) string {
	out := ""
	for i, s := range ss {
		if i > 0 {
			out += " "
		}
		out += s
	}
	return out
}

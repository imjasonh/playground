package resolve_test

import (
	"strings"
	"testing"

	"github.com/imjasonh/playground/node-image/internal/lock"
	"github.com/imjasonh/playground/node-image/internal/resolve"
)

func TestOptionalUpgradedToRequiredReprocesses(t *testing.T) {
	// Package win-only is first reached as optional (and would be skipped on linux),
	// then also required. Must fail as required, not silently skip.
	yaml := []byte(`
lockfileVersion: '9.0'
importers:
  .:
    dependencies:
      root:
        specifier: 1.0.0
        version: 1.0.0
    optionalDependencies:
      win-only:
        specifier: 1.0.0
        version: 1.0.0
packages:
  root@1.0.0:
    resolution: {integrity: sha512-AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA==}
  win-only@1.0.0:
    resolution: {integrity: sha512-BBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBB==}
    os: [win32]
snapshots:
  root@1.0.0:
    dependencies:
      win-only: 1.0.0
  win-only@1.0.0: {}
`)
	l, err := lock.Parse(yaml)
	if err != nil {
		t.Fatal(err)
	}
	_, err = resolve.Closure(l, ".", resolve.LinuxAmd64)
	if err == nil {
		t.Fatal("expected required platform mismatch after optional→required upgrade")
	}
	if !strings.Contains(err.Error(), "win-only") {
		t.Fatalf("unexpected error: %v", err)
	}
}

func TestOptionalStaysOptionalWhenOnlyOptional(t *testing.T) {
	yaml := []byte(`
lockfileVersion: '9.0'
importers:
  .:
    optionalDependencies:
      win-only:
        specifier: 1.0.0
        version: 1.0.0
packages:
  win-only@1.0.0:
    resolution: {integrity: sha512-BBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBB==}
    os: [win32]
snapshots:
  win-only@1.0.0: {}
`)
	l, err := lock.Parse(yaml)
	if err != nil {
		t.Fatal(err)
	}
	refs, err := resolve.Closure(l, ".", resolve.LinuxAmd64)
	if err != nil {
		t.Fatal(err)
	}
	if len(refs) != 0 {
		t.Fatalf("expected win-only to be skipped as optional, got %+v", refs)
	}
}

func TestDirectDepsAliasLinkName(t *testing.T) {
	yaml := []byte(`
lockfileVersion: '9.0'
importers:
  .:
    dependencies:
      is-alias:
        specifier: npm:@sindresorhus/is@4.6.0
        version: '@sindresorhus/is@4.6.0'
packages:
  '@sindresorhus/is@4.6.0':
    resolution: {integrity: sha512-AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA==}
snapshots:
  '@sindresorhus/is@4.6.0': {}
`)
	l, err := lock.Parse(yaml)
	if err != nil {
		t.Fatal(err)
	}
	deps := resolve.DirectDeps(l, ".")
	if len(deps) != 1 {
		t.Fatalf("%+v", deps)
	}
	if deps[0].LinkName != "is-alias" {
		t.Fatalf("link name: %q", deps[0].LinkName)
	}
	if deps[0].DepPath != "@sindresorhus/is@4.6.0" {
		t.Fatalf("dep path: %q", deps[0].DepPath)
	}
	refs, err := resolve.Closure(l, ".", resolve.LinuxAmd64)
	if err != nil {
		t.Fatal(err)
	}
	if len(refs) != 1 || refs[0].Name != "@sindresorhus/is" {
		t.Fatalf("refs: %+v", refs)
	}
}

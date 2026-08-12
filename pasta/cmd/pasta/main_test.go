package main

import (
	"os"
	"path/filepath"
	"reflect"
	"testing"
	"time"

	"github.com/imjasonh/pasta/internal/engine"
	"github.com/imjasonh/pasta/internal/loader"
)

func TestWalkSources_skipsVendorTrees(t *testing.T) {
	dir := t.TempDir()
	write := func(rel, body string) {
		t.Helper()
		p := filepath.Join(dir, rel)
		if err := os.MkdirAll(filepath.Dir(p), 0o755); err != nil {
			t.Fatal(err)
		}
		if err := os.WriteFile(p, []byte(body), 0o644); err != nil {
			t.Fatal(err)
		}
	}
	write("main.go", "package main\n")
	write("vendor/github.com/x/y/y.go", "package y\n")
	write("node_modules/leftpad/index.js", "module.exports = 1\n")
	write(".venv/lib/site.py", "x = 1\n")

	got, _, err := walkSources(dir, parseSkipDirs("", nil), 0)
	if err != nil {
		t.Fatal(err)
	}
	if len(got) != 1 || filepath.Base(got[0]) != "main.go" {
		t.Fatalf("got %v, want only main.go (vendored trees skipped)", got)
	}
}

func TestWalkSources_skipsSymlink(t *testing.T) {
	dir := t.TempDir()
	real := filepath.Join(dir, "real.go")
	if err := os.WriteFile(real, []byte("package x\n"), 0o644); err != nil {
		t.Fatal(err)
	}
	link := filepath.Join(dir, "link.go")
	if err := os.Symlink(real, link); err != nil {
		t.Skipf("symlink not supported: %v", err)
	}
	got, skipped, err := walkSources(dir, map[string]bool{}, 0)
	if err != nil {
		t.Fatal(err)
	}
	if len(skipped) != 0 {
		t.Fatalf("unexpected skipped: %v", skipped)
	}
	if len(got) != 1 || filepath.Base(got[0]) != "real.go" {
		t.Fatalf("got %v, want only real.go", got)
	}
}

func TestParseFailOn(t *testing.T) {
	cases := []struct {
		in      string
		want    failOnLevel
		wantErr bool
	}{
		{in: "none", want: failOnNone},
		{in: "warning", want: failOnWarning},
		{in: "error", want: failOnError},
		{in: "bogus", wantErr: true},
	}
	for _, tc := range cases {
		got, err := parseFailOn(tc.in)
		if tc.wantErr {
			if err == nil {
				t.Errorf("%q: expected error", tc.in)
			}
			continue
		}
		if err != nil || got != tc.want {
			t.Errorf("%q: got (%v, %v), want (%v, nil)", tc.in, got, err, tc.want)
		}
	}
	if !severityAtLeast("error", failOnWarning) {
		t.Error("error should fail on warning threshold")
	}
	if severityAtLeast("hint", failOnWarning) {
		t.Error("hint should not fail on warning threshold")
	}
}

func TestWriteFixedFile_refusesSymlink(t *testing.T) {
	dir := t.TempDir()
	real := filepath.Join(dir, "real.go")
	if err := os.WriteFile(real, []byte("package x\n"), 0o644); err != nil {
		t.Fatal(err)
	}
	link := filepath.Join(dir, "link.go")
	if err := os.Symlink(real, link); err != nil {
		t.Skipf("symlink not supported: %v", err)
	}
	if err := writeFixedFile(link, []byte("package y\n")); err == nil {
		t.Fatal("expected refusal to write through symlink")
	}
	got, err := os.ReadFile(real)
	if err != nil {
		t.Fatal(err)
	}
	if string(got) != "package x\n" {
		t.Fatalf("symlink target was modified: %q", got)
	}
}

func TestWalkSources_filtersByMaxFileSize(t *testing.T) {
	dir := t.TempDir()
	small := []byte("package x\n")
	big := make([]byte, 5_000_000) // 5 MB
	for i := range big {
		big[i] = ' '
	}
	for name, data := range map[string][]byte{
		"small.go": small,
		"big.go":   big,
		"tiny.go":  small,
	} {
		if err := os.WriteFile(filepath.Join(dir, name), data, 0o644); err != nil {
			t.Fatal(err)
		}
	}

	got, skipped, err := walkSources(dir, map[string]bool{}, 1<<20)
	if err != nil {
		t.Fatal(err)
	}
	// Strip the temp-dir prefix so the assertion is portable.
	rel := func(paths []string) []string {
		out := make([]string, len(paths))
		for i, p := range paths {
			out[i] = filepath.Base(p)
		}
		return out
	}
	wantKept := []string{"small.go", "tiny.go"}
	wantSkipped := []string{"big.go"}
	if got := rel(got); !sortedEqual(got, wantKept) {
		t.Errorf("kept: got %v, want %v", got, wantKept)
	}
	if got := rel(skipped); !sortedEqual(got, wantSkipped) {
		t.Errorf("skipped: got %v, want %v", got, wantSkipped)
	}
}

func TestWalkSources_zeroMaxDisablesCap(t *testing.T) {
	dir := t.TempDir()
	big := make([]byte, 5_000_000)
	if err := os.WriteFile(filepath.Join(dir, "huge.go"), big, 0o644); err != nil {
		t.Fatal(err)
	}
	got, skipped, err := walkSources(dir, map[string]bool{}, 0)
	if err != nil {
		t.Fatal(err)
	}
	if len(got) != 1 || filepath.Base(got[0]) != "huge.go" {
		t.Errorf("expected huge.go to be kept with maxFileSize=0; got %v", got)
	}
	if len(skipped) != 0 {
		t.Errorf("expected no skipped files; got %v", skipped)
	}
}

func TestResolveMaxFileSize(t *testing.T) {
	cases := []struct {
		name string
		cfg  *loader.Config
		want int64
	}{
		{name: "nil config", cfg: nil, want: defaultMaxFileSize},
		{name: "unset field", cfg: &loader.Config{}, want: defaultMaxFileSize},
		{name: "explicit zero", cfg: &loader.Config{MaxFileSize: int64Ptr(0)}, want: 0},
		{name: "explicit value", cfg: &loader.Config{MaxFileSize: int64Ptr(42)}, want: 42},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			if got := resolveMaxFileSize(tc.cfg); got != tc.want {
				t.Errorf("got %d, want %d", got, tc.want)
			}
		})
	}
}

func TestResolveParseTimeout(t *testing.T) {
	cases := []struct {
		name string
		flag time.Duration
		cfg  *loader.Config
		want time.Duration
	}{
		{name: "default", flag: -1, cfg: nil, want: engine.DefaultParseTimeout},
		{name: "flag wins", flag: 500 * time.Millisecond, cfg: &loader.Config{ParseTimeout: int64Ptr(9999)}, want: 500 * time.Millisecond},
		{name: "flag zero disables", flag: 0, cfg: nil, want: 0},
		{name: "config ms", flag: -1, cfg: &loader.Config{ParseTimeout: int64Ptr(1500)}, want: 1500 * time.Millisecond},
		{name: "config zero disables", flag: -1, cfg: &loader.Config{ParseTimeout: int64Ptr(0)}, want: 0},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			if got := resolveParseTimeout(tc.flag, tc.cfg); got != tc.want {
				t.Errorf("got %v, want %v", got, tc.want)
			}
		})
	}
}

// Local helpers — defined here rather than in main.go because they're
// test-only.

func int64Ptr(n int64) *int64 { return &n }

func sortedEqual(a, b []string) bool {
	if len(a) != len(b) {
		return false
	}
	ac := append([]string(nil), a...)
	bc := append([]string(nil), b...)
	sortStrings(ac)
	sortStrings(bc)
	return reflect.DeepEqual(ac, bc)
}

func sortStrings(s []string) {
	for i := 1; i < len(s); i++ {
		for j := i; j > 0 && s[j-1] > s[j]; j-- {
			s[j-1], s[j] = s[j], s[j-1]
		}
	}
}

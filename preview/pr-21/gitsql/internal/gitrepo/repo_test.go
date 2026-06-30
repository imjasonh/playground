package gitrepo

import (
	"os"
	"path/filepath"
	"testing"
)

func TestClassifySpec(t *testing.T) {
	// A real directory on disk is always local.
	dir := t.TempDir()

	cases := []struct {
		spec    string
		wantURL string
		wantKey string
		wantLoc bool
	}{
		{spec: "owner/repo", wantURL: "https://github.com/owner/repo", wantKey: "github.com/owner/repo"},
		{spec: "https://github.com/foo/bar.git", wantURL: "https://github.com/foo/bar.git", wantKey: "github.com/foo/bar"},
		{spec: "https://example.com/a/b/c", wantURL: "https://example.com/a/b/c", wantKey: "example.com/a/b/c"},
		{spec: "git@github.com:foo/bar.git", wantURL: "git@github.com:foo/bar.git", wantKey: "github.com/foo/bar"},
		{spec: dir, wantLoc: true},
		{spec: "./nope-not-a-repo", wantLoc: true},
	}

	for _, tc := range cases {
		t.Run(tc.spec, func(t *testing.T) {
			url, key, local, err := classifySpec(tc.spec)
			if err != nil {
				t.Fatalf("classifySpec(%q): %v", tc.spec, err)
			}
			if local != tc.wantLoc {
				t.Errorf("local = %v, want %v", local, tc.wantLoc)
			}
			if !tc.wantLoc {
				if url != tc.wantURL {
					t.Errorf("url = %q, want %q", url, tc.wantURL)
				}
				if key != tc.wantKey {
					t.Errorf("key = %q, want %q", key, tc.wantKey)
				}
			}
			if tc.wantLoc && !filepath.IsAbs(key) {
				t.Errorf("local key %q is not absolute", key)
			}
		})
	}
}

func TestClassifySpecEmpty(t *testing.T) {
	if _, _, _, err := classifySpec(""); err != nil {
		// classifySpec itself doesn't reject empty; Resolve does. Just ensure no panic.
		_ = err
	}
}

func TestResolveEmpty(t *testing.T) {
	m, err := NewManager(Options{CacheDir: t.TempDir()})
	if err != nil {
		t.Fatal(err)
	}
	if _, err := m.Resolve("   "); err == nil {
		t.Errorf("expected error resolving empty spec")
	}
}

func TestRemoteKeySanitizes(t *testing.T) {
	got := remoteKey("https://example.com/weird path/repo.git")
	if got == "" || filepath.IsAbs(got) {
		t.Errorf("unexpected key %q", got)
	}
	// No spaces should survive sanitization.
	for _, r := range got {
		if r == ' ' {
			t.Errorf("key %q contains a space", got)
		}
	}
}

func TestManagerCacheDirDefault(t *testing.T) {
	t.Setenv("XDG_CACHE_HOME", t.TempDir())
	m, err := NewManager(Options{})
	if err != nil {
		t.Fatal(err)
	}
	if m.CacheDir() == "" {
		t.Errorf("expected a non-empty default cache dir")
	}
	if _, err := os.Stat(filepath.Dir(m.CacheDir())); err != nil {
		t.Errorf("cache parent should exist: %v", err)
	}
}

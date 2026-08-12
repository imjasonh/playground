package toolchain

import (
	"os"
	"path/filepath"
	"testing"
)

func TestResolveVersion(t *testing.T) {
	cases := []struct {
		h    GoModHints
		want string
	}{
		{GoModHints{Toolchain: "go1.25.1"}, "1.25.1"},
		{GoModHints{Go: "1.24"}, "1.24.0"},
		{GoModHints{Go: "1.25.0", Toolchain: "go1.25.2"}, "1.25.2"},
		{GoModHints{}, "1.25.0"},
	}
	for _, tc := range cases {
		got := ResolveVersion(tc.h, "1.25.0")
		if got != tc.want {
			t.Fatalf("hints=%+v: got %q want %q", tc.h, got, tc.want)
		}
	}
}

func TestParseGoMod(t *testing.T) {
	dir := t.TempDir()
	content := "module m\n\ngo 1.25\n\ntoolchain go1.25.0\n"
	if err := os.WriteFile(filepath.Join(dir, "go.mod"), []byte(content), 0o644); err != nil {
		t.Fatal(err)
	}
	h, err := ParseGoMod(dir)
	if err != nil {
		t.Fatal(err)
	}
	if h.Go != "1.25" || h.Toolchain != "go1.25.0" {
		t.Fatalf("got %+v", h)
	}
}

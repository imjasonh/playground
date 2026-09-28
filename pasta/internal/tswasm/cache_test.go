package tswasm

import (
	"errors"
	"io/fs"
	"os"
	"path/filepath"
	"testing"
)

// tinyModule is a valid WASM module with one function that returns 42.
// It compiles in well under a millisecond.
var tinyModule = []byte{
	0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00, // magic and version
	0x01, 0x05, 0x01, 0x60, 0x00, 0x01, 0x7f, // type section: func() i32
	0x03, 0x02, 0x01, 0x00, // function section: one function of type 0
	0x0a, 0x06, 0x01, 0x04, 0x00, 0x41, 0x2a, 0x0b, // code section: i32.const 42
}

func TestLoadRuntime_compilationCache(t *testing.T) {
	dir := filepath.Join(t.TempDir(), "wazero")
	load := func() {
		t.Helper()
		r, err := loadRuntime(t.Context(), tinyModule, dir)
		if err != nil {
			t.Fatal(err)
		}
		if err := r.wz.Close(t.Context()); err != nil {
			t.Fatal(err)
		}
	}

	load()
	load()
	var entries []string
	if err := filepath.WalkDir(dir, func(p string, d fs.DirEntry, err error) error {
		if err == nil && d.Type().IsRegular() {
			entries = append(entries, p)
		}
		return err
	}); err != nil {
		t.Fatal(err)
	}
	if len(entries) == 0 {
		t.Fatal("no compiled code in the cache directory")
	}

	for _, p := range entries {
		if err := os.WriteFile(p, []byte("damaged"), 0o644); err != nil {
			t.Fatal(err)
		}
	}
	load()
	if _, err := os.Stat(dir); !errors.Is(err, fs.ErrNotExist) {
		t.Errorf("damaged cache directory is still there: %v", err)
	}
}

func TestLoadRuntime_unusableCacheDir(t *testing.T) {
	file := filepath.Join(t.TempDir(), "file")
	if err := os.WriteFile(file, nil, 0o644); err != nil {
		t.Fatal(err)
	}
	r, err := loadRuntime(t.Context(), tinyModule, filepath.Join(file, "wazero"))
	if err != nil {
		t.Fatal(err)
	}
	if err := r.wz.Close(t.Context()); err != nil {
		t.Fatal(err)
	}
}

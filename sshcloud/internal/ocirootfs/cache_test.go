package ocirootfs

import (
	"bytes"
	"os"
	"path/filepath"
	"strings"
	"testing"
	"time"
)

func TestRootfsCacheEvictsLeastRecentlyUsedDigestPair(t *testing.T) {
	t.Parallel()
	dir := t.TempDir()
	oldBase := strings.Repeat("a", 64) + "-v2-512m"
	newBase := strings.Repeat("b", 64) + "-v2-512m"
	writeCachePair := func(base string, used time.Time) {
		t.Helper()
		for name, size := range map[string]int{
			base + ".ext4":      60,
			base + ".boot.json": 10,
		} {
			path := filepath.Join(dir, name)
			if err := os.WriteFile(path, bytes.Repeat([]byte("x"), size), 0o600); err != nil {
				t.Fatal(err)
			}
			if err := os.Chtimes(path, used, used); err != nil {
				t.Fatal(err)
			}
		}
	}
	writeCachePair(oldBase, time.Unix(1, 0))
	writeCachePair(newBase, time.Unix(2, 0))

	if err := evictRootfsCache(dir, 100, 0, map[string]bool{newBase: true}); err != nil {
		t.Fatal(err)
	}
	for _, suffix := range []string{".ext4", ".boot.json"} {
		if _, err := os.Stat(filepath.Join(dir, oldBase+suffix)); !os.IsNotExist(err) {
			t.Fatalf("old cache pair member %s was not evicted: %v", suffix, err)
		}
		if _, err := os.Stat(filepath.Join(dir, newBase+suffix)); err != nil {
			t.Fatalf("protected recent cache pair member %s missing: %v", suffix, err)
		}
	}
}

func TestRootfsCacheRejectsItemLargerThanBudget(t *testing.T) {
	t.Parallel()
	if err := evictRootfsCache(t.TempDir(), 100, 101, nil); err == nil {
		t.Fatal("oversized rootfs cache item was accepted")
	}
}

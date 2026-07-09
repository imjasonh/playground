package layer_test

import (
	"io"
	"os"
	"path/filepath"
	"testing"

	"github.com/imjasonh/playground/node-image/internal/layer"
)

func TestBlobCacheTeesAndReuses(t *testing.T) {
	dir := t.TempDir()
	cache := &layer.BlobCache{Dir: dir}
	files := []layer.File{{Rel: "app/x.js", Mode: 0o644, Body: []byte("console.log(1)")}}

	d1, n1, p1, err := cache.EnsureCompressed(files)
	if err != nil {
		t.Fatal(err)
	}
	if d1 == "" || n1 == 0 || p1 == "" {
		t.Fatalf("empty result: %s %d %s", d1, n1, p1)
	}
	st1, err := os.Stat(p1)
	if err != nil {
		t.Fatal(err)
	}

	d2, n2, p2, err := cache.EnsureCompressed(files)
	if err != nil {
		t.Fatal(err)
	}
	if d1 != d2 || n1 != n2 || p1 != p2 {
		t.Fatalf("cache miss on second call: %s/%s %d/%d %s/%s", d1, d2, n1, n2, p1, p2)
	}
	st2, _ := os.Stat(p2)
	if st2.ModTime() != st1.ModTime() {
		t.Fatal("expected cached file to be reused without rewrite")
	}

	opener := cache.CachedOpener(files)
	r1, err := opener()
	if err != nil {
		t.Fatal(err)
	}
	b1, _ := io.ReadAll(r1)
	r1.Close()
	r2, err := opener()
	if err != nil {
		t.Fatal(err)
	}
	b2, _ := io.ReadAll(r2)
	r2.Close()
	if string(b1) != string(b2) || len(b1) == 0 {
		t.Fatalf("opener mismatch len %d/%d", len(b1), len(b2))
	}
	if filepath.Dir(p1) != dir {
		t.Fatalf("blob not under cache dir: %s", p1)
	}
}

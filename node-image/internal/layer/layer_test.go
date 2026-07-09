package layer_test

import (
	"io/fs"
	"testing"

	"github.com/imjasonh/playground/node-image/internal/layer"
)

func TestDeterministicDiffIDAndDigest(t *testing.T) {
	files := []layer.File{
		{Rel: "app/b.txt", Mode: 0o644, Body: []byte("b")},
		{Rel: "app/a.txt", Mode: 0o644, Body: []byte("a")},
		{Rel: "app/link", Mode: fs.ModeSymlink | 0o777, Link: "a.txt"},
	}
	d1, err := layer.DiffID(files)
	if err != nil {
		t.Fatal(err)
	}
	d2, err := layer.DiffID(files)
	if err != nil {
		t.Fatal(err)
	}
	if d1 != d2 {
		t.Fatalf("diffID not stable: %s vs %s", d1, d2)
	}
	// Different order must not matter.
	shuffled := []layer.File{files[2], files[0], files[1]}
	d3, err := layer.DiffID(shuffled)
	if err != nil {
		t.Fatal(err)
	}
	if d1 != d3 {
		t.Fatalf("diffID depends on input order: %s vs %s", d1, d3)
	}

	c1, s1, err := layer.CompressedDigest(files)
	if err != nil {
		t.Fatal(err)
	}
	c2, s2, err := layer.CompressedDigest(files)
	if err != nil {
		t.Fatal(err)
	}
	if c1 != c2 || s1 != s2 {
		t.Fatalf("compressed digest not stable: %s/%d vs %s/%d", c1, s1, c2, s2)
	}
	if c1 == d1 {
		t.Fatal("compressed digest unexpectedly equals diffID")
	}
	_, _, b1, err := layer.CompressedDigestBytes(files)
	if err != nil {
		t.Fatal(err)
	}
	_, _, b2, err := layer.CompressedDigestBytes(files)
	if err != nil {
		t.Fatal(err)
	}
	if string(b1) != string(b2) {
		t.Fatal("compressed bytes not stable")
	}
}

func TestContentChangeChangesDigest(t *testing.T) {
	a := []layer.File{{Rel: "app/x", Mode: 0o644, Body: []byte("one")}}
	b := []layer.File{{Rel: "app/x", Mode: 0o644, Body: []byte("two")}}
	da, _ := layer.DiffID(a)
	db, _ := layer.DiffID(b)
	if da == db {
		t.Fatal("expected different diffIDs for different content")
	}
}

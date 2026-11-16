package tree

import (
	"context"
	"os"
	"path/filepath"
	"slices"
	"testing"

	repb "github.com/bazelbuild/remote-apis/build/bazel/remote/execution/v2"

	"github.com/imjasonh/playground/ci-substrate/internal/digest"
)

// memFetcher serves blobs from memory and counts fetches.
type memFetcher struct {
	blobs   map[string][]byte
	fetches int
}

func newMemFetcher() *memFetcher { return &memFetcher{blobs: map[string][]byte{}} }

func (m *memFetcher) put(b []byte) *repb.Digest {
	d := digest.FromBytes(b)
	m.blobs[digest.Key(d)] = b
	return d
}

func (m *memFetcher) Fetch(_ context.Context, _ string, d *repb.Digest) ([]byte, error) {
	m.fetches++
	b, ok := m.blobs[digest.Key(d)]
	if !ok {
		return nil, os.ErrNotExist
	}
	return b, nil
}

// batchFetcher serves memFetcher's blobs through FetchBatch and records
// how many blobs each batch asked for.
type batchFetcher struct {
	*memFetcher
	batches []int
}

func (b *batchFetcher) FetchBatch(ctx context.Context, instance string, ds []*repb.Digest) ([][]byte, error) {
	b.batches = append(b.batches, len(ds))
	out := make([][]byte, len(ds))
	for i, d := range ds {
		blob, err := b.Fetch(ctx, instance, d)
		if err != nil {
			return nil, err
		}
		out[i] = blob
	}
	return out, nil
}

// TestBatchedReads checks that Load reads one batch per level of the tree,
// asking for each directory once, and that Materialize reads a directory's
// files in batches of at most materializeBatchBytes.
func TestBatchedReads(t *testing.T) {
	m := newMemFetcher()
	file := &repb.FileNode{Name: "f", Digest: m.put([]byte("shared"))}
	leaf := m.put(Marshal(&repb.Directory{Files: []*repb.FileNode{file}}))
	var mids []*repb.DirectoryNode
	for _, name := range []string{"a", "b", "c"} {
		mid := &repb.Directory{
			Files:       []*repb.FileNode{{Name: "own", Digest: m.put([]byte(name))}},
			Directories: []*repb.DirectoryNode{{Name: "leaf", Digest: leaf}},
		}
		mids = append(mids, &repb.DirectoryNode{Name: name, Digest: m.put(Marshal(mid))})
	}
	big1 := &repb.FileNode{Name: "big1", Digest: m.put(make([]byte, 3<<20))}
	big2 := &repb.FileNode{Name: "big2", Digest: m.put(make([]byte, 1<<20))}
	root := m.put(Marshal(&repb.Directory{Files: []*repb.FileNode{big1, big2, file}, Directories: mids}))

	f := &batchFetcher{memFetcher: m}
	tr, err := Load(t.Context(), f, "inst", root)
	if err != nil {
		t.Fatal(err)
	}
	if len(tr.Dirs) != 5 {
		t.Fatalf("loaded %d directories, want 5", len(tr.Dirs))
	}
	if want := []int{1, 3, 1}; !slices.Equal(f.batches, want) {
		t.Errorf("Load batches = %v, want %v", f.batches, want)
	}

	f.batches = nil
	dest := t.TempDir()
	if err := Materialize(t.Context(), f, "inst", tr, dest); err != nil {
		t.Fatal(err)
	}
	// The root's 3 MiB and 1 MiB files fill one 4 MiB batch, and its small
	// file starts the next.
	if want := []int{2, 1, 1, 1, 1, 1, 1, 1}; !slices.Equal(f.batches, want) {
		t.Errorf("Materialize batches = %v, want %v", f.batches, want)
	}
	if b, err := os.ReadFile(filepath.Join(dest, "b/leaf/f")); err != nil || string(b) != "shared" {
		t.Errorf("b/leaf/f: %q, %v", b, err)
	}
}

func TestLoadEmptyRoot(t *testing.T) {
	f := newMemFetcher()
	empty := digest.FromBytes(nil)
	got, err := Load(t.Context(), f, "", empty)
	if err != nil {
		t.Fatal(err)
	}
	if dir, err := got.Dir(empty); err != nil || len(dir.GetFiles()) != 0 {
		t.Fatalf("empty root: dir=%v err=%v", dir, err)
	}
	if f.fetches != 0 {
		t.Fatalf("empty root fetched %d blobs, want 0", f.fetches)
	}
	forged := &repb.Digest{Hash: digest.FromBytes([]byte("x")).GetHash(), SizeBytes: 0}
	if _, err := Load(t.Context(), f, "", forged); err == nil {
		t.Fatal("a size-0 digest with the wrong hash loaded as the empty root")
	}
}

func TestRoundTrip(t *testing.T) {
	src := t.TempDir()
	if err := os.MkdirAll(filepath.Join(src, "sub/deeper"), 0o755); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(filepath.Join(src, "a.txt"), []byte("alpha"), 0o644); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(filepath.Join(src, "sub/run.sh"), []byte("#!/bin/sh\n"), 0o755); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(filepath.Join(src, "sub/deeper/b.txt"), []byte("beta"), 0o644); err != nil {
		t.Fatal(err)
	}
	if err := os.Symlink("a.txt", filepath.Join(src, "link")); err != nil {
		t.Fatal(err)
	}

	out, err := FromDir(src)
	if err != nil {
		t.Fatal(err)
	}
	if len(out.Blobs) != 3 || len(out.Tree.GetChildren()) != 2 {
		t.Fatalf("got %d blobs and %d child directories, want 3 and 2", len(out.Blobs), len(out.Tree.GetChildren()))
	}
	again, err := FromDir(src)
	if err != nil {
		t.Fatal(err)
	}
	if Digest(out.Tree).GetHash() != Digest(again.Tree).GetHash() {
		t.Fatal("FromDir is not deterministic")
	}

	// Store the tree's directories and blobs in a fetcher, then load and
	// materialize it somewhere else.
	f := newMemFetcher()
	for _, b := range out.Blobs {
		f.put(b)
	}
	root := f.put(Marshal(out.Tree.GetRoot()))
	for _, c := range out.Tree.GetChildren() {
		f.put(Marshal(c))
	}
	tr, err := Load(t.Context(), f, "inst", root)
	if err != nil {
		t.Fatal(err)
	}
	if len(tr.Dirs) != 3 {
		t.Fatalf("loaded %d directories, want 3", len(tr.Dirs))
	}
	dest := t.TempDir()
	if err := Materialize(t.Context(), f, "inst", tr, dest); err != nil {
		t.Fatal(err)
	}
	b, err := os.ReadFile(filepath.Join(dest, "sub/deeper/b.txt"))
	if err != nil || string(b) != "beta" {
		t.Fatalf("b.txt: %q, %v", b, err)
	}
	info, err := os.Stat(filepath.Join(dest, "sub/run.sh"))
	if err != nil || info.Mode()&0o111 == 0 {
		t.Fatalf("run.sh not executable: %v %v", info, err)
	}
	target, err := os.Readlink(filepath.Join(dest, "link"))
	if err != nil || target != "a.txt" {
		t.Fatalf("link: %q, %v", target, err)
	}
}

func TestLoadRejectsEscapingNames(t *testing.T) {
	f := newMemFetcher()
	for _, dir := range []*repb.Directory{
		{Files: []*repb.FileNode{{Name: "../etc/passwd", Digest: digest.FromBytes(nil)}}},
		{Directories: []*repb.DirectoryNode{{Name: "a/b", Digest: digest.FromBytes(nil)}}},
		{Symlinks: []*repb.SymlinkNode{{Name: "l", Target: "/etc/passwd"}}},
		{Files: []*repb.FileNode{{Name: "ok", Digest: &repb.Digest{Hash: "zz", SizeBytes: 1}}}},
	} {
		root := f.put(Marshal(dir))
		if _, err := Load(t.Context(), f, "inst", root); err == nil {
			t.Errorf("Load accepted %v", dir)
		}
	}
}

func TestLoadRejectsCorruptDirectory(t *testing.T) {
	f := newMemFetcher()
	d := f.put([]byte("good"))
	f.blobs[digest.Key(d)] = []byte("evil")
	if _, err := Load(t.Context(), f, "inst", d); err == nil {
		t.Fatal("Load accepted a directory whose bytes do not match its digest")
	}
}

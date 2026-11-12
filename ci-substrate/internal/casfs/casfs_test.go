package casfs_test

import (
	"context"
	"os"
	"os/exec"
	"path/filepath"
	"sync"
	"testing"

	repb "github.com/bazelbuild/remote-apis/build/bazel/remote/execution/v2"

	"github.com/imjasonh/playground/ci-substrate/internal/casfs"
	"github.com/imjasonh/playground/ci-substrate/internal/digest"
	"github.com/imjasonh/playground/ci-substrate/internal/tree"
)

type memFetcher struct {
	mu      sync.Mutex
	blobs   map[string][]byte
	fetched map[string]int
}

func newMemFetcher() *memFetcher {
	return &memFetcher{blobs: map[string][]byte{}, fetched: map[string]int{}}
}

func (m *memFetcher) put(b []byte) *repb.Digest {
	d := digest.FromBytes(b)
	m.blobs[digest.Key(d)] = b
	return d
}

func (m *memFetcher) Fetch(_ context.Context, _ string, d *repb.Digest) ([]byte, error) {
	m.mu.Lock()
	defer m.mu.Unlock()
	m.fetched[digest.Key(d)]++
	b, ok := m.blobs[digest.Key(d)]
	if !ok {
		return nil, os.ErrNotExist
	}
	return b, nil
}

func (m *memFetcher) count(d *repb.Digest) int {
	m.mu.Lock()
	defer m.mu.Unlock()
	return m.fetched[digest.Key(d)]
}

func requireFUSE(t *testing.T) {
	t.Helper()
	if _, err := os.Stat("/dev/fuse"); err != nil {
		t.Skip("/dev/fuse not available")
	}
	if _, err := exec.LookPath("fusermount3"); err != nil {
		if _, err := exec.LookPath("fusermount"); err != nil {
			t.Skip("fusermount not available")
		}
	}
}

func TestLazyHydration(t *testing.T) {
	requireFUSE(t)
	f := newMemFetcher()
	small := f.put([]byte("hello from the CAS"))
	big := f.put(make([]byte, 3<<20))
	script := f.put([]byte("#!/bin/sh\necho hi\n"))
	sub := f.put(tree.Marshal(&repb.Directory{
		Files: []*repb.FileNode{{Name: "big.bin", Digest: big}},
	}))
	root := f.put(tree.Marshal(&repb.Directory{
		Files: []*repb.FileNode{
			{Name: "hello.txt", Digest: small},
			{Name: "run.sh", Digest: script, IsExecutable: true},
		},
		Directories: []*repb.DirectoryNode{{Name: "sub", Digest: sub}},
		Symlinks:    []*repb.SymlinkNode{{Name: "link", Target: "hello.txt"}},
	}))
	tr, err := tree.Load(t.Context(), f, "inst", root)
	if err != nil {
		t.Fatal(err)
	}
	fetchesAfterLoad := len(f.fetched)

	mnt := t.TempDir()
	server, err := casfs.Mount(t.Context(), mnt, tr, f, "inst")
	if err != nil {
		t.Fatalf("mount: %v", err)
	}
	t.Cleanup(func() { server.Unmount() })

	// Listing and stat need no file fetches.
	entries, err := os.ReadDir(mnt)
	if err != nil {
		t.Fatal(err)
	}
	if len(entries) != 4 {
		t.Fatalf("got %d entries, want 4", len(entries))
	}
	info, err := os.Stat(filepath.Join(mnt, "sub/big.bin"))
	if err != nil {
		t.Fatal(err)
	}
	if info.Size() != 3<<20 {
		t.Fatalf("big.bin size %d", info.Size())
	}
	if len(f.fetched) != fetchesAfterLoad {
		t.Fatalf("metadata operations fetched %d blobs", len(f.fetched)-fetchesAfterLoad)
	}
	if f.count(big) != 0 {
		t.Fatal("big.bin was fetched before anyone read it")
	}

	// Reading one file fetches only that file, once.
	got, err := os.ReadFile(filepath.Join(mnt, "hello.txt"))
	if err != nil || string(got) != "hello from the CAS" {
		t.Fatalf("hello.txt: %q, %v", got, err)
	}
	if _, err := os.ReadFile(filepath.Join(mnt, "hello.txt")); err != nil {
		t.Fatal(err)
	}
	if n := f.count(small); n != 1 {
		t.Fatalf("hello.txt fetched %d times, want 1", n)
	}
	if f.count(big) != 0 {
		t.Fatal("reading hello.txt fetched big.bin")
	}

	target, err := os.Readlink(filepath.Join(mnt, "link"))
	if err != nil || target != "hello.txt" {
		t.Fatalf("link: %q, %v", target, err)
	}
	info, err = os.Stat(filepath.Join(mnt, "run.sh"))
	if err != nil || info.Mode()&0o111 == 0 {
		t.Fatalf("run.sh mode %v, %v", info.Mode(), err)
	}
	out, err := exec.Command(filepath.Join(mnt, "run.sh")).Output()
	if err != nil || string(out) != "hi\n" {
		t.Fatalf("running run.sh from the mount: %q, %v", out, err)
	}

	// The mount is the exec root, so an action can write outputs into it:
	// new files, new directories, and changes to CAS-backed files. None of
	// that touches the CAS.
	if err := os.MkdirAll(filepath.Join(mnt, "out/nested"), 0o755); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(filepath.Join(mnt, "out/nested/result.txt"), []byte("built"), 0o644); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(filepath.Join(mnt, "sub/big.bin"), []byte("replaced"), 0o644); err != nil {
		t.Fatal(err)
	}
	got, err = os.ReadFile(filepath.Join(mnt, "out/nested/result.txt"))
	if err != nil || string(got) != "built" {
		t.Fatalf("result.txt: %q, %v", got, err)
	}
	got, err = os.ReadFile(filepath.Join(mnt, "sub/big.bin"))
	if err != nil || string(got) != "replaced" {
		t.Fatalf("big.bin after write: %d bytes, %v", len(got), err)
	}
	if f.count(big) != 0 {
		t.Fatal("truncating big.bin fetched its old contents")
	}
	if len(f.blobs[digest.Key(big)]) != 3<<20 {
		t.Fatal("writing through the mount changed the CAS")
	}
	if err := os.Rename(filepath.Join(mnt, "out/nested/result.txt"), filepath.Join(mnt, "out/final.txt")); err != nil {
		t.Fatal(err)
	}
	if err := os.Remove(filepath.Join(mnt, "out/nested")); err != nil {
		t.Fatal(err)
	}
	appendTo, err := os.OpenFile(filepath.Join(mnt, "hello.txt"), os.O_WRONLY|os.O_APPEND, 0)
	if err != nil {
		t.Fatal(err)
	}
	if _, err := appendTo.WriteString("!"); err != nil {
		t.Fatal(err)
	}
	appendTo.Close()
	got, err = os.ReadFile(filepath.Join(mnt, "hello.txt"))
	if err != nil || string(got) != "hello from the CAS!" {
		t.Fatalf("hello.txt after append: %q, %v", got, err)
	}
	out2, err := tree.FromDir(filepath.Join(mnt, "out"))
	if err != nil {
		t.Fatal(err)
	}
	if len(out2.Tree.GetRoot().GetFiles()) != 1 || out2.Tree.GetRoot().GetFiles()[0].GetName() != "final.txt" {
		t.Fatalf("out/ after rename and rmdir: %v", out2.Tree.GetRoot())
	}
}

func TestCorruptBlobIsNotServed(t *testing.T) {
	requireFUSE(t)
	f := newMemFetcher()
	d := f.put([]byte("trusted bytes"))
	f.blobs[digest.Key(d)] = []byte("swapped bytes")
	root := f.put(tree.Marshal(&repb.Directory{Files: []*repb.FileNode{{Name: "f", Digest: d}}}))
	tr, err := tree.Load(t.Context(), f, "inst", root)
	if err != nil {
		t.Fatal(err)
	}
	mnt := t.TempDir()
	server, err := casfs.Mount(t.Context(), mnt, tr, f, "inst")
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { server.Unmount() })
	if _, err := os.ReadFile(filepath.Join(mnt, "f")); err == nil {
		t.Fatal("read of a blob that fails verification succeeded")
	}
}

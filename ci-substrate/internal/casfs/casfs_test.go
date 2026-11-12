package casfs_test

import (
	"context"
	"os"
	"os/exec"
	"path/filepath"
	"sync"
	"syscall"
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
	server, err := casfs.Mount(mnt, tr, f, "inst")
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
	// A sandbox kernel checks the reported mode against its own user, which
	// is not the one serving the mount, so everything is open to everyone.
	for name, want := range map[string]os.FileMode{"": 0o777 | os.ModeDir, "sub": 0o777 | os.ModeDir, "hello.txt": 0o666, "run.sh": 0o777} {
		info, err := os.Stat(filepath.Join(mnt, name))
		if err != nil || info.Mode() != want {
			t.Errorf("%q mode %v, %v; want %v", name, info.Mode(), err, want)
		}
	}
	// gVisor's gofer chowns what it creates to the sandbox user and fails
	// the create when that fails, so a chown to the caller's own ids is
	// accepted on every kind of entry and reported back.
	me, mygroup := os.Getuid(), os.Getgid()
	for _, name := range []string{"sub", "hello.txt", "link"} {
		if err := os.Lchown(filepath.Join(mnt, name), me, mygroup); err != nil {
			t.Errorf("chown %q: %v", name, err)
		}
		info, err := os.Lstat(filepath.Join(mnt, name))
		if err != nil {
			t.Fatal(err)
		}
		if st := info.Sys().(*syscall.Stat_t); int(st.Uid) != me || int(st.Gid) != mygroup {
			t.Errorf("%q owner %d:%d after chown, want %d:%d", name, st.Uid, st.Gid, me, mygroup)
		}
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

func TestVolumeMaterializesExecRoots(t *testing.T) {
	requireFUSE(t)
	f := newMemFetcher()
	hello := f.put([]byte("hello from the CAS"))
	big := f.put(make([]byte, 1<<20))
	root := f.put(tree.Marshal(&repb.Directory{
		Files: []*repb.FileNode{
			{Name: "hello.txt", Digest: hello},
			{Name: "big.bin", Digest: big},
		},
	}))

	mnt := t.TempDir()
	server, err := casfs.MountVolume(mnt, f, "inst")
	if err != nil {
		t.Fatalf("mount: %v", err)
	}
	t.Cleanup(func() { server.Unmount() })

	// The root starts empty and takes nothing but exec roots.
	if entries, err := os.ReadDir(mnt); err != nil || len(entries) != 0 {
		t.Fatalf("fresh volume: %v, %v", entries, err)
	}
	if err := os.Mkdir(filepath.Join(mnt, "scratch"), 0o755); err == nil {
		t.Fatal("mkdir of a non-digest name succeeded")
	}
	if err := os.WriteFile(filepath.Join(mnt, "file"), nil, 0o644); err == nil {
		t.Fatal("create at the volume root succeeded")
	}
	missing := digest.FromBytes([]byte("not in the CAS"))
	if err := os.Mkdir(filepath.Join(mnt, casfs.ExecRootName(missing, "")), 0o755); err == nil {
		t.Fatal("mkdir of a digest the CAS lacks succeeded")
	}

	// mkdir of a digest loads the tree; the files hydrate on read.
	name := casfs.ExecRootName(root, "job-1")
	execRoot := filepath.Join(mnt, name)
	if err := os.Mkdir(execRoot, 0o755); err != nil {
		t.Fatalf("mkdir exec root: %v", err)
	}
	if f.count(root) != 1 {
		t.Fatalf("root directory fetched %d times, want 1", f.count(root))
	}
	info, err := os.Stat(filepath.Join(execRoot, "big.bin"))
	if err != nil || info.Size() != 1<<20 {
		t.Fatalf("big.bin: %v, %v", info, err)
	}
	if f.count(big) != 0 {
		t.Fatal("big.bin was fetched before anyone read it")
	}
	got, err := os.ReadFile(filepath.Join(execRoot, "hello.txt"))
	if err != nil || string(got) != "hello from the CAS" {
		t.Fatalf("hello.txt: %q, %v", got, err)
	}

	// The exec root takes outputs, and the same input root can be
	// materialized again under another tag without touching the first.
	if err := os.WriteFile(filepath.Join(execRoot, "out.txt"), []byte("built"), 0o644); err != nil {
		t.Fatal(err)
	}
	second := filepath.Join(mnt, casfs.ExecRootName(root, "job-2"))
	if err := os.Mkdir(second, 0o755); err != nil {
		t.Fatal(err)
	}
	if _, err := os.Stat(filepath.Join(second, "out.txt")); err == nil {
		t.Fatal("second exec root sees the first one's output")
	}
	if err := os.Mkdir(execRoot, 0o755); !os.IsExist(err) {
		t.Fatalf("mkdir of a live exec root: %v, want EEXIST", err)
	}
	if err := os.Rename(filepath.Join(execRoot, "out.txt"), filepath.Join(mnt, "out.txt")); err == nil {
		t.Fatal("rename into the volume root succeeded")
	}

	// rmdir drops a whole exec root, outputs and all.
	if err := os.Remove(execRoot); err != nil {
		t.Fatalf("rmdir exec root: %v", err)
	}
	if _, err := os.Stat(execRoot); !os.IsNotExist(err) {
		t.Fatalf("exec root after rmdir: %v", err)
	}
	entries, err := os.ReadDir(mnt)
	if err != nil || len(entries) != 1 || entries[0].Name() != filepath.Base(second) {
		t.Fatalf("volume after rmdir: %v, %v", entries, err)
	}
	if err := os.Remove(second); err != nil {
		t.Fatal(err)
	}

	// The empty input root materializes without a fetch.
	empty := tree.Digest(&repb.Directory{})
	if err := os.Mkdir(filepath.Join(mnt, casfs.ExecRootName(empty, "probe")), 0o755); err != nil {
		t.Fatalf("mkdir empty exec root: %v", err)
	}
	if f.count(empty) != 0 {
		t.Fatal("the empty Directory was fetched")
	}
}

func TestExecRootName(t *testing.T) {
	d := digest.FromBytes([]byte("x"))
	for _, tc := range []struct {
		name string
		want *repb.Digest
	}{
		{casfs.ExecRootName(d, ""), d},
		{casfs.ExecRootName(d, "job-1_a"), d},
		{casfs.ExecRootName(&repb.Digest{Hash: d.Hash, SizeBytes: 0}, "p"), &repb.Digest{Hash: d.Hash}},
		{d.Hash, nil},
		{d.Hash + "-01", nil},
		{d.Hash + "-1.", nil},
		{d.Hash + "-1.a/b", nil},
		{"..", nil},
		{"", nil},
	} {
		got, err := casfs.ParseExecRootName(tc.name)
		if tc.want == nil {
			if err == nil {
				t.Errorf("%q parsed as %v", tc.name, got)
			}
			continue
		}
		if err != nil || got.GetHash() != tc.want.GetHash() || got.GetSizeBytes() != tc.want.GetSizeBytes() {
			t.Errorf("%q: %v, %v; want %v", tc.name, got, err, tc.want)
		}
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
	server, err := casfs.Mount(mnt, tr, f, "inst")
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { server.Unmount() })
	if _, err := os.ReadFile(filepath.Join(mnt, "f")); err == nil {
		t.Fatal("read of a blob that fails verification succeeded")
	}
}

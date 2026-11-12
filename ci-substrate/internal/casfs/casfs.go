// Package casfs serves a Remote Execution input root as a FUSE filesystem
// whose files are fetched from the CAS on first read. The directory tree,
// names, sizes, and modes come from the Directory protos, so the mount is
// ready as soon as the metadata is loaded; file bytes arrive lazily, one blob
// per opened file, through the node-local cache. An action that reads a tenth
// of its inputs costs a tenth of the transfer, and the host, not the sandbox,
// holds the tenant credential that fetches them.
//
// The mount is also the action's exec root, so it accepts writes. A write to
// a CAS-backed file hydrates it first and then changes the copy in memory; new
// files and directories live in memory too. Nothing written reaches the CAS
// through the mount: the runner reads the output paths back and uploads them
// itself, which is where output handling decides what is worth keeping.
package casfs

import (
	"context"
	"log/slog"
	"sync"
	"syscall"

	repb "github.com/bazelbuild/remote-apis/build/bazel/remote/execution/v2"
	"github.com/hanwen/go-fuse/v2/fs"
	"github.com/hanwen/go-fuse/v2/fuse"

	"github.com/imjasonh/playground/ci-substrate/internal/digest"
	"github.com/imjasonh/playground/ci-substrate/internal/tree"
)

// Mount serves t at dir until Unmount is called on the returned server. Reads
// use f with instance.
func Mount(dir string, t *tree.Tree, f tree.Fetcher, instance string) (*fuse.Server, error) {
	root := &dirNode{fsys: &casfs{tree: t, fetcher: f, instance: instance}, digest: t.Root}
	return fs.Mount(dir, root, &fs.Options{
		MountOptions: fuse.MountOptions{FsName: "casfs", Name: "casfs"},
	})
}

type casfs struct {
	tree     *tree.Tree
	fetcher  tree.Fetcher
	instance string
}

// dirNode is a directory. One that came from the tree fills its children
// from its Directory proto when it is added; one created through the mount
// starts empty. The mutation methods only check preconditions and build new
// inodes: go-fuse's bridge adds, removes, and moves the children itself once
// they return success.
type dirNode struct {
	fs.Inode
	fsys   *casfs
	digest *repb.Digest
}

var (
	_ = (fs.NodeOnAdder)((*dirNode)(nil))
	_ = (fs.NodeMkdirer)((*dirNode)(nil))
	_ = (fs.NodeCreater)((*dirNode)(nil))
	_ = (fs.NodeUnlinker)((*dirNode)(nil))
	_ = (fs.NodeRmdirer)((*dirNode)(nil))
	_ = (fs.NodeRenamer)((*dirNode)(nil))
	_ = (fs.NodeSymlinker)((*dirNode)(nil))
)

func (d *dirNode) OnAdd(ctx context.Context) {
	if d.digest == nil {
		return
	}
	dir, err := d.fsys.tree.Dir(d.digest)
	if err != nil {
		// Load validated every reference, so a missing directory is a bug
		// rather than a runtime condition. Serve it empty.
		slog.Error("casfs: directory not loaded", "digest", digest.Key(d.digest), "err", err)
		return
	}
	for _, n := range dir.GetDirectories() {
		child := d.NewPersistentInode(ctx, &dirNode{fsys: d.fsys, digest: n.GetDigest()}, fs.StableAttr{Mode: syscall.S_IFDIR})
		d.AddChild(n.GetName(), child, true)
	}
	for _, n := range dir.GetFiles() {
		mode := uint32(0o644)
		if n.GetIsExecutable() {
			mode = 0o755
		}
		child := d.NewPersistentInode(ctx, &fileNode{fsys: d.fsys, source: n.GetDigest(), mode: mode}, fs.StableAttr{Mode: syscall.S_IFREG})
		d.AddChild(n.GetName(), child, true)
	}
	for _, n := range dir.GetSymlinks() {
		child := d.NewPersistentInode(ctx, &fs.MemSymlink{Data: []byte(n.GetTarget())}, fs.StableAttr{Mode: syscall.S_IFLNK})
		d.AddChild(n.GetName(), child, true)
	}
}

func (d *dirNode) Mkdir(ctx context.Context, name string, mode uint32, out *fuse.EntryOut) (*fs.Inode, syscall.Errno) {
	if d.GetChild(name) != nil {
		return nil, syscall.EEXIST
	}
	return d.NewPersistentInode(ctx, &dirNode{fsys: d.fsys}, fs.StableAttr{Mode: syscall.S_IFDIR}), 0
}

func (d *dirNode) Create(ctx context.Context, name string, flags uint32, mode uint32, out *fuse.EntryOut) (*fs.Inode, fs.FileHandle, uint32, syscall.Errno) {
	if d.GetChild(name) != nil {
		return nil, nil, 0, syscall.EEXIST
	}
	f := &fileNode{fsys: d.fsys, hydrated: true, mode: mode & 0o777}
	return d.NewPersistentInode(ctx, f, fs.StableAttr{Mode: syscall.S_IFREG}), nil, fuse.FOPEN_KEEP_CACHE, 0
}

func (d *dirNode) Symlink(ctx context.Context, target, name string, out *fuse.EntryOut) (*fs.Inode, syscall.Errno) {
	if d.GetChild(name) != nil {
		return nil, syscall.EEXIST
	}
	return d.NewPersistentInode(ctx, &fs.MemSymlink{Data: []byte(target)}, fs.StableAttr{Mode: syscall.S_IFLNK}), 0
}

func (d *dirNode) Unlink(ctx context.Context, name string) syscall.Errno {
	child := d.GetChild(name)
	if child == nil {
		return syscall.ENOENT
	}
	if child.IsDir() {
		return syscall.EISDIR
	}
	return 0
}

func (d *dirNode) Rmdir(ctx context.Context, name string) syscall.Errno {
	child := d.GetChild(name)
	if child == nil {
		return syscall.ENOENT
	}
	if !child.IsDir() {
		return syscall.ENOTDIR
	}
	if len(child.Children()) > 0 {
		return syscall.ENOTEMPTY
	}
	return 0
}

func (d *dirNode) Rename(ctx context.Context, name string, newParent fs.InodeEmbedder, newName string, flags uint32) syscall.Errno {
	if d.GetChild(name) == nil {
		return syscall.ENOENT
	}
	return 0
}

// fileNode is a file. One from the tree has a source digest and is hydrated
// from the CAS on first open; one created through the mount, or hydrated and
// then written, is plain bytes in memory.
type fileNode struct {
	fs.Inode
	fsys   *casfs
	source *repb.Digest
	mode   uint32

	mu       sync.Mutex
	hydrated bool
	data     []byte
}

var (
	_ = (fs.NodeGetattrer)((*fileNode)(nil))
	_ = (fs.NodeSetattrer)((*fileNode)(nil))
	_ = (fs.NodeOpener)((*fileNode)(nil))
	_ = (fs.NodeReader)((*fileNode)(nil))
	_ = (fs.NodeWriter)((*fileNode)(nil))
	_ = (fs.NodeFlusher)((*fileNode)(nil))
)

func (f *fileNode) Getattr(ctx context.Context, fh fs.FileHandle, out *fuse.AttrOut) syscall.Errno {
	f.mu.Lock()
	defer f.mu.Unlock()
	out.Mode = f.mode
	if f.hydrated {
		out.Size = uint64(len(f.data))
	} else {
		out.Size = uint64(f.source.GetSizeBytes())
	}
	return 0
}

func (f *fileNode) Setattr(ctx context.Context, fh fs.FileHandle, in *fuse.SetAttrIn, out *fuse.AttrOut) syscall.Errno {
	f.mu.Lock()
	defer f.mu.Unlock()
	if m, ok := in.GetMode(); ok {
		f.mode = m & 0o777
	}
	if sz, ok := in.GetSize(); ok {
		if sz == 0 {
			// Truncation to nothing needs no fetch: whatever the CAS held
			// is gone.
			f.hydrated, f.data = true, nil
		} else {
			if errno := f.hydrateLocked(ctx); errno != 0 {
				return errno
			}
			if sz <= uint64(len(f.data)) {
				f.data = f.data[:sz]
			} else {
				n := make([]byte, sz)
				copy(n, f.data)
				f.data = n
			}
		}
	}
	out.Mode = f.mode
	if f.hydrated {
		out.Size = uint64(len(f.data))
	} else {
		out.Size = uint64(f.source.GetSizeBytes())
	}
	return 0
}

// Open does not fetch anything. The kernel usually sends truncation as a
// separate Setattr after Open, so fetching here would read bytes that a
// `> file` redirect is about to throw away. The first Read or Write hydrates.
func (f *fileNode) Open(ctx context.Context, flags uint32) (fs.FileHandle, uint32, syscall.Errno) {
	if flags&syscall.O_TRUNC != 0 {
		f.mu.Lock()
		f.hydrated, f.data = true, nil
		f.mu.Unlock()
	}
	return nil, fuse.FOPEN_KEEP_CACHE, 0
}

// hydrateLocked fetches the file's bytes if it still has none. Callers hold
// f.mu, so concurrent readers share one fetch, and the bytes are verified
// against the digest before any read sees them.
func (f *fileNode) hydrateLocked(ctx context.Context) syscall.Errno {
	if f.hydrated {
		return 0
	}
	// Detach from the opener: a second reader must not find the file
	// broken because the first one gave up.
	b, err := f.fsys.fetcher.Fetch(context.WithoutCancel(ctx), f.fsys.instance, f.source)
	if err == nil {
		err = digest.Verify(f.source, b)
	}
	if err != nil {
		slog.Error("casfs: hydrating file", "digest", digest.Key(f.source), "err", err)
		return syscall.EIO
	}
	f.hydrated, f.data = true, b
	return 0
}

func (f *fileNode) Read(ctx context.Context, fh fs.FileHandle, dest []byte, off int64) (fuse.ReadResult, syscall.Errno) {
	f.mu.Lock()
	defer f.mu.Unlock()
	if errno := f.hydrateLocked(ctx); errno != 0 {
		return nil, errno
	}
	if off >= int64(len(f.data)) {
		return fuse.ReadResultData(nil), 0
	}
	end := min(int64(len(f.data)), off+int64(len(dest)))
	return fuse.ReadResultData(f.data[off:end]), 0
}

func (f *fileNode) Write(ctx context.Context, fh fs.FileHandle, data []byte, off int64) (uint32, syscall.Errno) {
	f.mu.Lock()
	defer f.mu.Unlock()
	if errno := f.hydrateLocked(ctx); errno != 0 {
		return 0, errno
	}
	if end := off + int64(len(data)); end > int64(len(f.data)) {
		n := make([]byte, end)
		copy(n, f.data)
		f.data = n
	}
	copy(f.data[off:], data)
	return uint32(len(data)), 0
}

func (f *fileNode) Flush(ctx context.Context, fh fs.FileHandle) syscall.Errno {
	return 0
}

// Package casfs serves a Remote Execution input root as a read-only FUSE
// filesystem whose files are fetched from the CAS on first read. The
// directory tree, names, sizes, and modes come from the Directory protos, so
// the mount is ready as soon as the metadata is loaded; file bytes arrive
// lazily, one blob per opened file, through the node-local cache. An action
// that reads a tenth of its inputs costs a tenth of the transfer, and the
// host, not the sandbox, holds the tenant credential that fetches them.
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
		MountOptions: fuse.MountOptions{
			FsName: "casfs",
			Name:   "casfs",
			// The content behind a digest never changes, so the kernel may
			// cache every page it reads for as long as it likes.
			Options: []string{"ro"},
		},
	})
}

type casfs struct {
	tree     *tree.Tree
	fetcher  tree.Fetcher
	instance string
}

// dirNode is a Directory from the tree. Its children are created when the
// kernel first looks at it.
type dirNode struct {
	fs.Inode
	fsys   *casfs
	digest *repb.Digest
}

var _ = (fs.NodeOnAdder)((*dirNode)(nil))

func (d *dirNode) OnAdd(ctx context.Context) {
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
		child := d.NewPersistentInode(ctx, &fileNode{fsys: d.fsys, node: n}, fs.StableAttr{Mode: syscall.S_IFREG})
		d.AddChild(n.GetName(), child, true)
	}
	for _, n := range dir.GetSymlinks() {
		child := d.NewPersistentInode(ctx, &fs.MemSymlink{Data: []byte(n.GetTarget())}, fs.StableAttr{Mode: syscall.S_IFLNK})
		d.AddChild(n.GetName(), child, true)
	}
}

// fileNode is a FileNode whose bytes are fetched on first open.
type fileNode struct {
	fs.Inode
	fsys *casfs
	node *repb.FileNode

	once sync.Once
	data []byte
	err  error
}

var (
	_ = (fs.NodeGetattrer)((*fileNode)(nil))
	_ = (fs.NodeOpener)((*fileNode)(nil))
	_ = (fs.NodeReader)((*fileNode)(nil))
)

func (f *fileNode) Getattr(ctx context.Context, fh fs.FileHandle, out *fuse.AttrOut) syscall.Errno {
	out.Mode = 0o444
	if f.node.GetIsExecutable() {
		out.Mode = 0o555
	}
	out.Size = uint64(f.node.GetDigest().GetSizeBytes())
	return 0
}

// Open hydrates the file. Concurrent opens share one fetch, and the fetched
// bytes are verified against the digest before any read sees them.
func (f *fileNode) Open(ctx context.Context, flags uint32) (fs.FileHandle, uint32, syscall.Errno) {
	if flags&(syscall.O_WRONLY|syscall.O_RDWR) != 0 {
		return nil, 0, syscall.EROFS
	}
	f.once.Do(func() {
		// Detach from the opener: a second reader must not find the file
		// permanently broken because the first one gave up.
		fetchCtx := context.WithoutCancel(ctx)
		b, err := f.fsys.fetcher.Fetch(fetchCtx, f.fsys.instance, f.node.GetDigest())
		if err == nil {
			err = digest.Verify(f.node.GetDigest(), b)
		}
		f.data, f.err = b, err
	})
	if f.err != nil {
		slog.Error("casfs: hydrating file", "digest", digest.Key(f.node.GetDigest()), "err", f.err)
		return nil, 0, syscall.EIO
	}
	return nil, fuse.FOPEN_KEEP_CACHE, 0
}

func (f *fileNode) Read(ctx context.Context, fh fs.FileHandle, dest []byte, off int64) (fuse.ReadResult, syscall.Errno) {
	if f.err != nil {
		return nil, syscall.EIO
	}
	if off >= int64(len(f.data)) {
		return fuse.ReadResultData(nil), 0
	}
	end := min(int64(len(f.data)), off+int64(len(dest)))
	return fuse.ReadResultData(f.data[off:end]), 0
}

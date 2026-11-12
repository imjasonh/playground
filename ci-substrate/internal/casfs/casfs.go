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
//
// Every entry reports itself as writable by everyone, and directories as
// world-writable. A mount belongs to one action or one actor, and the
// filesystem itself decides what each name allows, so the mode bits carry
// only the executable bit. That matters in a sandbox whose kernel checks
// permissions against the reported owner and mode: a gVisor sandbox runs the
// action as whatever user its image names, while the mount is served by root
// on the host, and a root-owned 0755 exec root would refuse that user's
// outputs. A chmod that removes write permission is accepted and has no
// effect. A chown is accepted and reported back, because gVisor's gofer
// chowns every entry it creates to the sandbox user and gives up on the
// create when that fails.
//
// There are two mounts. Mount serves one input root, for a runner that can
// mount FUSE itself. MountVolume serves a volume that a host agent mounts once
// and a sandbox uses for many actions: mkdir of a digest under its root
// materializes that input root as an exec root, and rmdir drops it. That is
// how a Substrate actor, which cannot mount anything, gets lazy hydration from
// its own node: the CSI driver on the node mounts the volume and the sandbox
// sees it as a directory.
package casfs

import (
	"context"
	"errors"
	"fmt"
	"log/slog"
	"os"
	"regexp"
	"strconv"
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
	return mount(dir, root, false)
}

// MountVolume serves an inputs volume at dir until Unmount is called on the
// returned server. The volume starts empty. A mkdir of a name that
// ExecRootName produces loads that Directory tree from f with instance and
// serves it as a writable exec root under that name; a mkdir of any other
// name fails with EINVAL, and one of a digest the CAS does not hold fails
// with ENOENT. An rmdir of an exec root drops it with whatever it holds.
// Nothing else can be created at the root.
//
// The mount allows other users, since the sandbox that reads it is not the
// user that serves it.
func MountVolume(dir string, f tree.Fetcher, instance string) (*fuse.Server, error) {
	return mount(dir, &volumeNode{fetcher: f, instance: instance}, true)
}

func mount(dir string, root fs.InodeEmbedder, allowOther bool) (*fuse.Server, error) {
	// As root, call mount(2) directly: a container has no fusermount binary,
	// and the strict mode reports the mount error itself rather than a
	// missing fusermount. Otherwise go with the fusermount helper, which
	// refuses allow_other unless /etc/fuse.conf opts in, so only root asks
	// for it; an unprivileged mount is only ever read by its own user.
	isRoot := os.Geteuid() == 0
	return fs.Mount(dir, root, &fs.Options{
		MountOptions: fuse.MountOptions{
			FsName:            "casfs",
			Name:              "casfs",
			DirectMountStrict: isRoot,
			AllowOther:        allowOther && isRoot,
		},
	})
}

// ExecRootName is the directory name that materializes the input root d on a
// volume: the digest's hash and size joined by a hyphen, then a dot and tag
// when tag is not empty. The tag keeps two exec roots of the same input root
// apart, so a runner uses its job id.
func ExecRootName(d *repb.Digest, tag string) string {
	name := fmt.Sprintf("%s-%d", d.GetHash(), d.GetSizeBytes())
	if tag != "" {
		name += "." + tag
	}
	return name
}

var execRootName = regexp.MustCompile(`^([0-9a-f]{64})-(0|[1-9][0-9]{0,17})(?:\.([A-Za-z0-9_-]{1,64}))?$`)

// ParseExecRootName returns the digest an exec root name materializes.
func ParseExecRootName(name string) (*repb.Digest, error) {
	m := execRootName.FindStringSubmatch(name)
	if m == nil {
		return nil, errors.New("casfs: an exec root is named <sha256>-<size>[.<tag>]")
	}
	size, err := strconv.ParseInt(m[2], 10, 64)
	if err != nil {
		return nil, fmt.Errorf("casfs: exec root size %q: %w", m[2], err)
	}
	return &repb.Digest{Hash: m[1], SizeBytes: size}, nil
}

type casfs struct {
	tree     *tree.Tree
	fetcher  tree.Fetcher
	instance string
}

// volumeNode is the root of an inputs volume. Its children are exec roots,
// one dirNode per materialized input root, each with its own loaded tree.
type volumeNode struct {
	fs.Inode
	fetcher  tree.Fetcher
	instance string
}

var (
	_ = (fs.NodeGetattrer)((*volumeNode)(nil))
	_ = (fs.NodeMkdirer)((*volumeNode)(nil))
	_ = (fs.NodeRmdirer)((*volumeNode)(nil))
	_ = (fs.NodeCreater)((*volumeNode)(nil))
	_ = (fs.NodeSymlinker)((*volumeNode)(nil))
	_ = (fs.NodeRenamer)((*volumeNode)(nil))
	_ = (fs.NodeUnlinker)((*volumeNode)(nil))
)

// dirMode is what every directory reports: the volume's root, so that any
// user in the sandbox can mkdir an exec root, and the exec roots, so that
// the action can write its outputs. The bridge ORs in S_IFDIR.
const dirMode = 0o777

// owner is the uid and gid an entry reports. They start as the mount's
// (root) and change when a chown sets them.
type owner struct {
	mu       sync.Mutex
	uid, gid uint32
}

func (o *owner) get(out *fuse.Attr) {
	o.mu.Lock()
	defer o.mu.Unlock()
	out.Uid, out.Gid = o.uid, o.gid
}

func (o *owner) set(in *fuse.SetAttrIn) {
	o.mu.Lock()
	defer o.mu.Unlock()
	if uid, ok := in.GetUID(); ok {
		o.uid = uid
	}
	if gid, ok := in.GetGID(); ok {
		o.gid = gid
	}
}

func (v *volumeNode) Getattr(ctx context.Context, fh fs.FileHandle, out *fuse.AttrOut) syscall.Errno {
	out.Mode = dirMode
	return 0
}

func (v *volumeNode) Mkdir(ctx context.Context, name string, mode uint32, out *fuse.EntryOut) (*fs.Inode, syscall.Errno) {
	d, err := ParseExecRootName(name)
	if err != nil {
		return nil, syscall.EINVAL
	}
	if v.GetChild(name) != nil {
		return nil, syscall.EEXIST
	}
	var t *tree.Tree
	if d.GetSizeBytes() == 0 {
		// The empty Directory is well known and needs no fetch.
		t = &tree.Tree{Root: d, Dirs: map[string]*repb.Directory{digest.Key(d): {}}}
	} else {
		// Detach from the caller: the loaded tree outlives this mkdir.
		t, err = tree.Load(context.WithoutCancel(ctx), v.fetcher, v.instance, d)
		if err != nil {
			slog.Error("casfs: loading input root", "digest", digest.Key(d), "err", err)
			return nil, syscall.ENOENT
		}
	}
	root := &dirNode{fsys: &casfs{tree: t, fetcher: v.fetcher, instance: v.instance}, digest: d}
	return v.NewPersistentInode(ctx, root, fs.StableAttr{Mode: syscall.S_IFDIR}), 0
}

// Rmdir drops an exec root with everything in it. A runner is done with the
// whole tree at once, and removing lazily hydrated entries one by one would
// only cost lookups.
func (v *volumeNode) Rmdir(ctx context.Context, name string) syscall.Errno {
	child := v.GetChild(name)
	if child == nil {
		return syscall.ENOENT
	}
	if !child.IsDir() {
		return syscall.ENOTDIR
	}
	return 0
}

func (v *volumeNode) Create(context.Context, string, uint32, uint32, *fuse.EntryOut) (*fs.Inode, fs.FileHandle, uint32, syscall.Errno) {
	return nil, nil, 0, syscall.EPERM
}

func (v *volumeNode) Symlink(context.Context, string, string, *fuse.EntryOut) (*fs.Inode, syscall.Errno) {
	return nil, syscall.EPERM
}

func (v *volumeNode) Rename(context.Context, string, fs.InodeEmbedder, string, uint32) syscall.Errno {
	return syscall.EPERM
}

func (v *volumeNode) Unlink(context.Context, string) syscall.Errno {
	return syscall.EPERM
}

// dirNode is a directory. One that came from the tree fills its children
// from its Directory proto when it is added; one created through the mount
// starts empty. The mutation methods only check preconditions and build new
// inodes: go-fuse's bridge adds, removes, and moves the children itself once
// they return success.
type dirNode struct {
	fs.Inode
	owner
	fsys   *casfs
	digest *repb.Digest
}

var (
	_ = (fs.NodeOnAdder)((*dirNode)(nil))
	_ = (fs.NodeGetattrer)((*dirNode)(nil))
	_ = (fs.NodeSetattrer)((*dirNode)(nil))
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
		mode := uint32(0o666)
		if n.GetIsExecutable() {
			mode = 0o777
		}
		child := d.NewPersistentInode(ctx, &fileNode{fsys: d.fsys, source: n.GetDigest(), mode: mode}, fs.StableAttr{Mode: syscall.S_IFREG})
		d.AddChild(n.GetName(), child, true)
	}
	for _, n := range dir.GetSymlinks() {
		child := d.NewPersistentInode(ctx, newSymlink(n.GetTarget()), fs.StableAttr{Mode: syscall.S_IFLNK})
		d.AddChild(n.GetName(), child, true)
	}
}

func (d *dirNode) Getattr(ctx context.Context, fh fs.FileHandle, out *fuse.AttrOut) syscall.Errno {
	out.Mode = dirMode
	d.get(&out.Attr)
	return 0
}

// Setattr accepts a chown and ignores a chmod: directories stay open to
// everyone.
func (d *dirNode) Setattr(ctx context.Context, fh fs.FileHandle, in *fuse.SetAttrIn, out *fuse.AttrOut) syscall.Errno {
	d.set(in)
	return d.Getattr(ctx, fh, out)
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
	f := &fileNode{fsys: d.fsys, hydrated: true, mode: fileMode(mode)}
	return d.NewPersistentInode(ctx, f, fs.StableAttr{Mode: syscall.S_IFREG}), nil, fuse.FOPEN_KEEP_CACHE, 0
}

func (d *dirNode) Symlink(ctx context.Context, target, name string, out *fuse.EntryOut) (*fs.Inode, syscall.Errno) {
	if d.GetChild(name) != nil {
		return nil, syscall.EEXIST
	}
	return d.NewPersistentInode(ctx, newSymlink(target), fs.StableAttr{Mode: syscall.S_IFLNK}), 0
}

// symlinkNode is a symbolic link that accepts a chown.
type symlinkNode struct {
	fs.MemSymlink
	owner
}

var _ = (fs.NodeSetattrer)((*symlinkNode)(nil))

func newSymlink(target string) *symlinkNode {
	return &symlinkNode{MemSymlink: fs.MemSymlink{Data: []byte(target), Attr: fuse.Attr{Mode: 0o777}}}
}

func (l *symlinkNode) Getattr(ctx context.Context, fh fs.FileHandle, out *fuse.AttrOut) syscall.Errno {
	if errno := l.MemSymlink.Getattr(ctx, fh, out); errno != 0 {
		return errno
	}
	l.get(&out.Attr)
	return 0
}

func (l *symlinkNode) Setattr(ctx context.Context, fh fs.FileHandle, in *fuse.SetAttrIn, out *fuse.AttrOut) syscall.Errno {
	l.set(in)
	return l.Getattr(ctx, fh, out)
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
	if _, ok := newParent.(*volumeNode); ok {
		// Only exec roots live at a volume's root.
		return syscall.EPERM
	}
	return 0
}

// fileNode is a file. One from the tree has a source digest and is hydrated
// from the CAS on first open; one created through the mount, or hydrated and
// then written, is plain bytes in memory.
type fileNode struct {
	fs.Inode
	owner
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

// fileMode is the mode a file reports for the mode an action asked for:
// readable and writable by everyone, executable when the action said so.
func fileMode(requested uint32) uint32 {
	return 0o666 | requested&0o111
}

func (f *fileNode) Getattr(ctx context.Context, fh fs.FileHandle, out *fuse.AttrOut) syscall.Errno {
	f.get(&out.Attr)
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
	f.set(in)
	f.get(&out.Attr)
	f.mu.Lock()
	defer f.mu.Unlock()
	if m, ok := in.GetMode(); ok {
		f.mode = fileMode(m)
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

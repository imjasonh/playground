// Package tree moves Remote Execution directory trees between the CAS and a
// filesystem. It loads the Directory protos an action's input root names,
// writes them out as files (or hands them to casfs to serve lazily), and
// turns an output directory back into a Tree and the blobs it needs uploaded.
package tree

import (
	"context"
	"fmt"
	"io/fs"
	"os"
	"path/filepath"
	"slices"
	"strings"

	repb "github.com/bazelbuild/remote-apis/build/bazel/remote/execution/v2"
	"google.golang.org/protobuf/proto"

	"github.com/imjasonh/playground/ci-substrate/internal/digest"
	"github.com/imjasonh/playground/ci-substrate/internal/tenant"
)

// Fetcher reads one blob from the CAS. Both remote.Client and the node-local
// cache client satisfy it.
type Fetcher interface {
	Fetch(ctx context.Context, instanceName string, d *repb.Digest) ([]byte, error)
}

// BatchFetcher is a Fetcher that can also read many blobs in one call. Load
// reads each level of a tree with one FetchBatch when its Fetcher has it.
type BatchFetcher interface {
	Fetcher
	// FetchBatch returns the contents of each of ds, in the order of ds.
	FetchBatch(ctx context.Context, instanceName string, ds []*repb.Digest) ([][]byte, error)
}

// FetchAll reads ds with f's FetchBatch when f is a BatchFetcher, and one
// Fetch at a time when it is not. It returns the contents in the order of
// ds.
func FetchAll(ctx context.Context, f Fetcher, instance string, ds []*repb.Digest) ([][]byte, error) {
	if bf, ok := f.(BatchFetcher); ok {
		return bf.FetchBatch(ctx, instance, ds)
	}
	out := make([][]byte, len(ds))
	for i, d := range ds {
		b, err := f.Fetch(ctx, instance, d)
		if err != nil {
			return nil, fmt.Errorf("fetching %s: %w", digest.Key(d), err)
		}
		out[i] = b
	}
	return out, nil
}

// WithToken returns a BatchFetcher that sends the tenant token on every read
// of f.
// casfs calls Fetch with the kernel's request context, which carries no
// token, so the token travels with the fetcher instead.
func WithToken(f Fetcher, token string) BatchFetcher {
	return tokenFetcher{f: f, token: token}
}

type tokenFetcher struct {
	f     Fetcher
	token string
}

func (t tokenFetcher) Fetch(ctx context.Context, instance string, d *repb.Digest) ([]byte, error) {
	return t.f.Fetch(tenant.Outgoing(ctx, t.token), instance, d)
}

func (t tokenFetcher) FetchBatch(ctx context.Context, instance string, ds []*repb.Digest) ([][]byte, error) {
	return FetchAll(tenant.Outgoing(ctx, t.token), t.f, instance, ds)
}

// Tree is an input root and every Directory reachable from it, keyed by the
// digest key of each Directory.
type Tree struct {
	Root *repb.Digest
	Dirs map[string]*repb.Directory
}

// Load fetches the Directory at root and, transitively, every subdirectory,
// verifying each against its digest. It reads one level of the tree at a
// time, with one FetchAll for the level, so a BatchFetcher reads the tree
// in a few calls per level instead of one per directory. It stops at the
// first malformed or cyclic reference. The empty Directory, whose encoding
// is no bytes, is never fetched.
func Load(ctx context.Context, f Fetcher, instance string, root *repb.Digest) (*Tree, error) {
	t := &Tree{Root: root, Dirs: map[string]*repb.Directory{}}
	if digest.Verify(root, nil) == nil {
		t.Dirs[digest.Key(root)] = &repb.Directory{}
		return t, nil
	}
	level := []*repb.Digest{root}
	for len(level) > 0 {
		var want []*repb.Digest
		seen := map[string]bool{}
		for _, d := range level {
			k := digest.Key(d)
			if _, ok := t.Dirs[k]; ok || seen[k] {
				continue
			}
			seen[k] = true
			want = append(want, d)
		}
		if len(t.Dirs)+len(want) > maxDirectories {
			return nil, fmt.Errorf("input root has more than %d directories", maxDirectories)
		}
		blobs, err := FetchAll(ctx, f, instance, want)
		if err != nil {
			return nil, fmt.Errorf("fetching directories: %w", err)
		}
		level = nil
		for i, d := range want {
			if err := digest.Verify(d, blobs[i]); err != nil {
				return nil, err
			}
			dir := &repb.Directory{}
			if err := proto.Unmarshal(blobs[i], dir); err != nil {
				return nil, fmt.Errorf("directory %s: %w", digest.Key(d), err)
			}
			if err := validate(dir); err != nil {
				return nil, fmt.Errorf("directory %s: %w", digest.Key(d), err)
			}
			t.Dirs[digest.Key(d)] = dir
			for _, sub := range dir.GetDirectories() {
				level = append(level, sub.GetDigest())
			}
		}
	}
	return t, nil
}

// maxDirectories bounds how large a tree the runner will walk, so a malicious
// input root cannot make it allocate without end.
const maxDirectories = 100_000

// materializeBatchBytes bounds the file contents Materialize holds at once.
// A file larger than this is fetched alone.
const materializeBatchBytes = 4 << 20

// validate rejects names that would escape the directory they are in.
func validate(dir *repb.Directory) error {
	for _, n := range dir.GetFiles() {
		if err := validName(n.GetName()); err != nil {
			return err
		}
		if err := digest.Validate(n.GetDigest()); err != nil {
			return fmt.Errorf("file %q: %w", n.GetName(), err)
		}
	}
	for _, n := range dir.GetDirectories() {
		if err := validName(n.GetName()); err != nil {
			return err
		}
		if err := digest.Validate(n.GetDigest()); err != nil {
			return fmt.Errorf("directory %q: %w", n.GetName(), err)
		}
	}
	for _, n := range dir.GetSymlinks() {
		if err := validName(n.GetName()); err != nil {
			return err
		}
		if filepath.IsAbs(n.GetTarget()) {
			return fmt.Errorf("symlink %q: absolute target %q", n.GetName(), n.GetTarget())
		}
	}
	return nil
}

func validName(name string) error {
	if name == "" || name == "." || name == ".." || strings.ContainsAny(name, "/\x00") {
		return fmt.Errorf("invalid node name %q", name)
	}
	return nil
}

// Dir returns the Directory for d, which Load must have fetched.
func (t *Tree) Dir(d *repb.Digest) (*repb.Directory, error) {
	dir, ok := t.Dirs[digest.Key(d)]
	if !ok {
		return nil, fmt.Errorf("directory %s not loaded", digest.Key(d))
	}
	return dir, nil
}

// Materialize writes the tree under dest, fetching every file. This is the
// eager alternative to casfs: every byte is read before the action starts.
func Materialize(ctx context.Context, f Fetcher, instance string, t *Tree, dest string) error {
	return t.materialize(ctx, f, instance, t.Root, dest)
}

func (t *Tree) materialize(ctx context.Context, f Fetcher, instance string, d *repb.Digest, dest string) error {
	dir, err := t.Dir(d)
	if err != nil {
		return err
	}
	if err := os.MkdirAll(dest, 0o755); err != nil {
		return err
	}
	files := dir.GetFiles()
	ds := make([]*repb.Digest, len(files))
	for i, fn := range files {
		ds[i] = fn.GetDigest()
	}
	for _, batch := range digest.Batches(ds, len(ds), materializeBatchBytes) {
		blobs, err := FetchAll(ctx, f, instance, batch)
		if err != nil {
			return fmt.Errorf("fetching files of %s: %w", dest, err)
		}
		for i, fn := range files[:len(batch)] {
			if err := digest.Verify(fn.GetDigest(), blobs[i]); err != nil {
				return err
			}
			mode := os.FileMode(0o644)
			if fn.GetIsExecutable() {
				mode = 0o755
			}
			if err := os.WriteFile(filepath.Join(dest, fn.GetName()), blobs[i], mode); err != nil {
				return err
			}
		}
		files = files[len(batch):]
	}
	for _, n := range dir.GetSymlinks() {
		if err := os.Symlink(n.GetTarget(), filepath.Join(dest, n.GetName())); err != nil {
			return err
		}
	}
	for _, n := range dir.GetDirectories() {
		if err := t.materialize(ctx, f, instance, n.GetDigest(), filepath.Join(dest, n.GetName())); err != nil {
			return err
		}
	}
	return nil
}

// Output is a directory read from disk as a Remote Execution Tree, with the
// file contents the Tree refers to, keyed by digest key, so the caller can
// upload only the blobs the CAS is missing.
type Output struct {
	Tree  *repb.Tree
	Blobs map[string][]byte
}

// FromDir reads dir into an Output. Directories are encoded
// deterministically, so the same contents always yield the same Tree digest.
func FromDir(dir string) (*Output, error) {
	out := &Output{Tree: &repb.Tree{}, Blobs: map[string][]byte{}}
	root, err := out.walk(dir)
	if err != nil {
		return nil, err
	}
	out.Tree.Root = root
	return out, nil
}

func (o *Output) walk(dir string) (*repb.Directory, error) {
	entries, err := os.ReadDir(dir)
	if err != nil {
		return nil, err
	}
	d := &repb.Directory{}
	for _, e := range entries {
		p := filepath.Join(dir, e.Name())
		switch {
		case e.Type()&fs.ModeSymlink != 0:
			target, err := os.Readlink(p)
			if err != nil {
				return nil, err
			}
			d.Symlinks = append(d.Symlinks, &repb.SymlinkNode{Name: e.Name(), Target: target})
		case e.IsDir():
			sub, err := o.walk(p)
			if err != nil {
				return nil, err
			}
			o.Tree.Children = append(o.Tree.Children, sub)
			d.Directories = append(d.Directories, &repb.DirectoryNode{Name: e.Name(), Digest: Digest(sub)})
		default:
			b, err := os.ReadFile(p)
			if err != nil {
				return nil, err
			}
			info, err := e.Info()
			if err != nil {
				return nil, err
			}
			fd := digest.FromBytes(b)
			o.Blobs[digest.Key(fd)] = b
			d.Files = append(d.Files, &repb.FileNode{Name: e.Name(), Digest: fd, IsExecutable: info.Mode()&0o111 != 0})
		}
	}
	slices.SortFunc(d.Files, func(a, b *repb.FileNode) int { return strings.Compare(a.GetName(), b.GetName()) })
	slices.SortFunc(d.Directories, func(a, b *repb.DirectoryNode) int { return strings.Compare(a.GetName(), b.GetName()) })
	slices.SortFunc(d.Symlinks, func(a, b *repb.SymlinkNode) int { return strings.Compare(a.GetName(), b.GetName()) })
	return d, nil
}

// Marshal encodes m deterministically, so equal messages have equal digests.
func Marshal(m proto.Message) []byte {
	b, err := proto.MarshalOptions{Deterministic: true}.Marshal(m)
	if err != nil {
		// Only an unmarshalable message type gets here, which is a bug in
		// the caller, not a condition to handle.
		panic(err)
	}
	return b
}

// Digest is the digest of m's deterministic encoding.
func Digest(m proto.Message) *repb.Digest {
	return digest.FromBytes(Marshal(m))
}

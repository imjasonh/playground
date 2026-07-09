package layer

import (
	"archive/tar"
	"bytes"
	"compress/gzip"
	"crypto/sha256"
	"encoding/hex"
	"fmt"
	"io"
	"io/fs"
	"os"
	"path/filepath"
	"sort"
	"strings"
	"time"
)

// Epoch is the fixed mtime used for deterministic tarballs.
var Epoch = time.Unix(0, 0).UTC()

// File is a regular file, directory, or symlink to include in a layer.
//
// Regular file contents come from either Body (small / tests) or DiskPath
// (streamed from disk — preferred for real packages so we never buffer the
// whole tree in memory).
type File struct {
	// Rel is the path inside the layer (forward slashes, no leading slash).
	Rel string
	// Mode is the file mode bits (type + perms). For symlinks, type should be fs.ModeSymlink.
	Mode fs.FileMode
	// Body is in-memory file contents (ignored for symlinks/dirs; ignored if DiskPath is set).
	Body []byte
	// DiskPath, when set, is opened and streamed into the tar (preferred over Body).
	DiskPath string
	// Link is the symlink target (only for symlinks).
	Link string
}

// DiffID returns the sha256 of the uncompressed tar (OCI diff_id).
func DiffID(files []File) (string, error) {
	h := sha256.New()
	if err := WriteTar(h, files); err != nil {
		return "", err
	}
	return "sha256:" + hex.EncodeToString(h.Sum(nil)), nil
}

// CompressedDigest streams tar→gzip through a hasher and returns the compressed
// digest and size. The compressed bytes are NOT retained — callers that need the
// blob should stream via WriteCompressed or publish.LayerFromFiles.
func CompressedDigest(files []File) (digest string, size int64, err error) {
	h := sha256.New()
	cw := &countingWriter{w: h}
	if err := WriteCompressed(cw, files); err != nil {
		return "", 0, err
	}
	return "sha256:" + hex.EncodeToString(h.Sum(nil)), cw.n, nil
}

// CompressedDigestBytes is like CompressedDigest but also returns the compressed
// blob. Prefer streaming APIs for real builds; this exists for small unit tests.
func CompressedDigestBytes(files []File) (digest string, size int64, compressed []byte, err error) {
	var buf bytes.Buffer
	if err := WriteCompressed(&buf, files); err != nil {
		return "", 0, nil, err
	}
	out := buf.Bytes()
	sum := sha256.Sum256(out)
	return "sha256:" + hex.EncodeToString(sum[:]), int64(len(out)), out, nil
}

// WriteCompressed writes a deterministic gzip-compressed tar of files to w.
func WriteCompressed(w io.Writer, files []File) error {
	zw := gzip.NewWriter(w)
	zw.Header.ModTime = Epoch
	zw.Header.Name = ""
	zw.Header.OS = 255
	if err := WriteTar(zw, files); err != nil {
		_ = zw.Close()
		return err
	}
	return zw.Close()
}

// FromDir walks root and returns deterministic Files with paths relative to
// root, prefixed with prefix (e.g. "app"). Symlinks are preserved.
// Regular file contents are referenced by DiskPath (not loaded into memory).
func FromDir(root, prefix string) ([]File, error) {
	var files []File
	err := filepath.WalkDir(root, func(path string, d fs.DirEntry, err error) error {
		if err != nil {
			return err
		}
		rel, err := filepath.Rel(root, path)
		if err != nil {
			return err
		}
		if rel == "." {
			return nil
		}
		rel = filepath.ToSlash(rel)
		name := rel
		if prefix != "" {
			name = strings.TrimSuffix(prefix, "/") + "/" + rel
		}
		info, err := d.Info()
		if err != nil {
			return err
		}
		if d.Type()&fs.ModeSymlink != 0 {
			target, err := os.Readlink(path)
			if err != nil {
				return err
			}
			files = append(files, File{
				Rel:  name,
				Mode: fs.ModeSymlink | 0o777,
				Link: filepath.ToSlash(target),
			})
			return nil
		}
		if d.IsDir() {
			files = append(files, File{
				Rel:  name,
				Mode: fs.ModeDir | 0o755,
			})
			return nil
		}
		if !d.Type().IsRegular() {
			return fmt.Errorf("unsupported file type %s: %s", d.Type(), path)
		}
		mode := info.Mode().Perm()
		if mode&0o111 != 0 {
			mode = 0o755
		} else {
			mode = 0o644
		}
		files = append(files, File{
			Rel:      name,
			Mode:     mode,
			DiskPath: path,
		})
		return nil
	})
	if err != nil {
		return nil, err
	}
	sortFiles(files)
	return files, nil
}

// WriteTar writes a deterministic uncompressed tar of files to w.
// File bodies are streamed from DiskPath when set.
func WriteTar(w io.Writer, files []File) error {
	files = append([]File(nil), files...)
	sortFiles(files)
	tw := tar.NewWriter(w)
	defer tw.Close()

	seenDirs := map[string]struct{}{}
	for _, f := range files {
		if err := ensureParentDirs(tw, f.Rel, seenDirs); err != nil {
			return err
		}
		switch {
		case f.Mode.IsDir():
			hdr := &tar.Header{
				Name:     strings.TrimSuffix(f.Rel, "/") + "/",
				Mode:     0o755,
				Typeflag: tar.TypeDir,
				ModTime:  Epoch,
				Uid:      0,
				Gid:      0,
			}
			if err := tw.WriteHeader(hdr); err != nil {
				return err
			}
			seenDirs[strings.TrimSuffix(f.Rel, "/")] = struct{}{}
		case f.Mode&fs.ModeSymlink != 0:
			hdr := &tar.Header{
				Name:     f.Rel,
				Mode:     0o777,
				Typeflag: tar.TypeSymlink,
				Linkname: f.Link,
				ModTime:  Epoch,
				Uid:      0,
				Gid:      0,
			}
			if err := tw.WriteHeader(hdr); err != nil {
				return err
			}
		default:
			size, err := fileSize(f)
			if err != nil {
				return err
			}
			hdr := &tar.Header{
				Name:     f.Rel,
				Mode:     int64(f.Mode.Perm()),
				Typeflag: tar.TypeReg,
				Size:     size,
				ModTime:  Epoch,
				Uid:      0,
				Gid:      0,
			}
			if err := tw.WriteHeader(hdr); err != nil {
				return err
			}
			if err := copyFileBody(tw, f); err != nil {
				return err
			}
		}
	}
	return tw.Close()
}

func fileSize(f File) (int64, error) {
	if f.DiskPath != "" {
		st, err := os.Stat(f.DiskPath)
		if err != nil {
			return 0, err
		}
		return st.Size(), nil
	}
	return int64(len(f.Body)), nil
}

func copyFileBody(w io.Writer, f File) error {
	if f.DiskPath != "" {
		in, err := os.Open(f.DiskPath)
		if err != nil {
			return err
		}
		defer in.Close()
		_, err = io.Copy(w, in)
		return err
	}
	_, err := w.Write(f.Body)
	return err
}

func ensureParentDirs(tw *tar.Writer, rel string, seen map[string]struct{}) error {
	parts := strings.Split(rel, "/")
	if len(parts) <= 1 {
		return nil
	}
	cur := ""
	for _, p := range parts[:len(parts)-1] {
		if cur == "" {
			cur = p
		} else {
			cur += "/" + p
		}
		if _, ok := seen[cur]; ok {
			continue
		}
		hdr := &tar.Header{
			Name:     cur + "/",
			Mode:     0o755,
			Typeflag: tar.TypeDir,
			ModTime:  Epoch,
			Uid:      0,
			Gid:      0,
		}
		if err := tw.WriteHeader(hdr); err != nil {
			return err
		}
		seen[cur] = struct{}{}
	}
	return nil
}

func sortFiles(files []File) {
	sort.Slice(files, func(i, j int) bool {
		return files[i].Rel < files[j].Rel
	})
}

type countingWriter struct {
	w io.Writer
	n int64
}

func (c *countingWriter) Write(p []byte) (int, error) {
	n, err := c.w.Write(p)
	c.n += int64(n)
	return n, err
}

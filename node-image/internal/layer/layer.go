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

// File is a regular file or symlink to include in a layer.
type File struct {
	// Rel is the path inside the layer (forward slashes, no leading slash).
	Rel string
	// Mode is the file mode bits (type + perms). For symlinks, type should be fs.ModeSymlink.
	Mode fs.FileMode
	// Body is file contents (ignored for symlinks).
	Body []byte
	// Link is the symlink target (only for symlinks).
	Link string
}

// DiffID returns the sha256 of the uncompressed tar (OCI diff_id).
func DiffID(files []File) (string, error) {
	var buf bytes.Buffer
	if err := writeTar(&buf, files); err != nil {
		return "", err
	}
	sum := sha256.Sum256(buf.Bytes())
	return "sha256:" + hex.EncodeToString(sum[:]), nil
}

// CompressedDigest returns the sha256 of the gzip-compressed tar (OCI layer digest)
// and the compressed size.
func CompressedDigest(files []File) (digest string, size int64, compressed []byte, err error) {
	var raw bytes.Buffer
	if err := writeTar(&raw, files); err != nil {
		return "", 0, nil, err
	}
	var gz bytes.Buffer
	zw := gzip.NewWriter(&gz)
	// Deterministic gzip header: zero mtime, no name.
	zw.Header.ModTime = Epoch
	zw.Header.Name = ""
	zw.Header.OS = 255 // unknown, stable across Go versions historically varies; pin
	if _, err := io.Copy(zw, &raw); err != nil {
		_ = zw.Close()
		return "", 0, nil, err
	}
	if err := zw.Close(); err != nil {
		return "", 0, nil, err
	}
	out := gz.Bytes()
	sum := sha256.Sum256(out)
	return "sha256:" + hex.EncodeToString(sum[:]), int64(len(out)), out, nil
}

// FromDir walks root and returns deterministic Files with paths relative to
// root, prefixed with prefix (e.g. "app"). Symlinks are preserved.
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
		body, err := os.ReadFile(path)
		if err != nil {
			return err
		}
		mode := info.Mode().Perm()
		if mode&0o111 != 0 {
			mode = 0o755
		} else {
			mode = 0o644
		}
		files = append(files, File{
			Rel:  name,
			Mode: mode,
			Body: body,
		})
		return nil
	})
	if err != nil {
		return nil, err
	}
	sortFiles(files)
	return files, nil
}

func writeTar(w io.Writer, files []File) error {
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
			hdr := &tar.Header{
				Name:     f.Rel,
				Mode:     int64(f.Mode.Perm()),
				Typeflag: tar.TypeReg,
				Size:     int64(len(f.Body)),
				ModTime:  Epoch,
				Uid:      0,
				Gid:      0,
			}
			if err := tw.WriteHeader(hdr); err != nil {
				return err
			}
			if _, err := tw.Write(f.Body); err != nil {
				return err
			}
		}
	}
	return tw.Close()
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

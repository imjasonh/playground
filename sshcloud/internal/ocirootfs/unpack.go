package ocirootfs

import (
	"archive/tar"
	"fmt"
	"io"
	"os"
	"path"
	"strings"

	v1 "github.com/google/go-containerregistry/pkg/v1"
	"github.com/google/go-containerregistry/pkg/v1/types"
)

const (
	whiteoutPrefix   = ".wh."
	opaqueWhiteout   = ".wh..wh..opq"
	maxUnpackEntries = 100_000
)

// Unpack applies img layers in order into destDir, honoring OCI whiteouts.
// Uncompressed file bytes written must not exceed maxBytes (required, > 0).
func Unpack(img v1.Image, destDir string, maxBytes int64) error {
	if destDir == "" {
		return fmt.Errorf("dest dir required")
	}
	if maxBytes <= 0 {
		return fmt.Errorf("max uncompressed bytes must be positive")
	}
	if err := os.MkdirAll(destDir, 0o755); err != nil {
		return err
	}
	root, err := os.OpenRoot(destDir)
	if err != nil {
		return fmt.Errorf("open unpack root: %w", err)
	}
	defer root.Close()

	cfg, err := img.ConfigFile()
	if err != nil {
		return fmt.Errorf("image config: %w", err)
	}
	if cfg != nil && strings.EqualFold(strings.TrimSpace(cfg.OS), "windows") {
		return fmt.Errorf("windows images are not supported")
	}

	layers, err := img.Layers()
	if err != nil {
		return fmt.Errorf("image layers: %w", err)
	}

	var written, entries int64
	for i, layer := range layers {
		mt, err := layer.MediaType()
		if err == nil && skipLayerMediaType(mt) {
			continue
		}
		if err := applyLayer(layer, root, maxBytes, &written, &entries); err != nil {
			return fmt.Errorf("layer %d: %w", i, err)
		}
	}
	return nil
}

func skipLayerMediaType(mt types.MediaType) bool {
	s := strings.ToLower(string(mt))
	if strings.Contains(s, "foreign") || strings.Contains(s, "nondistributable") {
		return true
	}
	return strings.Contains(s, "windows")
}

func applyLayer(layer v1.Layer, root *os.Root, maxBytes int64, written, entries *int64) error {
	opaque, whiteouts, err := scanWhiteouts(layer, maxBytes-*written, entries)
	if err != nil {
		return err
	}
	for _, dir := range opaque {
		if err := clearDir(root, dir); err != nil {
			return err
		}
	}
	for _, target := range whiteouts {
		if err := root.RemoveAll(target); err != nil {
			return err
		}
	}

	rc, err := layer.Uncompressed()
	if err != nil {
		return fmt.Errorf("uncompress: %w", err)
	}
	defer rc.Close()

	tr := tar.NewReader(rc)
	for {
		hdr, err := tr.Next()
		if err == io.EOF {
			break
		}
		if err != nil {
			return fmt.Errorf("read tar: %w", err)
		}
		name, err := sanitizeTarName(hdr.Name)
		if err != nil {
			return err
		}
		if name == "." {
			continue
		}
		base := path.Base(name)
		if base == opaqueWhiteout || strings.HasPrefix(base, whiteoutPrefix) {
			continue
		}
		if err := extractEntry(root, hdr, name, tr, maxBytes, written); err != nil {
			return err
		}
	}
	if _, err := io.Copy(io.Discard, rc); err != nil {
		return fmt.Errorf("verify layer: %w", err)
	}
	return nil
}

func scanWhiteouts(layer v1.Layer, remainingBytes int64, entries *int64) (opaque, whiteouts []string, err error) {
	rc, err := layer.Uncompressed()
	if err != nil {
		return nil, nil, fmt.Errorf("uncompress: %w", err)
	}
	defer rc.Close()

	tr := tar.NewReader(rc)
	for {
		hdr, err := tr.Next()
		if err == io.EOF {
			break
		}
		if err != nil {
			return nil, nil, fmt.Errorf("read tar: %w", err)
		}
		*entries++
		if *entries > maxUnpackEntries {
			return nil, nil, fmt.Errorf("unpack exceeds %d entry limit", maxUnpackEntries)
		}
		if hdr.Size < 0 {
			return nil, nil, fmt.Errorf("negative file size for %q", hdr.Name)
		}
		if hdr.Typeflag == tar.TypeReg || hdr.Typeflag == tar.TypeRegA {
			remainingBytes -= hdr.Size
			if remainingBytes < 0 {
				return nil, nil, fmt.Errorf("uncompressed unpack exceeds byte limit")
			}
		}
		name, err := sanitizeTarName(hdr.Name)
		if err != nil {
			return nil, nil, err
		}
		base := path.Base(name)
		dir := path.Dir(name)
		if dir == "." {
			dir = ""
		}
		switch {
		case base == opaqueWhiteout:
			opaque = append(opaque, dir)
		case strings.HasPrefix(base, whiteoutPrefix):
			leaf := strings.TrimPrefix(base, whiteoutPrefix)
			if leaf == "" || leaf == "." || leaf == ".." {
				return nil, nil, fmt.Errorf("invalid whiteout %q", name)
			}
			target, err := sanitizeTarName(path.Join(dir, leaf))
			if err != nil {
				return nil, nil, err
			}
			whiteouts = append(whiteouts, target)
		}
	}
	return opaque, whiteouts, nil
}

func extractEntry(root *os.Root, hdr *tar.Header, name string, r io.Reader, maxBytes int64, written *int64) error {
	mode := hdr.FileInfo().Mode()
	permissions := entryMode(mode)

	switch hdr.Typeflag {
	case tar.TypeDir:
		if st, err := root.Lstat(name); err == nil && !st.IsDir() {
			if err := root.RemoveAll(name); err != nil {
				return err
			}
		}
		if err := root.MkdirAll(name, dirPerm(mode).Perm()); err != nil {
			return err
		}
		return root.Chmod(name, permissions)
	case tar.TypeReg, tar.TypeRegA:
		if hdr.Size < 0 {
			return fmt.Errorf("negative file size for %q", name)
		}
		if *written+hdr.Size > maxBytes {
			return fmt.Errorf("uncompressed unpack exceeds %d byte limit", maxBytes)
		}
		if err := root.MkdirAll(path.Dir(name), 0o755); err != nil {
			return err
		}
		if err := root.RemoveAll(name); err != nil {
			return err
		}
		if err := writeFile(root, name, r, hdr.Size, permissions); err != nil {
			return err
		}
		*written += hdr.Size
		return nil
	case tar.TypeSymlink:
		if err := root.MkdirAll(path.Dir(name), 0o755); err != nil {
			return err
		}
		if err := root.RemoveAll(name); err != nil {
			return err
		}
		return root.Symlink(hdr.Linkname, name)
	case tar.TypeLink:
		target, err := sanitizeTarName(hdr.Linkname)
		if err != nil {
			return err
		}
		if target == "." {
			return fmt.Errorf("invalid hard-link target %q", hdr.Linkname)
		}
		if err := root.MkdirAll(path.Dir(name), 0o755); err != nil {
			return err
		}
		if err := root.RemoveAll(name); err != nil {
			return err
		}
		return root.Link(target, name)
	default:
		return nil
	}
}

func writeFile(root *os.Root, name string, r io.Reader, size int64, perm os.FileMode) error {
	f, err := root.OpenFile(name, os.O_CREATE|os.O_EXCL|os.O_WRONLY, perm.Perm())
	if err != nil {
		return err
	}
	if _, err := io.CopyN(f, r, size); err != nil {
		_ = f.Close()
		return err
	}
	if err := f.Close(); err != nil {
		return err
	}
	return root.Chmod(name, perm)
}

func dirPerm(mode os.FileMode) os.FileMode {
	p := entryMode(mode)
	if p == 0 {
		return 0o755
	}
	return p
}

func entryMode(mode os.FileMode) os.FileMode {
	return mode.Perm() | mode&(os.ModeSetuid|os.ModeSetgid|os.ModeSticky)
}

func clearDir(root *os.Root, dir string) error {
	if dir == "" {
		dir = "."
	}
	f, err := root.Open(dir)
	if err != nil {
		if os.IsNotExist(err) {
			return root.MkdirAll(dir, 0o755)
		}
		return err
	}
	entries, readErr := f.ReadDir(-1)
	closeErr := f.Close()
	if readErr != nil {
		return readErr
	}
	if closeErr != nil {
		return closeErr
	}
	for _, e := range entries {
		if err := root.RemoveAll(path.Join(dir, e.Name())); err != nil {
			return err
		}
	}
	return nil
}

func sanitizeTarName(raw string) (string, error) {
	name := path.Clean(strings.TrimPrefix(raw, "./"))
	name = strings.TrimPrefix(name, "/")
	if name == ".." || strings.HasPrefix(name, "../") {
		return "", fmt.Errorf("unsafe tar path %q", raw)
	}
	if name == "." || name == "" {
		return ".", nil
	}
	return name, nil
}

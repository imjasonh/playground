package ocirootfs

import (
	"archive/tar"
	"fmt"
	"io"
	"os"
	"path"
	"path/filepath"
	"strings"

	v1 "github.com/google/go-containerregistry/pkg/v1"
	"github.com/google/go-containerregistry/pkg/v1/types"
)

const (
	whiteoutPrefix = ".wh."
	opaqueWhiteout = ".wh..wh..opq"
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

	var written int64
	for i, layer := range layers {
		mt, err := layer.MediaType()
		if err == nil && skipLayerMediaType(mt) {
			continue
		}
		if err := applyLayer(layer, destDir, maxBytes, &written); err != nil {
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

func applyLayer(layer v1.Layer, destDir string, maxBytes int64, written *int64) error {
	opaque, whiteouts, err := scanWhiteouts(layer)
	if err != nil {
		return err
	}
	for _, dir := range opaque {
		full, err := safeJoin(destDir, dir)
		if err != nil {
			return err
		}
		if err := clearDir(full); err != nil {
			return err
		}
	}
	for _, target := range whiteouts {
		full, err := safeJoin(destDir, target)
		if err != nil {
			return err
		}
		if err := os.RemoveAll(full); err != nil {
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
		if err := extractEntry(destDir, hdr, name, tr, maxBytes, written); err != nil {
			return err
		}
	}
	if _, err := io.Copy(io.Discard, rc); err != nil {
		return fmt.Errorf("verify layer: %w", err)
	}
	return nil
}

func scanWhiteouts(layer v1.Layer) (opaque, whiteouts []string, err error) {
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
			target := path.Join(dir, strings.TrimPrefix(base, whiteoutPrefix))
			whiteouts = append(whiteouts, target)
		}
	}
	return opaque, whiteouts, nil
}

func extractEntry(destDir string, hdr *tar.Header, name string, r io.Reader, maxBytes int64, written *int64) error {
	full, err := safeJoin(destDir, name)
	if err != nil {
		return err
	}
	mode := hdr.FileInfo().Mode()

	switch hdr.Typeflag {
	case tar.TypeDir:
		return os.MkdirAll(full, dirPerm(mode))
	case tar.TypeReg, tar.TypeRegA:
		if hdr.Size < 0 {
			return fmt.Errorf("negative file size for %q", name)
		}
		if *written+hdr.Size > maxBytes {
			return fmt.Errorf("uncompressed unpack exceeds %d byte limit", maxBytes)
		}
		if err := os.MkdirAll(filepath.Dir(full), 0o755); err != nil {
			return err
		}
		if err := writeFile(full, r, hdr.Size, mode.Perm()); err != nil {
			return err
		}
		*written += hdr.Size
		return nil
	case tar.TypeSymlink:
		if err := os.MkdirAll(filepath.Dir(full), 0o755); err != nil {
			return err
		}
		_ = os.RemoveAll(full)
		return os.Symlink(hdr.Linkname, full)
	case tar.TypeLink:
		target, err := safeJoin(destDir, path.Clean(hdr.Linkname))
		if err != nil {
			return err
		}
		if err := os.MkdirAll(filepath.Dir(full), 0o755); err != nil {
			return err
		}
		_ = os.RemoveAll(full)
		return os.Link(target, full)
	default:
		return nil
	}
}

func writeFile(path string, r io.Reader, size int64, perm os.FileMode) error {
	f, err := os.OpenFile(path, os.O_CREATE|os.O_TRUNC|os.O_WRONLY, perm)
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
	return os.Chmod(path, perm)
}

func dirPerm(mode os.FileMode) os.FileMode {
	p := mode.Perm()
	if p == 0 {
		return 0o755
	}
	return p
}

func clearDir(dir string) error {
	if dir == "" {
		return fmt.Errorf("clearDir: empty path")
	}
	entries, err := os.ReadDir(dir)
	if err != nil {
		if os.IsNotExist(err) {
			return os.MkdirAll(dir, 0o755)
		}
		return err
	}
	for _, e := range entries {
		if err := os.RemoveAll(filepath.Join(dir, e.Name())); err != nil {
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

func safeJoin(root, rel string) (string, error) {
	rel = path.Clean(strings.TrimPrefix(rel, "/"))
	if rel == ".." || strings.HasPrefix(rel, "../") {
		return "", fmt.Errorf("unsafe path %q", rel)
	}
	root = filepath.Clean(root)
	if rel == "." || rel == "" {
		return root, nil
	}
	full := filepath.Join(root, filepath.FromSlash(rel))
	prefix := root + string(os.PathSeparator)
	if full != root && !strings.HasPrefix(full, prefix) {
		return "", fmt.Errorf("unsafe path %q", rel)
	}
	return full, nil
}

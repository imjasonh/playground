package layout

import (
	"crypto/sha512"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"io"
	"io/fs"
	"os"
	"path/filepath"
	"strings"

	"github.com/imjasonh/playground/node-image/internal/layer"
)

// SpoolLocalPackage copies a workspace/directory package into the spool under
// key (typically "local-<contenthash>"). Excludes node_modules, VCS, and
// common junk. Returns the absolute package directory in the spool.
//
// contentSHA512, when non-empty, is the precomputed hashTree result (from
// LocalContentKeyAndHash). Passing it avoids a second full tree walk on the
// warm path — the biggest local-package win.
func SpoolLocalPackage(spoolRoot, key, srcDir string) (pkgDir string, err error) {
	return SpoolLocalPackageHash(spoolRoot, key, srcDir, "")
}

// SpoolLocalPackageHash is SpoolLocalPackage with an optional precomputed
// content SHA-512 hex digest.
func SpoolLocalPackageHash(spoolRoot, key, srcDir, contentSHA512 string) (pkgDir string, err error) {
	if key == "" {
		return "", fmt.Errorf("empty spool key for local package")
	}
	if err := os.MkdirAll(spoolRoot, 0o700); err != nil {
		return "", err
	}
	pkgDir = filepath.Join(spoolRoot, key)
	metaPath := filepath.Join(pkgDir, spoolMetaName)
	srcAbs, err := filepath.Abs(srcDir)
	if err != nil {
		return "", err
	}
	sum := contentSHA512
	if sum == "" {
		sum, err = hashTree(srcAbs)
		if err != nil {
			return "", err
		}
	}
	if st, err := os.Stat(pkgDir); err == nil && st.IsDir() {
		if b, err := os.ReadFile(metaPath); err == nil {
			var meta spoolMeta
			if json.Unmarshal(b, &meta) == nil && meta.IntegrityKey == key && meta.TarballSHA512 == sum {
				if err := assertSafeSpoolTree(pkgDir); err == nil {
					return pkgDir, nil
				}
			}
		}
		_ = os.RemoveAll(pkgDir)
	}

	tmp, err := os.MkdirTemp(spoolRoot, "spool-local-*.tmp")
	if err != nil {
		return "", err
	}
	defer os.RemoveAll(tmp)

	if err := copyPackageTree(srcAbs, tmp); err != nil {
		return "", err
	}
	if err := assertSafeSpoolTree(tmp); err != nil {
		return "", fmt.Errorf("local package spool unsafe: %w", err)
	}
	meta := spoolMeta{
		IntegrityKey:  key,
		TarballSHA512: sum,
	}
	b, err := json.Marshal(meta)
	if err != nil {
		return "", err
	}
	if err := os.WriteFile(filepath.Join(tmp, spoolMetaName), append(b, '\n'), 0o600); err != nil {
		return "", err
	}
	_ = os.RemoveAll(pkgDir)
	if err := os.Rename(tmp, pkgDir); err != nil {
		return "", err
	}
	return pkgDir, nil
}

// LocalContentKey returns a stable spool key for a local package directory.
func LocalContentKey(srcDir string) (string, error) {
	key, _, err := LocalContentKeyAndHash(srcDir)
	return key, err
}

// LocalContentKeyAndHash returns the spool key and full sha512 hex in one walk.
func LocalContentKeyAndHash(srcDir string) (key, sha512hex string, err error) {
	sum, err := hashTree(srcDir)
	if err != nil {
		return "", "", err
	}
	return "local-" + sum[:32], sum, nil
}

func hashTree(root string) (string, error) {
	h := sha512.New()
	err := filepath.Walk(root, func(path string, info os.FileInfo, err error) error {
		if err != nil {
			return err
		}
		rel, err := filepath.Rel(root, path)
		if err != nil {
			return err
		}
		rel = filepath.ToSlash(rel)
		if info.IsDir() {
			base := info.Name()
			if base == "node_modules" || base == ".git" || base == ".hg" || base == "dist" && rel != "." {
				// Keep dist/ — workspace packages may ship built output.
				// Only skip VCS and node_modules.
			}
			if base == "node_modules" || base == ".git" || base == ".hg" {
				return filepath.SkipDir
			}
			_, _ = io.WriteString(h, "D:"+rel+"\n")
			return nil
		}
		if info.Mode()&os.ModeSymlink != 0 {
			return nil
		}
		_, _ = io.WriteString(h, "F:"+rel+":")
		f, err := os.Open(path)
		if err != nil {
			return err
		}
		_, copyErr := io.Copy(h, f)
		_ = f.Close()
		_, _ = io.WriteString(h, "\n")
		return copyErr
	})
	if err != nil {
		return "", err
	}
	return hex.EncodeToString(h.Sum(nil)), nil
}

func copyPackageTree(src, dst string) error {
	return filepath.Walk(src, func(path string, info os.FileInfo, err error) error {
		if err != nil {
			return err
		}
		rel, err := filepath.Rel(src, path)
		if err != nil {
			return err
		}
		if info.IsDir() {
			base := info.Name()
			if base == "node_modules" || base == ".git" || base == ".hg" {
				return filepath.SkipDir
			}
			return os.MkdirAll(filepath.Join(dst, rel), 0o755)
		}
		if info.Mode()&os.ModeSymlink != 0 {
			return nil // skip symlinks in workspace packages
		}
		if rel == "." {
			return nil
		}
		target := filepath.Join(dst, rel)
		if err := os.MkdirAll(filepath.Dir(target), 0o755); err != nil {
			return err
		}
		return copyFile(path, target, info.Mode())
	})
}

func copyFile(src, dst string, mode fs.FileMode) error {
	in, err := os.Open(src)
	if err != nil {
		return err
	}
	defer in.Close()
	out, err := os.OpenFile(dst, os.O_CREATE|os.O_WRONLY|os.O_TRUNC, mode.Perm())
	if err != nil {
		return err
	}
	_, copyErr := io.Copy(out, in)
	closeErr := out.Close()
	if copyErr != nil {
		return copyErr
	}
	return closeErr
}

// FilterSpoolMeta removes spool metadata files from a file list (they must not
// appear in OCI layers).
func FilterSpoolMeta(files []layer.File) []layer.File {
	out := files[:0]
	for _, f := range files {
		base := pathBase(f.Rel)
		if base == spoolMetaName || base == ".node-image-spool-ok" {
			continue
		}
		out = append(out, f)
	}
	return out
}

func pathBase(rel string) string {
	if i := strings.LastIndex(rel, "/"); i >= 0 {
		return rel[i+1:]
	}
	return rel
}

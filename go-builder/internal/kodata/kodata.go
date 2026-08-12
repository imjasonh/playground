// Package kodata bundles ko's kodata/ static assets into a launch layer.
package kodata

import (
	"fmt"
	"io"
	"io/fs"
	"os"
	"path/filepath"
	"strings"
)

const (
	// DirName is the magic directory name ko looks for next to the main package.
	DirName = "kodata"
	// RuntimeRoot is ko's default path inside the image ($KO_DATA_PATH).
	RuntimeRoot = "/var/run/ko"
)

// Find returns the absolute path of kodata/ for the main package, or "".
// mainPkg is a relative package path like "." or "./cmd/app".
func Find(appDir, mainPkg string) (string, error) {
	rel := strings.TrimPrefix(mainPkg, "./")
	if rel == "" || rel == "." {
		rel = "."
	}
	// If main points at a file, use its directory.
	candidate := filepath.Join(appDir, rel)
	if st, err := os.Stat(candidate); err == nil && !st.IsDir() {
		candidate = filepath.Dir(candidate)
	}
	dir := filepath.Join(candidate, DirName)
	st, err := os.Stat(dir)
	if err != nil {
		if os.IsNotExist(err) {
			return "", nil
		}
		return "", err
	}
	if !st.IsDir() {
		return "", fmt.Errorf("%s exists but is not a directory", dir)
	}
	return dir, nil
}

// CopyTree copies src into dest, following symlinks the way ko does (include
// the referent's contents under the symlink's relative path).
func CopyTree(src, dest string) error {
	if err := os.MkdirAll(dest, 0o755); err != nil {
		return err
	}
	return filepath.WalkDir(src, func(path string, d fs.DirEntry, err error) error {
		if err != nil {
			return err
		}
		rel, err := filepath.Rel(src, path)
		if err != nil {
			return err
		}
		if rel == "." {
			return nil
		}
		target := filepath.Join(dest, rel)

		// Follow symlinks.
		info, err := os.Lstat(path)
		if err != nil {
			return err
		}
		if info.Mode()&os.ModeSymlink != 0 {
			resolved, err := filepath.EvalSymlinks(path)
			if err != nil {
				return fmt.Errorf("kodata symlink %s: %w", path, err)
			}
			st, err := os.Stat(resolved)
			if err != nil {
				return err
			}
			if st.IsDir() {
				return CopyTree(resolved, target)
			}
			return copyFile(resolved, target, st.Mode())
		}
		if d.IsDir() {
			return os.MkdirAll(target, 0o755)
		}
		return copyFile(path, target, info.Mode())
	})
}

func copyFile(src, dest string, mode os.FileMode) error {
	if err := os.MkdirAll(filepath.Dir(dest), 0o755); err != nil {
		return err
	}
	in, err := os.Open(src)
	if err != nil {
		return err
	}
	defer in.Close()
	out, err := os.OpenFile(dest, os.O_CREATE|os.O_TRUNC|os.O_WRONLY, mode.Perm())
	if err != nil {
		return err
	}
	if _, err := io.Copy(out, in); err != nil {
		out.Close()
		return err
	}
	return out.Close()
}

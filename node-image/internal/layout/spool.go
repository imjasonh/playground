package layout

import (
	"archive/tar"
	"compress/gzip"
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
	"github.com/imjasonh/playground/node-image/internal/resolve"
)

const spoolMetaName = ".node-image-spool.json"

type spoolMeta struct {
	IntegrityKey string `json:"integrityKey"`
	TarballSHA512 string `json:"tarballSHA512"`
	TarballSize  int64  `json:"tarballSize"`
}

// SpoolDir returns ~/.cache/node-image/spool — content-addressed extracted
// package trees keyed by integrity. Used so OCI layer writes can reopen file
// bodies without keeping a per-build staging tree, and so rebuilds skip
// re-extracting unchanged tarballs.
func SpoolDir() (string, error) {
	home, err := os.UserHomeDir()
	if err != nil {
		return "", err
	}
	return filepath.Join(home, ".cache", "node-image", "spool"), nil
}

// SpoolPackage ensures the npm tarball at tgzPath is extracted under
// spoolRoot/<integrityKey>/ (package contents only — no package/ wrapper).
// Returns the absolute package directory.
//
// On cache hit the source tarball is re-hashed and compared to metadata written
// at extract time (same trust model as fetch.Cache). The spool tree is also
// checked for path-escaping symlinks before reuse.
func SpoolPackage(spoolRoot, integrityKey, tgzPath string) (pkgDir string, err error) {
	if integrityKey == "" {
		return "", fmt.Errorf("empty integrity key for spool")
	}
	if err := os.MkdirAll(spoolRoot, 0o700); err != nil {
		return "", err
	}
	pkgDir = filepath.Join(spoolRoot, integrityKey)
	metaPath := filepath.Join(pkgDir, spoolMetaName)

	sum, size, err := hashTarball(tgzPath)
	if err != nil {
		return "", err
	}
	if hit, err := spoolHitOK(pkgDir, metaPath, integrityKey, sum, size); err != nil {
		return "", err
	} else if hit {
		return pkgDir, nil
	}

	_ = os.RemoveAll(pkgDir)
	tmp, err := os.MkdirTemp(spoolRoot, "spool-*.tmp")
	if err != nil {
		return "", err
	}
	defer os.RemoveAll(tmp)

	if err := extractNPMTarball(tgzPath, tmp); err != nil {
		return "", err
	}
	if err := assertSafeSpoolTree(tmp); err != nil {
		return "", fmt.Errorf("extracted spool unsafe: %w", err)
	}
	meta := spoolMeta{
		IntegrityKey:  integrityKey,
		TarballSHA512: sum,
		TarballSize:   size,
	}
	b, err := json.Marshal(meta)
	if err != nil {
		return "", err
	}
	if err := os.WriteFile(filepath.Join(tmp, spoolMetaName), append(b, '\n'), 0o600); err != nil {
		return "", err
	}
	if err := os.RemoveAll(pkgDir); err != nil && !os.IsNotExist(err) {
		return "", err
	}
	if err := os.Rename(tmp, pkgDir); err != nil {
		// Another process may have won the race — accept only if their hit verifies.
		if hit, err2 := spoolHitOK(pkgDir, metaPath, integrityKey, sum, size); err2 == nil && hit {
			return pkgDir, nil
		}
		return "", err
	}
	return pkgDir, nil
}

func spoolHitOK(pkgDir, metaPath, integrityKey, sum string, size int64) (bool, error) {
	b, err := os.ReadFile(metaPath)
	if err != nil {
		return false, nil
	}
	var meta spoolMeta
	if err := json.Unmarshal(b, &meta); err != nil {
		return false, nil
	}
	if meta.IntegrityKey != integrityKey || meta.TarballSHA512 != sum || meta.TarballSize != size {
		return false, nil
	}
	if _, err := os.Stat(filepath.Join(pkgDir, "package.json")); err != nil {
		return false, nil
	}
	if err := assertSafeSpoolTree(pkgDir); err != nil {
		return false, fmt.Errorf("cached spool %s failed safety check (delete and rebuild): %w", pkgDir, err)
	}
	return true, nil
}

func hashTarball(path string) (hexSum string, size int64, err error) {
	f, err := os.Open(path)
	if err != nil {
		return "", 0, err
	}
	defer f.Close()
	h := sha512.New()
	n, err := io.Copy(h, f)
	if err != nil {
		return "", 0, err
	}
	return hex.EncodeToString(h.Sum(nil)), n, nil
}

// assertSafeSpoolTree ensures every symlink under root resolves inside root and
// no entry path escapes. Regular files that are unexpectedly symlinks are
// caught via Lstat during the walk.
func assertSafeSpoolTree(root string) error {
	rootAbs, err := filepath.Abs(root)
	if err != nil {
		return err
	}
	return filepath.WalkDir(rootAbs, func(path string, d fs.DirEntry, err error) error {
		if err != nil {
			return err
		}
		rel, err := filepath.Rel(rootAbs, path)
		if err != nil {
			return err
		}
		if rel == "." {
			return nil
		}
		if base := filepath.Base(path); base == spoolMetaName {
			return nil
		}
		clean := filepath.Clean(rel)
		if clean == ".." || strings.HasPrefix(clean, ".."+string(os.PathSeparator)) {
			return fmt.Errorf("path escape in spool: %s", rel)
		}
		info, err := d.Info()
		if err != nil {
			return err
		}
		if info.Mode()&os.ModeSymlink != 0 {
			target, err := os.Readlink(path)
			if err != nil {
				return err
			}
			if filepath.IsAbs(target) || strings.HasPrefix(filepath.Clean(target), "..") {
				return fmt.Errorf("unsafe symlink in spool: %s -> %s", rel, target)
			}
			resolved := filepath.Clean(filepath.Join(filepath.Dir(path), filepath.FromSlash(target)))
			if !isWithinDir(rootAbs, resolved) {
				return fmt.Errorf("symlink escape in spool: %s -> %s", rel, target)
			}
		}
		return nil
	})
}

// StoreFilesFromSpool walks an extracted package directory and returns layer
// files under node_modules/.pnpm/<vdir>/node_modules/<pkgName>/… with DiskPath
// set so WriteCompressed streams from the spool. Metadata files are omitted.
// Symlinks are preserved as symlinks (never followed into host files).
func StoreFilesFromSpool(pkgDir, depPath, pkgName string) ([]layer.File, error) {
	vdir := VirtualStoreDir(depPath)
	prefix := "node_modules/.pnpm/" + vdir + "/node_modules/" + strings.Trim(filepath.ToSlash(pkgName), "/")
	files, err := layer.FromDir(pkgDir, prefix)
	if err != nil {
		return nil, err
	}
	out := make([]layer.File, 0, len(files))
	for _, f := range files {
		base := filepath.Base(f.Rel)
		if base == spoolMetaName || base == ".node-image-spool-ok" {
			continue
		}
		out = append(out, f)
	}
	return out, nil
}

// ScanTarballMeta reads package.json and flags (binding.gyp, prebuilds/) from
// an npm tarball without writing a full tree.
func ScanTarballMeta(tgzPath string) (pj packageJSON, hasBindingGyp, hasPrebuilds bool, err error) {
	prefix, err := npmTarballRootPrefix(tgzPath)
	if err != nil {
		return pj, false, false, err
	}
	f, err := os.Open(tgzPath)
	if err != nil {
		return pj, false, false, err
	}
	defer f.Close()
	gr, err := gzip.NewReader(f)
	if err != nil {
		return pj, false, false, err
	}
	defer gr.Close()
	tr := tar.NewReader(gr)
	var pjBytes []byte
	for {
		hdr, err := tr.Next()
		if err == io.EOF {
			break
		}
		if err != nil {
			return pj, false, false, err
		}
		name := strings.TrimPrefix(hdr.Name, "./")
		if prefix != "" {
			if name == strings.TrimSuffix(prefix, "/") {
				continue
			}
			if !strings.HasPrefix(name, prefix) {
				continue
			}
			name = strings.TrimPrefix(name, prefix)
		}
		switch {
		case name == "package.json":
			pjBytes, err = io.ReadAll(tr)
			if err != nil {
				return pj, false, false, err
			}
		case name == "binding.gyp":
			hasBindingGyp = true
			_, _ = io.Copy(io.Discard, tr)
		case name == "prebuilds" || strings.HasPrefix(name, "prebuilds/"):
			hasPrebuilds = true
			_, _ = io.Copy(io.Discard, tr)
		default:
			_, _ = io.Copy(io.Discard, tr)
		}
	}
	if len(pjBytes) == 0 {
		return pj, false, false, fmt.Errorf("tarball %s has no package.json", tgzPath)
	}
	if err := json.Unmarshal(pjBytes, &pj); err != nil {
		return pj, false, false, err
	}
	return pj, hasBindingGyp, hasPrebuilds, nil
}

// CheckScriptsMeta is CheckScriptsInDir without a package directory on disk.
func CheckScriptsMeta(ref resolve.PackageRef, pj packageJSON, hasBindingGyp, hasPrebuilds bool) error {
	if ref.Optional {
		return nil
	}
	hasPlatformOptionals := false
	if pj.OptionalDependencies != nil {
		for name := range pj.OptionalDependencies {
			if strings.Contains(name, "/") && (strings.Contains(name, "linux-") || strings.Contains(name, "darwin-") || strings.Contains(name, "win32-")) {
				hasPlatformOptionals = true
				break
			}
		}
	}
	if hasPrebuilds || hasPlatformOptionals {
		return nil
	}
	needsNative := hasBindingGyp
	for _, s := range []string{"preinstall", "install", "postinstall"} {
		body := pj.scriptString(s)
		if body == "" {
			continue
		}
		lower := strings.ToLower(body)
		if strings.Contains(lower, "node-gyp") ||
			strings.Contains(lower, "node-pre-gyp") ||
			strings.Contains(lower, "prebuild-install") ||
			strings.Contains(lower, "nan ") ||
			strings.Contains(lower, "cmake-js") {
			needsNative = true
			break
		}
	}
	if !needsNative {
		return nil
	}
	return fmt.Errorf("package %s appears to require a native build (node-gyp/binding.gyp) and node-image never runs dependency install scripts\nHint: prefer packages that ship prebuilds/ or platform-specific optionalDependencies (e.g. @esbuild/linux-x64). Remove or replace %s if it must compile from source", ref.PackageID, ref.PackageID)
}

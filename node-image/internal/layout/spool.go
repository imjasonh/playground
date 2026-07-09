package layout

import (
	"archive/tar"
	"compress/gzip"
	"encoding/json"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"strings"

	"github.com/imjasonh/playground/node-image/internal/layer"
	"github.com/imjasonh/playground/node-image/internal/resolve"
)

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
// Extraction streams from the tarball into the spool; subsequent calls with
// the same integrity are a no-op. Layer assembly then streams from these
// files via layer.File{DiskPath} — never buffering the whole tree in memory.
func SpoolPackage(spoolRoot, integrityKey, tgzPath string) (pkgDir string, err error) {
	if integrityKey == "" {
		return "", fmt.Errorf("empty integrity key for spool")
	}
	if err := os.MkdirAll(spoolRoot, 0o755); err != nil {
		return "", err
	}
	pkgDir = filepath.Join(spoolRoot, integrityKey)
	marker := filepath.Join(pkgDir, ".node-image-spool-ok")
	if st, err := os.Stat(marker); err == nil && !st.IsDir() {
		if _, err := os.Stat(filepath.Join(pkgDir, "package.json")); err == nil {
			return pkgDir, nil
		}
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
	if err := os.WriteFile(filepath.Join(tmp, ".node-image-spool-ok"), []byte("ok\n"), 0o644); err != nil {
		return "", err
	}
	if err := os.RemoveAll(pkgDir); err != nil && !os.IsNotExist(err) {
		return "", err
	}
	if err := os.Rename(tmp, pkgDir); err != nil {
		// Another process may have won the race.
		if _, err2 := os.Stat(marker); err2 == nil {
			return pkgDir, nil
		}
		return "", err
	}
	return pkgDir, nil
}

// StoreFilesFromSpool walks an extracted package directory and returns layer
// files under node_modules/.pnpm/<vdir>/node_modules/<pkgName>/… with DiskPath
// set so WriteCompressed streams from the spool. The spool marker file is omitted.
func StoreFilesFromSpool(pkgDir, depPath, pkgName string) ([]layer.File, error) {
	vdir := VirtualStoreDir(depPath)
	prefix := "node_modules/.pnpm/" + vdir + "/node_modules/" + strings.Trim(filepath.ToSlash(pkgName), "/")
	files, err := layer.FromDir(pkgDir, prefix)
	if err != nil {
		return nil, err
	}
	out := files[:0]
	for _, f := range files {
		base := filepath.Base(f.Rel)
		if base == ".node-image-spool-ok" {
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

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

	"github.com/imjasonh/playground/node-image/internal/lock"
	"github.com/imjasonh/playground/node-image/internal/resolve"
)

// Result is a materialized node_modules tree under Root.
type Result struct {
	Root string
}

// Materialize extracts packages into root/node_modules using a pnpm-like virtual store.
// tarballs maps PackageID → local .tgz path.
// Edges from the lock are used to create store-internal dependency symlinks.
// Only importer direct dependencies are linked at the top level (plus root .bin).
func Materialize(root string, l *lock.Lock, refs []resolve.PackageRef, tarballs map[string]string, direct []string) (*Result, error) {
	nm := filepath.Join(root, "node_modules")
	store := filepath.Join(nm, ".pnpm")
	if err := os.MkdirAll(store, 0o755); err != nil {
		return nil, err
	}

	byDepPath := make(map[string]resolve.PackageRef, len(refs))
	byName := make(map[string]resolve.PackageRef, len(refs))
	for _, ref := range refs {
		byDepPath[ref.DepPath] = ref
		byName[ref.Name] = ref
	}

	type installed struct {
		ref     resolve.PackageRef
		pkgDir  string
		pkgJSON packageJSON
	}
	inst := make([]installed, 0, len(refs))

	for _, ref := range refs {
		tgz, ok := tarballs[ref.PackageID]
		if !ok {
			return nil, fmt.Errorf("missing tarball for %s", ref.PackageID)
		}
		depDir := filepath.Join(store, VirtualStoreDir(ref.DepPath), "node_modules")
		pkgDir := filepath.Join(depDir, filepath.FromSlash(ref.Name))
		if err := os.MkdirAll(filepath.Dir(pkgDir), 0o755); err != nil {
			return nil, err
		}
		if err := extractNPMTarball(tgz, pkgDir); err != nil {
			return nil, fmt.Errorf("extract %s: %w", ref.PackageID, err)
		}
		pj, err := readPackageJSON(pkgDir)
		if err != nil {
			return nil, fmt.Errorf("%s package.json: %w", ref.PackageID, err)
		}
		if err := CheckScriptsInDir(ref, pkgDir, pj); err != nil {
			return nil, err
		}
		inst = append(inst, installed{ref: ref, pkgDir: pkgDir, pkgJSON: pj})
	}

	for _, in := range inst {
		snap := l.Snapshots[in.ref.DepPath]
		if snap == nil {
			snap = l.Snapshots[in.ref.PackageID]
		}
		if snap != nil {
			var deps []namedDep
			add := func(depName, ver string) {
				depPath := resolve.DepPathFrom(depName, ver)
				var ref resolve.PackageRef
				var ok bool
				if ref, ok = byDepPath[depPath]; !ok {
					if ref, ok = byDepPath[ver]; !ok {
						for _, r := range refs {
							if r.PackageID == ver || r.DepPath == ver || r.PackageID == depPath || r.DepPath == depPath {
								ref = r
								ok = true
								break
							}
						}
					}
				}
				if !ok {
					return // filtered optional / missing
				}
				deps = append(deps, namedDep{linkName: depName, ref: ref})
			}
			for depName, ver := range snap.Dependencies {
				add(depName, ver)
			}
			for depName, ver := range snap.OptionalDependencies {
				add(depName, ver)
			}
			if err := linkStoreDeps(root, in.ref, deps); err != nil {
				return nil, err
			}
		}
		// Bins inside the virtual store node_modules (pnpm-compatible).
		if err := writeBins(filepath.Dir(in.pkgDir), in.pkgDir, in.pkgJSON); err != nil {
			return nil, err
		}
	}

	if err := LinkTopLevel(root, refs, direct); err != nil {
		return nil, err
	}
	// Root node_modules/.bin for direct deps that expose bins.
	if err := linkRootBins(root, refs, direct, byName); err != nil {
		return nil, err
	}
	return &Result{Root: root}, nil
}

// VirtualStoreDir encodes a lock depPath the way pnpm names directories under
// node_modules/.pnpm: '/' → '+', '(' → '_', ')' removed.
// e.g. "@scope/pkg@1.0.0(peer@2)" → "@scope+pkg@1.0.0_peer@2"
func VirtualStoreDir(depPath string) string {
	s := strings.ReplaceAll(depPath, "/", "+")
	s = strings.ReplaceAll(s, "(", "_")
	s = strings.ReplaceAll(s, ")", "")
	return s
}

// LinkTopLevel creates node_modules/<name> → .pnpm/.../node_modules/<name>
// for importer direct dependencies only.
func LinkTopLevel(root string, refs []resolve.PackageRef, direct []string) error {
	nm := filepath.Join(root, "node_modules")
	want := map[string]struct{}{}
	if len(direct) == 0 {
		// Back-compat: if caller didn't pass directs, link everything (tests).
		for _, ref := range refs {
			want[ref.Name] = struct{}{}
		}
	} else {
		for _, n := range direct {
			want[n] = struct{}{}
		}
	}
	byName := map[string]resolve.PackageRef{}
	for _, ref := range refs {
		if _, ok := want[ref.Name]; ok {
			byName[ref.Name] = ref
		}
	}
	for name, ref := range byName {
		targetAbs := filepath.Join(nm, ".pnpm", VirtualStoreDir(ref.DepPath), "node_modules", filepath.FromSlash(ref.Name))
		link := filepath.Join(nm, filepath.FromSlash(name))
		if err := os.MkdirAll(filepath.Dir(link), 0o755); err != nil {
			return err
		}
		rel, err := filepath.Rel(filepath.Dir(link), targetAbs)
		if err != nil {
			return err
		}
		_ = os.Remove(link)
		if err := os.Symlink(rel, link); err != nil {
			return fmt.Errorf("symlink %s: %w", link, err)
		}
	}
	return nil
}

func linkRootBins(root string, refs []resolve.PackageRef, direct []string, byName map[string]resolve.PackageRef) error {
	want := map[string]struct{}{}
	if len(direct) == 0 {
		for _, ref := range refs {
			want[ref.Name] = struct{}{}
		}
	} else {
		for _, n := range direct {
			want[n] = struct{}{}
		}
	}
	nm := filepath.Join(root, "node_modules")
	for name := range want {
		ref, ok := byName[name]
		if !ok {
			continue
		}
		pkgDir := filepath.Join(root, "node_modules", ".pnpm", VirtualStoreDir(ref.DepPath), "node_modules", filepath.FromSlash(ref.Name))
		pj, err := readPackageJSON(pkgDir)
		if err != nil {
			continue
		}
		if err := writeBins(nm, pkgDir, pj); err != nil {
			return err
		}
	}
	return nil
}

type namedDep struct {
	linkName string
	ref      resolve.PackageRef
}

func linkStoreDeps(root string, parent resolve.PackageRef, deps []namedDep) error {
	parentNM := filepath.Join(root, "node_modules", ".pnpm", VirtualStoreDir(parent.DepPath), "node_modules")
	for _, dep := range deps {
		depPkg := filepath.Join(root, "node_modules", ".pnpm", VirtualStoreDir(dep.ref.DepPath), "node_modules", filepath.FromSlash(dep.ref.Name))
		link := filepath.Join(parentNM, filepath.FromSlash(dep.linkName))
		if _, err := os.Lstat(link); err == nil {
			continue
		}
		if err := os.MkdirAll(filepath.Dir(link), 0o755); err != nil {
			return err
		}
		rel, err := filepath.Rel(filepath.Dir(link), depPkg)
		if err != nil {
			return err
		}
		if err := os.Symlink(rel, link); err != nil {
			return err
		}
	}
	return nil
}

type packageJSON struct {
	Name                 string            `json:"name"`
	Version              string            `json:"version"`
	Bin                  json.RawMessage   `json:"bin"`
	Directories          *directoriesJSON  `json:"directories"`
	Scripts              map[string]string `json:"scripts"`
	OptionalDependencies map[string]string `json:"optionalDependencies"`
}

type directoriesJSON struct {
	Bin string `json:"bin"`
}

func readPackageJSON(dir string) (packageJSON, error) {
	var pj packageJSON
	b, err := os.ReadFile(filepath.Join(dir, "package.json"))
	if err != nil {
		return pj, err
	}
	if err := json.Unmarshal(b, &pj); err != nil {
		return pj, err
	}
	return pj, nil
}

// CheckScriptsInDir fails if a non-optional package needs lifecycle scripts
// without a workable offline alternative (prebuilds/ or platform optionalDependencies).
func CheckScriptsInDir(ref resolve.PackageRef, pkgDir string, pj packageJSON) error {
	if ref.Optional {
		return nil
	}
	hasPrebuilds := false
	if st, err := os.Stat(filepath.Join(pkgDir, "prebuilds")); err == nil && st.IsDir() {
		hasPrebuilds = true
	}
	// Packages like esbuild ship a postinstall that only selects an optional
	// platform binary already present via optionalDependencies — allow that.
	hasPlatformOptionals := false
	if pj.OptionalDependencies != nil {
		for name := range pj.OptionalDependencies {
			if strings.Contains(name, "/") && (strings.Contains(name, "linux-") || strings.Contains(name, "darwin-") || strings.Contains(name, "win32-")) {
				hasPlatformOptionals = true
				break
			}
		}
	}
	for _, s := range []string{"preinstall", "install", "postinstall"} {
		if pj.Scripts[s] == "" {
			continue
		}
		if hasPrebuilds || hasPlatformOptionals {
			continue
		}
		return fmt.Errorf("package %s declares a %s lifecycle script; node-image never runs dependency install scripts (required for multi-arch hermetic builds)\nHint: prefer packages that ship prebuilds/ (prebuildify) or platform-specific optionalDependencies (e.g. @esbuild/linux-x64). Remove or replace %s if it must compile from source", ref.PackageID, s, ref.PackageID)
	}
	return nil
}

func writeBins(nodeModulesDir, pkgDir string, pj packageJSON) error {
	bins, err := parseBin(pj)
	if err != nil || len(bins) == 0 {
		return err
	}
	binDir := filepath.Join(nodeModulesDir, ".bin")
	if err := os.MkdirAll(binDir, 0o755); err != nil {
		return err
	}
	for name, rel := range bins {
		target := filepath.Join(pkgDir, filepath.FromSlash(rel))
		link := filepath.Join(binDir, name)
		relTarget, err := filepath.Rel(binDir, target)
		if err != nil {
			return err
		}
		_ = os.Remove(link)
		if err := os.Symlink(relTarget, link); err != nil {
			return err
		}
	}
	return nil
}

func parseBin(pj packageJSON) (map[string]string, error) {
	out := map[string]string{}
	if len(pj.Bin) != 0 && string(pj.Bin) != "null" {
		var asString string
		if err := json.Unmarshal(pj.Bin, &asString); err == nil {
			name := pj.Name
			if i := strings.LastIndex(name, "/"); i >= 0 {
				name = name[i+1:]
			}
			out[name] = asString
		} else {
			var asMap map[string]string
			if err := json.Unmarshal(pj.Bin, &asMap); err != nil {
				return nil, err
			}
			for k, v := range asMap {
				out[k] = v
			}
		}
	}
	if pj.Directories != nil && pj.Directories.Bin != "" {
		// directories.bin is a directory of executables; we only record the dir
		// marker by linking each file when present on disk — caller may not
		// have extracted yet, so skip if missing.
		binDir := filepath.Join(filepath.Dir(pj.Name), pj.Directories.Bin) // unused path helper
		_ = binDir
	}
	return out, nil
}

func extractNPMTarball(tgzPath, destDir string) error {
	f, err := os.Open(tgzPath)
	if err != nil {
		return err
	}
	defer f.Close()
	gr, err := gzip.NewReader(f)
	if err != nil {
		return err
	}
	defer gr.Close()
	tr := tar.NewReader(gr)
	if err := os.MkdirAll(destDir, 0o755); err != nil {
		return err
	}
	for {
		hdr, err := tr.Next()
		if err == io.EOF {
			break
		}
		if err != nil {
			return err
		}
		name := hdr.Name
		name = strings.TrimPrefix(name, "./")
		if !strings.HasPrefix(name, "package/") {
			continue
		}
		rel := strings.TrimPrefix(name, "package/")
		if rel == "" {
			continue
		}
		// Reject path traversal.
		clean := filepath.Clean(filepath.FromSlash(rel))
		if strings.HasPrefix(clean, "..") || filepath.IsAbs(clean) {
			return fmt.Errorf("refusing unsafe path in tarball: %s", hdr.Name)
		}
		out := filepath.Join(destDir, clean)
		switch hdr.Typeflag {
		case tar.TypeDir:
			if err := os.MkdirAll(out, 0o755); err != nil {
				return err
			}
		case tar.TypeReg, tar.TypeRegA:
			if err := os.MkdirAll(filepath.Dir(out), 0o755); err != nil {
				return err
			}
			mode := hdr.FileInfo().Mode().Perm()
			w, err := os.OpenFile(out, os.O_CREATE|os.O_WRONLY|os.O_TRUNC, mode)
			if err != nil {
				return err
			}
			if _, err := io.Copy(w, tr); err != nil {
				w.Close()
				return err
			}
			if err := w.Close(); err != nil {
				return err
			}
		case tar.TypeSymlink:
			if err := os.MkdirAll(filepath.Dir(out), 0o755); err != nil {
				return err
			}
			_ = os.Remove(out)
			if err := os.Symlink(hdr.Linkname, out); err != nil {
				return err
			}
		}
	}
	return nil
}

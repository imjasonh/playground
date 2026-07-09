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
func Materialize(root string, l *lock.Lock, refs []resolve.PackageRef, tarballs map[string]string) (*Result, error) {
	nm := filepath.Join(root, "node_modules")
	store := filepath.Join(nm, ".pnpm")
	if err := os.MkdirAll(store, 0o755); err != nil {
		return nil, err
	}

	byDepPath := make(map[string]resolve.PackageRef, len(refs))
	for _, ref := range refs {
		byDepPath[ref.DepPath] = ref
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
		depDir := filepath.Join(store, sanitizeDepPath(ref.DepPath), "node_modules")
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
			var deps []resolve.PackageRef
			add := func(ver string) {
				if dep, ok := byDepPath[ver]; ok {
					deps = append(deps, dep)
					return
				}
				// version might be package id without being the depPath key
				for _, r := range refs {
					if r.PackageID == ver || r.DepPath == ver {
						deps = append(deps, r)
						break
					}
				}
			}
			for _, ver := range snap.Dependencies {
				add(ver)
			}
			for _, ver := range snap.OptionalDependencies {
				add(ver)
			}
			if err := linkStoreDeps(root, in.ref, deps); err != nil {
				return nil, err
			}
		}
		if err := writeBins(filepath.Dir(in.pkgDir), in.pkgDir, in.pkgJSON); err != nil {
			return nil, err
		}
	}

	if err := LinkTopLevel(root, refs); err != nil {
		return nil, err
	}
	return &Result{Root: root}, nil
}

// LinkTopLevel creates node_modules/<name> → .pnpm/.../node_modules/<name>.
func LinkTopLevel(root string, refs []resolve.PackageRef) error {
	nm := filepath.Join(root, "node_modules")
	for _, ref := range refs {
		target := filepath.Join(".pnpm", sanitizeDepPath(ref.DepPath), "node_modules", filepath.FromSlash(ref.Name))
		link := filepath.Join(nm, filepath.FromSlash(ref.Name))
		if err := os.MkdirAll(filepath.Dir(link), 0o755); err != nil {
			return err
		}
		_ = os.Remove(link)
		if err := os.Symlink(target, link); err != nil {
			return fmt.Errorf("symlink %s: %w", link, err)
		}
	}
	return nil
}

func linkStoreDeps(root string, parent resolve.PackageRef, deps []resolve.PackageRef) error {
	parentNM := filepath.Join(root, "node_modules", ".pnpm", sanitizeDepPath(parent.DepPath), "node_modules")
	for _, dep := range deps {
		if dep.Name == parent.Name {
			continue
		}
		depPkg := filepath.Join(root, "node_modules", ".pnpm", sanitizeDepPath(dep.DepPath), "node_modules", filepath.FromSlash(dep.Name))
		rel, err := filepath.Rel(parentNM, depPkg)
		if err != nil {
			return err
		}
		link := filepath.Join(parentNM, filepath.FromSlash(dep.Name))
		if _, err := os.Lstat(link); err == nil {
			continue
		}
		if err := os.MkdirAll(filepath.Dir(link), 0o755); err != nil {
			return err
		}
		if err := os.Symlink(rel, link); err != nil {
			return err
		}
	}
	return nil
}

func sanitizeDepPath(depPath string) string {
	return filepath.FromSlash(depPath)
}

type packageJSON struct {
	Name    string            `json:"name"`
	Version string            `json:"version"`
	Bin     json.RawMessage   `json:"bin"`
	Scripts map[string]string `json:"scripts"`
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

// CheckScriptsInDir fails if a non-optional package needs lifecycle scripts without prebuilds.
func CheckScriptsInDir(ref resolve.PackageRef, pkgDir string, pj packageJSON) error {
	if ref.Optional {
		return nil
	}
	hasPrebuilds := false
	if st, err := os.Stat(filepath.Join(pkgDir, "prebuilds")); err == nil && st.IsDir() {
		hasPrebuilds = true
	}
	for _, s := range []string{"preinstall", "install", "postinstall"} {
		if pj.Scripts[s] == "" {
			continue
		}
		if hasPrebuilds {
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
	if len(pj.Bin) == 0 || string(pj.Bin) == "null" {
		return nil, nil
	}
	var asString string
	if err := json.Unmarshal(pj.Bin, &asString); err == nil {
		name := pj.Name
		if i := strings.LastIndex(name, "/"); i >= 0 {
			name = name[i+1:]
		}
		return map[string]string{name: asString}, nil
	}
	var asMap map[string]string
	if err := json.Unmarshal(pj.Bin, &asMap); err != nil {
		return nil, err
	}
	return asMap, nil
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
		out := filepath.Join(destDir, filepath.FromSlash(rel))
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

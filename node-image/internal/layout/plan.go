package layout

import (
	"fmt"
	"io/fs"
	"os"
	"path"
	"path/filepath"
	"sort"
	"strings"

	"github.com/imjasonh/playground/node-image/internal/layer"
	"github.com/imjasonh/playground/node-image/internal/lock"
	"github.com/imjasonh/playground/node-image/internal/resolve"
)

// PlannedLayout is a hermetic node_modules layout expressed as OCI layer file
// lists — no per-build staging tree. Store package bodies stream from the
// integrity spool; symlink/bin edges are synthesized from the lock.
type PlannedLayout struct {
	// Store is one entry per virtual-store package (files under .pnpm/<vdir>/…).
	Store []layer.PackageStore
	// Links is the top-level node_modules symlink / .bin layer.
	Links []layer.File
	// PackageJSON holds parsed package.json per depPath (for bins / diagnostics).
	PackageJSON map[string]packageJSON
}

// PlanOptions controls PlanLayout.
type PlanOptions struct {
	// SpoolRoot is the integrity spool directory (see SpoolDir).
	SpoolRoot string
	// IntegrityKey maps PackageID → filesystem key (e.g. sha512-<hex> from fetch.Cache).
	// Required for every non-local PackageID in refs.
	IntegrityKey map[string]string
	// LockRoot is the directory containing pnpm-lock.yaml (for patch paths).
	LockRoot string
	// AllowScripts is a named allowlist of packages permitted to need native builds
	// without prebuilds (scripts are still never executed by node-image).
	AllowScripts []string
}

// PlanLayout builds store + symlink layer file lists from the lock and cached
// tarballs (or workspace directories). Tarball contents are extracted once into
// the integrity spool (if missing) and then referenced by DiskPath for
// streaming into OCI layers.
func PlanLayout(l *lock.Lock, refs []resolve.PackageRef, tarballs map[string]string, direct []resolve.DirectDep, opt PlanOptions) (*PlannedLayout, error) {
	if opt.SpoolRoot == "" {
		return nil, fmt.Errorf("PlanLayout: SpoolRoot required")
	}
	if opt.IntegrityKey == nil {
		opt.IntegrityKey = map[string]string{}
	}
	byDepPath := make(map[string]resolve.PackageRef, len(refs))
	for _, ref := range refs {
		byDepPath[ref.DepPath] = ref
	}

	out := &PlannedLayout{
		Store:       make([]layer.PackageStore, 0, len(refs)),
		PackageJSON: make(map[string]packageJSON, len(refs)),
	}
	allow := allowSet(opt.AllowScripts)

	for _, ref := range refs {
		pkgDir, err := spoolRef(opt, ref, tarballs)
		if err != nil {
			return nil, err
		}
		if ref.PatchPath != "" {
			pkgDir, err = ensurePatchedSpool(opt, ref, pkgDir)
			if err != nil {
				return nil, err
			}
		}
		pj, err := readPackageJSON(pkgDir)
		if err != nil {
			return nil, fmt.Errorf("%s package.json: %w", ref.PackageID, err)
		}
		if err := CheckScriptsInDirAllow(ref, pkgDir, pj, allow); err != nil {
			return nil, err
		}
		out.PackageJSON[ref.DepPath] = pj

		files, err := StoreFilesFromSpool(pkgDir, ref.DepPath, ref.Name)
		if err != nil {
			return nil, err
		}
		files = FilterSpoolMeta(files)
		depLinks, err := storeDepSymlinks(ref, l, byDepPath)
		if err != nil {
			return nil, err
		}
		binLinks, err := storeBinSymlinks(ref, pj)
		if err != nil {
			return nil, err
		}
		files = append(files, depLinks...)
		files = append(files, binLinks...)
		sortLayerFiles(files)
		out.Store = append(out.Store, layer.PackageStore{
			Name:    ref.Name,
			DepPath: VirtualStoreDir(ref.DepPath),
			Files:   files,
		})
	}
	sort.Slice(out.Store, func(i, j int) bool { return out.Store[i].DepPath < out.Store[j].DepPath })

	links, err := planLinkLayer(refs, direct, out.PackageJSON, byDepPath)
	if err != nil {
		return nil, err
	}
	out.Links = links
	return out, nil
}

func spoolRef(opt PlanOptions, ref resolve.PackageRef, tarballs map[string]string) (string, error) {
	if ref.IsLocal {
		if ref.LocalPath == "" {
			return "", fmt.Errorf("local package %s missing LocalPath", ref.PackageID)
		}
		key := opt.IntegrityKey[ref.PackageID]
		if key == "" {
			var err error
			key, err = LocalContentKey(ref.LocalPath)
			if err != nil {
				return "", err
			}
		}
		pkgDir, err := SpoolLocalPackage(opt.SpoolRoot, key, ref.LocalPath)
		if err != nil {
			return "", fmt.Errorf("spool local %s: %w", ref.PackageID, err)
		}
		return pkgDir, nil
	}
	tgz, ok := tarballs[ref.PackageID]
	if !ok {
		return "", fmt.Errorf("missing tarball for %s", ref.PackageID)
	}
	key := opt.IntegrityKey[ref.PackageID]
	if key == "" {
		return "", fmt.Errorf("missing integrity key for %s", ref.PackageID)
	}
	pkgDir, err := SpoolPackage(opt.SpoolRoot, key, tgz)
	if err != nil {
		return "", fmt.Errorf("spool %s: %w", ref.PackageID, err)
	}
	return pkgDir, nil
}

func ensurePatchedSpool(opt PlanOptions, ref resolve.PackageRef, unpatchedDir string) (string, error) {
	patchFile := ref.PatchPath
	if opt.LockRoot != "" && !filepath.IsAbs(patchFile) {
		patchFile = filepath.Join(opt.LockRoot, filepath.FromSlash(ref.PatchPath))
	}
	baseKey := opt.IntegrityKey[ref.PackageID]
	if baseKey == "" {
		baseKey = "unknown"
	}
	suffix := "patch"
	if ref.PatchHash != "" {
		n := 16
		if len(ref.PatchHash) < n {
			n = len(ref.PatchHash)
		}
		suffix = "patch-" + ref.PatchHash[:n]
	}
	patchedKey := baseKey + "-" + suffix
	patchedDir := filepath.Join(opt.SpoolRoot, patchedKey)
	if _, err := os.Stat(filepath.Join(patchedDir, "package.json")); err == nil {
		return patchedDir, nil
	}
	_ = os.RemoveAll(patchedDir)
	tmp, err := os.MkdirTemp(opt.SpoolRoot, "patch-*.tmp")
	if err != nil {
		return "", err
	}
	defer os.RemoveAll(tmp)
	if err := copyPackageTree(unpatchedDir, tmp); err != nil {
		return "", fmt.Errorf("copy for patch %s: %w", ref.PackageID, err)
	}
	_ = os.Remove(filepath.Join(tmp, spoolMetaName))
	if err := ApplyPatch(tmp, patchFile); err != nil {
		return "", fmt.Errorf("patch %s: %w", ref.PackageID, err)
	}
	if err := os.Rename(tmp, patchedDir); err != nil {
		if _, err2 := os.Stat(filepath.Join(patchedDir, "package.json")); err2 == nil {
			return patchedDir, nil
		}
		return "", err
	}
	return patchedDir, nil
}

func allowSet(names []string) map[string]bool {
	m := map[string]bool{}
	for _, n := range names {
		m[n] = true
		if i := strings.Index(n, "@"); i > 0 && !strings.HasPrefix(n, "@") {
			m[n[:i]] = true
		}
	}
	return m
}

func storeDepSymlinks(parent resolve.PackageRef, l *lock.Lock, byDepPath map[string]resolve.PackageRef) ([]layer.File, error) {
	snap := l.Snapshots[parent.DepPath]
	if snap == nil {
		snap = l.Snapshots[parent.PackageID]
	}
	if snap == nil {
		return nil, nil
	}
	parentV := VirtualStoreDir(parent.DepPath)
	parentNM := "node_modules/.pnpm/" + parentV + "/node_modules"
	var files []layer.File
	add := func(linkName, ver string) error {
		if !validNodeModulesName(linkName) {
			return fmt.Errorf("package %s: dependency link name %q is not a valid node_modules entry", parent.PackageID, linkName)
		}
		depPath := resolve.DepPathFrom(linkName, ver)
		ref, ok := byDepPath[depPath]
		if !ok {
			if ref, ok = byDepPath[ver]; !ok {
				for _, r := range byDepPath {
					if r.PackageID == ver || r.DepPath == ver || r.PackageID == depPath || r.DepPath == depPath {
						ref = r
						ok = true
						break
					}
				}
			}
		}
		if !ok {
			return nil // filtered optional / missing
		}
		linkRel := parentNM + "/" + strings.Trim(filepath.ToSlash(linkName), "/")
		if err := safeLayerRel(linkRel); err != nil {
			return err
		}
		targetAbs := "node_modules/.pnpm/" + VirtualStoreDir(ref.DepPath) + "/node_modules/" + strings.Trim(filepath.ToSlash(ref.Name), "/")
		rel, err := relSymlink(path.Dir(linkRel), targetAbs)
		if err != nil {
			return err
		}
		files = append(files, layer.File{
			Rel:  linkRel,
			Mode: fs.ModeSymlink | 0o777,
			Link: rel,
		})
		return nil
	}
	for name, ver := range snap.Dependencies {
		if err := add(name, ver); err != nil {
			return nil, err
		}
	}
	for name, ver := range snap.OptionalDependencies {
		if err := add(name, ver); err != nil {
			return nil, err
		}
	}
	return files, nil
}

func storeBinSymlinks(ref resolve.PackageRef, pj packageJSON) ([]layer.File, error) {
	bins, err := parseBin(pj)
	if err != nil {
		return nil, err
	}
	if len(bins) == 0 {
		return nil, nil
	}
	vdir := VirtualStoreDir(ref.DepPath)
	binDir := "node_modules/.pnpm/" + vdir + "/node_modules/.bin"
	pkgPrefix := "node_modules/.pnpm/" + vdir + "/node_modules/" + strings.Trim(filepath.ToSlash(ref.Name), "/")
	var files []layer.File
	names := make([]string, 0, len(bins))
	for name := range bins {
		names = append(names, name)
	}
	sort.Strings(names)
	for _, name := range names {
		rel := bins[name] // already sanitized by parseBin
		target := pkgPrefix + "/" + rel
		linkRel := binDir + "/" + name
		sym, err := relSymlink(binDir, target)
		if err != nil {
			return nil, err
		}
		files = append(files, layer.File{
			Rel:  linkRel,
			Mode: fs.ModeSymlink | 0o777,
			Link: sym,
		})
	}
	return files, nil
}

func planLinkLayer(refs []resolve.PackageRef, direct []resolve.DirectDep, pjs map[string]packageJSON, byDepPath map[string]resolve.PackageRef) ([]layer.File, error) {
	links := direct
	if len(links) == 0 {
		for _, ref := range refs {
			links = append(links, resolve.DirectDep{LinkName: ref.Name, DepPath: ref.DepPath})
		}
	}
	var files []layer.File
	seenTop := map[string]struct{}{}
	for _, d := range links {
		if !validNodeModulesName(d.LinkName) {
			return nil, fmt.Errorf("direct dependency link name %q is not a valid node_modules entry", d.LinkName)
		}
		ref, ok := byDepPath[d.DepPath]
		if !ok {
			for _, r := range refs {
				if r.PackageID == d.DepPath || r.DepPath == d.DepPath {
					ref = r
					ok = true
					break
				}
			}
		}
		if !ok {
			return nil, fmt.Errorf("direct dependency %q → %q not found in resolved closure", d.LinkName, d.DepPath)
		}
		linkRel := "node_modules/" + strings.Trim(filepath.ToSlash(d.LinkName), "/")
		if err := safeLayerRel(linkRel); err != nil {
			return nil, err
		}
		if _, dup := seenTop[linkRel]; dup {
			continue
		}
		seenTop[linkRel] = struct{}{}
		target := "node_modules/.pnpm/" + VirtualStoreDir(ref.DepPath) + "/node_modules/" + strings.Trim(filepath.ToSlash(ref.Name), "/")
		sym, err := relSymlink(path.Dir(linkRel), target)
		if err != nil {
			return nil, err
		}
		files = append(files, layer.File{
			Rel:  linkRel,
			Mode: fs.ModeSymlink | 0o777,
			Link: sym,
		})
	}

	seenBinPkg := map[string]struct{}{}
	for _, d := range links {
		ref, ok := byDepPath[d.DepPath]
		if !ok {
			continue
		}
		if _, dup := seenBinPkg[ref.DepPath]; dup {
			continue
		}
		seenBinPkg[ref.DepPath] = struct{}{}
		pj, ok := pjs[ref.DepPath]
		if !ok {
			continue
		}
		bins, err := parseBin(pj)
		if err != nil {
			return nil, err
		}
		if len(bins) == 0 {
			continue
		}
		binDir := "node_modules/.bin"
		pkgPrefix := "node_modules/.pnpm/" + VirtualStoreDir(ref.DepPath) + "/node_modules/" + strings.Trim(filepath.ToSlash(ref.Name), "/")
		names := make([]string, 0, len(bins))
		for name := range bins {
			names = append(names, name)
		}
		sort.Strings(names)
		for _, name := range names {
			rel := bins[name]
			target := pkgPrefix + "/" + rel
			sym, err := relSymlink(binDir, target)
			if err != nil {
				return nil, err
			}
			files = append(files, layer.File{
				Rel:  binDir + "/" + name,
				Mode: fs.ModeSymlink | 0o777,
				Link: sym,
			})
		}
	}
	sortLayerFiles(files)
	return files, nil
}

// relSymlink returns a relative symlink target from linkDir to target.
// Both paths are slash-separated and relative to the same root. Fails closed
// if Rel cannot produce a relative path (never emits absolute targets).
func relSymlink(linkDir, target string) (string, error) {
	linkDir = path.Clean("/" + strings.TrimPrefix(linkDir, "/"))
	target = path.Clean("/" + strings.TrimPrefix(target, "/"))
	rel, err := filepath.Rel(filepath.FromSlash(linkDir), filepath.FromSlash(target))
	if err != nil {
		return "", fmt.Errorf("symlink %s -> %s: %w", linkDir, target, err)
	}
	rel = filepath.ToSlash(rel)
	if filepath.IsAbs(rel) || strings.HasPrefix(rel, "/") {
		return "", fmt.Errorf("refusing absolute symlink target for %s -> %s", linkDir, target)
	}
	return rel, nil
}

func sortLayerFiles(files []layer.File) {
	sort.Slice(files, func(i, j int) bool { return files[i].Rel < files[j].Rel })
}

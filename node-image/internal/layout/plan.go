package layout

import (
	"fmt"
	"io/fs"
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
	IntegrityKey map[string]string
}

// PlanLayout builds store + symlink layer file lists from the lock and cached
// tarballs. Tarball contents are extracted once into the integrity spool (if
// missing) and then referenced by DiskPath for streaming into OCI layers.
func PlanLayout(l *lock.Lock, refs []resolve.PackageRef, tarballs map[string]string, direct []resolve.DirectDep, opt PlanOptions) (*PlannedLayout, error) {
	if opt.SpoolRoot == "" {
		return nil, fmt.Errorf("PlanLayout: SpoolRoot required")
	}
	byDepPath := make(map[string]resolve.PackageRef, len(refs))
	for _, ref := range refs {
		byDepPath[ref.DepPath] = ref
	}

	out := &PlannedLayout{
		Store:       make([]layer.PackageStore, 0, len(refs)),
		PackageJSON: make(map[string]packageJSON, len(refs)),
	}

	for _, ref := range refs {
		tgz, ok := tarballs[ref.PackageID]
		if !ok {
			return nil, fmt.Errorf("missing tarball for %s", ref.PackageID)
		}
		key := ""
		if opt.IntegrityKey != nil {
			key = opt.IntegrityKey[ref.PackageID]
		}
		if key == "" {
			key = filepath.Base(tgz)
			key = strings.TrimSuffix(key, ".tgz")
		}
		pkgDir, err := SpoolPackage(opt.SpoolRoot, key, tgz)
		if err != nil {
			return nil, fmt.Errorf("spool %s: %w", ref.PackageID, err)
		}
		pj, err := readPackageJSON(pkgDir)
		if err != nil {
			return nil, fmt.Errorf("%s package.json: %w", ref.PackageID, err)
		}
		if err := CheckScriptsInDir(ref, pkgDir, pj); err != nil {
			return nil, err
		}
		out.PackageJSON[ref.DepPath] = pj

		files, err := StoreFilesFromSpool(pkgDir, ref.DepPath, ref.Name)
		if err != nil {
			return nil, err
		}
		// Nested dependency symlinks + store-local .bin live in the same store
		// package layer as the extracted files (pnpm layout).
		files = append(files, storeDepSymlinks(ref, l, byDepPath)...)
		files = append(files, storeBinSymlinks(ref, pj)...)
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

func storeDepSymlinks(parent resolve.PackageRef, l *lock.Lock, byDepPath map[string]resolve.PackageRef) []layer.File {
	snap := l.Snapshots[parent.DepPath]
	if snap == nil {
		snap = l.Snapshots[parent.PackageID]
	}
	if snap == nil {
		return nil
	}
	parentV := VirtualStoreDir(parent.DepPath)
	parentNM := "node_modules/.pnpm/" + parentV + "/node_modules"
	var files []layer.File
	add := func(linkName, ver string) {
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
			return
		}
		// Relative from parentNM/<linkName> → ../../<depV>/node_modules/<name>
		// Mirror filepath.Rel used by linkStoreDeps on a real tree.
		linkRel := parentNM + "/" + strings.Trim(filepath.ToSlash(linkName), "/")
		targetAbs := "node_modules/.pnpm/" + VirtualStoreDir(ref.DepPath) + "/node_modules/" + strings.Trim(filepath.ToSlash(ref.Name), "/")
		rel := relSymlink(path.Dir(linkRel), targetAbs)
		files = append(files, layer.File{
			Rel:  linkRel,
			Mode: fs.ModeSymlink | 0o777,
			Link: rel,
		})
	}
	for name, ver := range snap.Dependencies {
		add(name, ver)
	}
	for name, ver := range snap.OptionalDependencies {
		add(name, ver)
	}
	return files
}

func storeBinSymlinks(ref resolve.PackageRef, pj packageJSON) []layer.File {
	bins, err := parseBin(pj)
	if err != nil || len(bins) == 0 {
		return nil
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
		rel := strings.TrimPrefix(filepath.ToSlash(bins[name]), "./")
		target := pkgPrefix + "/" + rel
		files = append(files, layer.File{
			Rel:  binDir + "/" + name,
			Mode: fs.ModeSymlink | 0o777,
			Link: relSymlink(binDir, target),
		})
	}
	return files
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
		if _, dup := seenTop[linkRel]; dup {
			continue
		}
		seenTop[linkRel] = struct{}{}
		target := "node_modules/.pnpm/" + VirtualStoreDir(ref.DepPath) + "/node_modules/" + strings.Trim(filepath.ToSlash(ref.Name), "/")
		files = append(files, layer.File{
			Rel:  linkRel,
			Mode: fs.ModeSymlink | 0o777,
			Link: relSymlink(path.Dir(linkRel), target),
		})
	}

	// Root node_modules/.bin for direct deps.
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
		if err != nil || len(bins) == 0 {
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
			rel := strings.TrimPrefix(filepath.ToSlash(bins[name]), "./")
			target := pkgPrefix + "/" + rel
			files = append(files, layer.File{
				Rel:  binDir + "/" + name,
				Mode: fs.ModeSymlink | 0o777,
				Link: relSymlink(binDir, target),
			})
		}
	}
	sortLayerFiles(files)
	return files, nil
}

// relSymlink returns a relative symlink target from linkDir to target, using
// forward slashes (OCI / Linux layout). Both paths are slash-separated and
// relative to the same root (no leading slash).
func relSymlink(linkDir, target string) string {
	linkDir = path.Clean("/" + strings.TrimPrefix(linkDir, "/"))
	target = path.Clean("/" + strings.TrimPrefix(target, "/"))
	rel, err := filepath.Rel(filepath.FromSlash(linkDir), filepath.FromSlash(target))
	if err != nil {
		return target
	}
	return filepath.ToSlash(rel)
}

func sortLayerFiles(files []layer.File) {
	sort.Slice(files, func(i, j int) bool { return files[i].Rel < files[j].Rel })
}

package layer

import (
	"fmt"
	"hash/fnv"
	"io/fs"
	"os"
	"path/filepath"
	"sort"
	"strings"
)

// PackageStore is one virtual-store package directory to turn into layer(s).
type PackageStore struct {
	// Name is the package name used for stable bucketing (e.g. "ms" or "@scope/pkg").
	Name string
	// DepPath is the .pnpm directory name (e.g. "ms@2.1.3").
	DepPath string
	// Files are layer entries with Rel already under node_modules/.pnpm/<DepPath>/...
	Files []File
}

// Budget plans how many store layers we can emit.
type Budget struct {
	// MaxLayers is the total image layer budget including base + symlink + app.
	MaxLayers int
	// BaseLayers is the number of layers already in the base image.
	BaseLayers int
	// ExtraLayers counts non-store layers we will add (symlink + app, typically 2).
	ExtraLayers int
}

// StoreSlots returns how many store layers fit in the budget (at least 1).
func (b Budget) StoreSlots() int {
	slots := b.MaxLayers - b.BaseLayers - b.ExtraLayers
	if slots < 1 {
		return 1
	}
	return slots
}

// BucketStorePackages assigns packages to store layers.
// If len(packages) <= slots, one layer per package (sorted by DepPath).
// Otherwise packages are hashed by Name into exactly slots buckets (stable).
func BucketStorePackages(packages []PackageStore, slots int) [][]File {
	if slots < 1 {
		slots = 1
	}
	pkgs := append([]PackageStore(nil), packages...)
	sort.Slice(pkgs, func(i, j int) bool { return pkgs[i].DepPath < pkgs[j].DepPath })

	if len(pkgs) <= slots {
		out := make([][]File, 0, len(pkgs))
		for _, p := range pkgs {
			out = append(out, p.Files)
		}
		return out
	}

	buckets := make([][]File, slots)
	for _, p := range pkgs {
		h := fnv.New32a()
		_, _ = h.Write([]byte(p.Name))
		i := int(h.Sum32() % uint32(slots))
		buckets[i] = append(buckets[i], p.Files...)
	}
	// Drop empty buckets (possible when slots > distinct hash range — not with FNV)
	out := make([][]File, 0, slots)
	for _, b := range buckets {
		if len(b) == 0 {
			continue
		}
		sortFiles(b)
		out = append(out, b)
	}
	return out
}

// StorePackagesFromDir walks node_modules/.pnpm and returns one PackageStore per depPath dir.
func StorePackagesFromDir(stage string) ([]PackageStore, error) {
	pnpmDir := filepath.Join(stage, "node_modules", ".pnpm")
	st, err := os.Stat(pnpmDir)
	if err != nil {
		if os.IsNotExist(err) {
			return nil, nil
		}
		return nil, err
	}
	if !st.IsDir() {
		return nil, fmt.Errorf("%s is not a directory", pnpmDir)
	}
	entries, err := os.ReadDir(pnpmDir)
	if err != nil {
		return nil, err
	}
	var out []PackageStore
	for _, e := range entries {
		name := e.Name()
		if !e.IsDir() || name == "lock.yaml" || strings.HasPrefix(name, ".") {
			continue
		}
		// skip non-package dirs like node_modules at this level if any
		depPath := name
		abs := filepath.Join(pnpmDir, depPath)
		files, err := FromDir(abs, "node_modules/.pnpm/"+filepath.ToSlash(depPath))
		if err != nil {
			return nil, err
		}
		pkgName := packageNameFromDepPath(depPath)
		out = append(out, PackageStore{Name: pkgName, DepPath: depPath, Files: files})
	}
	sort.Slice(out, func(i, j int) bool { return out[i].DepPath < out[j].DepPath })
	return out, nil
}

func packageNameFromDepPath(depPath string) string {
	// depPath may be a pnpm virtual-store directory name ("/" → "+").
	s := depPath
	if strings.HasPrefix(s, "@") {
		rest := s[1:]
		i := strings.Index(rest, "@")
		if i <= 0 {
			return strings.ReplaceAll(s, "+", "/")
		}
		return "@" + strings.ReplaceAll(rest[:i], "+", "/")
	}
	i := strings.Index(s, "@")
	if i > 0 {
		return s[:i]
	}
	return strings.ReplaceAll(s, "+", "/")
}

// Ensure Directory entries exist — FromDir already adds dirs.

// MergeFiles concatenates and sorts files (for tests).
func MergeFiles(groups [][]File) []File {
	var all []File
	for _, g := range groups {
		all = append(all, g...)
	}
	sortFiles(all)
	return all
}

// FileCount helper for tests.
func FileCount(files []File) int {
	n := 0
	for _, f := range files {
		if f.Mode&fs.ModeDir == 0 {
			n++
		}
	}
	return n
}

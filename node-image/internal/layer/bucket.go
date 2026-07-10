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

// BucketOptions tunes BucketStorePackages.
type BucketOptions struct {
	// Unbucketed package names always get their own store layer (consume slots
	// first). Remaining packages fill hash buckets.
	Unbucketed []string
}

// BucketStorePackages assigns packages to store layers.
// If len(packages) <= slots, one layer per package (sorted by DepPath).
// Otherwise packages are hashed by Name into exactly slots buckets (stable).
func BucketStorePackages(packages []PackageStore, slots int) [][]File {
	return BucketStorePackagesOpts(packages, slots, BucketOptions{})
}

// BucketStorePackagesOpts is BucketStorePackages with a hot-list of unbucketed names.
func BucketStorePackagesOpts(packages []PackageStore, slots int, opt BucketOptions) [][]File {
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

	hot := map[string]bool{}
	for _, n := range opt.Unbucketed {
		hot[n] = true
	}

	var dedicated [][]File
	var rest []PackageStore
	for _, p := range pkgs {
		if hot[p.Name] && len(dedicated)+1 < slots {
			dedicated = append(dedicated, p.Files)
			continue
		}
		rest = append(rest, p)
	}
	remain := slots - len(dedicated)
	if remain < 1 {
		remain = 1
	}
	if len(rest) == 0 {
		return dedicated
	}
	if len(rest) <= remain {
		for _, p := range rest {
			dedicated = append(dedicated, p.Files)
		}
		return dedicated
	}

	buckets := make([][]File, remain)
	for _, p := range rest {
		h := fnv.New32a()
		_, _ = h.Write([]byte(p.Name))
		i := int(h.Sum32() % uint32(remain))
		buckets[i] = append(buckets[i], p.Files...)
	}
	out := append([][]File{}, dedicated...)
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

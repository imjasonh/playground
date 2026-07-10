package resolve

import (
	"fmt"
	"path/filepath"
	"runtime"
	"sort"
	"strings"

	"github.com/imjasonh/playground/node-image/internal/lock"
)

// Platform is a target install platform.
type Platform struct {
	OS   string // e.g. "linux"
	CPU  string // e.g. "x64", "arm64" (npm/pnpm arch names)
	Libc string // e.g. "glibc", "musl"
}

// LinuxAmd64 and LinuxArm64 are the default multi-arch targets.
var (
	LinuxAmd64 = Platform{OS: "linux", CPU: "x64", Libc: "glibc"}
	LinuxArm64 = Platform{OS: "linux", CPU: "arm64", Libc: "glibc"}
)

// HostPlatform approximates the build host (for diagnostics only).
func HostPlatform() Platform {
	cpu := runtime.GOARCH
	switch cpu {
	case "amd64":
		cpu = "x64"
	case "arm64":
		cpu = "arm64"
	}
	return Platform{OS: runtime.GOOS, CPU: cpu, Libc: "glibc"}
}

// PackageRef is one installable unit in the closure.
type PackageRef struct {
	// DepPath is the snapshots key (may include peer suffix).
	DepPath string
	// PackageID is name@version without peer suffix.
	PackageID string
	// Name is the package name (@scope/name).
	Name string
	// Version is the version string.
	Version string
	// Integrity from the lock.
	Integrity string
	// Tarball URL if present in lock; otherwise derived from registry.
	Tarball string
	// Optional is true if this node was reached only via optionalDependencies.
	Optional bool
	// LocalPath is set for workspace/link/directory packages (absolute or
	// lock-root-relative path to the package directory on disk).
	LocalPath string
	// IsLocal is true when the package is materialized from the workspace tree
	// rather than a registry/git tarball.
	IsLocal bool
	// PatchPath is a lock-root-relative path to a patch file, if any.
	PatchPath string
	// PatchHash is the pnpm patch hash from the lock, if any.
	PatchHash string
}

// DirectDep is an importer-facing dependency name bound to a resolved store path.
// LinkName is the top-level node_modules entry (may be an alias); DepPath is the
// snapshots / virtual-store key for the real package.
type DirectDep struct {
	LinkName string
	DepPath  string
}

type visitState struct {
	optional        bool
	done            bool
	skippedPlatform bool
	outIdx          int // index in out, or -1
}

// ClosureOptions configures Closure.
type ClosureOptions struct {
	// LockRoot is the directory containing pnpm-lock.yaml (for resolving
	// workspace/link/directory paths).
	LockRoot string
}

// Closure returns the production dependency closure for an importer.
func Closure(l *lock.Lock, importerKey string, plat Platform) ([]PackageRef, error) {
	return ClosureOpts(l, importerKey, plat, ClosureOptions{})
}

// ClosureOpts is Closure with extra options (workspace path resolution).
func ClosureOpts(l *lock.Lock, importerKey string, plat Platform, opt ClosureOptions) ([]PackageRef, error) {
	imp := l.Importers[importerKey]
	if imp == nil {
		return nil, fmt.Errorf("importer %q not found in lockfile", importerKey)
	}
	type item struct {
		depPath  string
		optional bool
		linkName string // original dependency name (for local packages)
		version  string // raw version field (may be link:/workspace:)
	}
	var queue []item
	state := map[string]*visitState{}

	enqueue := func(name, version string, optional bool) error {
		if version == "" || name == "" {
			return nil
		}
		if strings.HasPrefix(version, "catalog:") {
			return fmt.Errorf("dependency %q has unresolved catalog specifier %q\nHint: re-lock with pnpm so catalog: expands to a concrete version", name, version)
		}
		depPath := depPathFrom(name, version)
		st := state[depPath]
		if st == nil {
			state[depPath] = &visitState{optional: optional, outIdx: -1}
			queue = append(queue, item{depPath: depPath, optional: optional, linkName: name, version: version})
			return nil
		}
		if st.optional && !optional {
			if st.skippedPlatform {
				return fmt.Errorf("required package %s does not support %s/%s (libc=%s)\nHint: this package was first reached as optional and skipped for this platform, but is also required via another path", depPath, plat.OS, plat.CPU, plat.Libc)
			}
			st.optional = false
			if st.done {
				st.done = false
				queue = append(queue, item{depPath: depPath, optional: false, linkName: name, version: version})
			}
		}
		return nil
	}

	for name, d := range imp.Dependencies {
		if err := enqueue(name, d.Version, false); err != nil {
			return nil, err
		}
	}
	for name, d := range imp.OptionalDependencies {
		if err := enqueue(name, d.Version, true); err != nil {
			return nil, err
		}
	}

	var out []PackageRef
	for i := 0; i < len(queue); i++ {
		it := queue[i]
		st := state[it.depPath]
		if st == nil {
			continue
		}
		optional := st.optional
		if st.done && optional {
			continue
		}
		if st.done && !optional {
			if st.outIdx >= 0 {
				out[st.outIdx].Optional = false
			}
		}

		// Local workspace / link / file packages.
		if isLocalVersion(it.version) {
			ref, err := localRef(l, opt.LockRoot, it.linkName, it.version, it.depPath, optional)
			if err != nil {
				return nil, err
			}
			if st.outIdx >= 0 {
				out[st.outIdx].Optional = optional
			} else {
				st.outIdx = len(out)
				out = append(out, ref)
			}
			st.done = true
			st.optional = optional
			// Local packages may still have snapshot edges if present.
			snap := l.Snapshots[it.depPath]
			if snap != nil {
				for depName, ver := range snap.Dependencies {
					if err := enqueue(depName, ver, optional); err != nil {
						return nil, err
					}
				}
				for depName, ver := range snap.OptionalDependencies {
					if err := enqueue(depName, ver, true); err != nil {
						return nil, err
					}
				}
			}
			continue
		}

		pkgID := lock.PackageIDFromDepPath(it.depPath)
		pkgID = stripPatchHash(pkgID)
		pkg := l.Packages[pkgID]
		if pkg == nil {
			// Directory packages sometimes appear only as resolution.type=directory
			// under a different key — try the raw depPath.
			pkg = l.Packages[it.depPath]
			if pkg == nil {
				return nil, fmt.Errorf("package %s (from %s) missing from lock packages", pkgID, it.depPath)
			}
		}

		// Directory resolution recorded on the package entry.
		if pkg.Resolution.Type == "directory" || pkg.Resolution.Directory != "" {
			localPath := pkg.Resolution.Directory
			if opt.LockRoot != "" && !filepath.IsAbs(localPath) {
				localPath = filepath.Join(opt.LockRoot, filepath.FromSlash(localPath))
			}
			name, version, err := splitNameVersion(pkgID)
			if err != nil {
				name, version = it.linkName, "0.0.0"
			}
			ref := PackageRef{
				DepPath:   it.depPath,
				PackageID: pkgID,
				Name:      name,
				Version:   version,
				Optional:  optional,
				LocalPath: localPath,
				IsLocal:   true,
			}
			if st.outIdx >= 0 {
				out[st.outIdx] = ref
			} else {
				st.outIdx = len(out)
				out = append(out, ref)
			}
			st.done = true
			continue
		}

		if !platformMatch(pkg, plat) {
			if optional {
				st.done = true
				st.skippedPlatform = true
				continue
			}
			return nil, fmt.Errorf("required package %s does not support %s/%s (libc=%s)\nHint: this often means a native optional dependency was promoted to required, or the lock was generated on another OS. Re-lock on linux or adjust optionalDependencies", pkgID, plat.OS, plat.CPU, plat.Libc)
		}
		if muslOnly(pkg) && plat.Libc == "glibc" && !optional {
			return nil, fmt.Errorf("required package %s is musl-only (os/cpu/libc markers), but this build targets glibc\nHint: use glibc builds of the native package, or wait for --libc musl support with a musl Node base", pkgID)
		}
		name, version, err := splitNameVersion(pkgID)
		if err != nil {
			return nil, err
		}
		tarball := pkg.Resolution.Tarball
		if tarball == "" && pkg.Resolution.Type == "git" && pkg.Resolution.Repo != "" {
			tarball = gitArchiveURL(pkg.Resolution)
		}
		if tarball == "" {
			tarball = defaultRegistryTarball(name, version)
		}

		patchPath, patchHash := "", ""
		if e, ok := l.PatchedLookup(pkgID); ok {
			patchPath, patchHash = e.Path, e.Hash
		}

		if st.outIdx >= 0 {
			out[st.outIdx].Optional = optional
		} else {
			ref := PackageRef{
				DepPath:   it.depPath,
				PackageID: pkgID,
				Name:      name,
				Version:   version,
				Integrity: pkg.Resolution.Integrity,
				Tarball:   tarball,
				Optional:  optional,
				PatchPath: patchPath,
				PatchHash: patchHash,
			}
			st.outIdx = len(out)
			out = append(out, ref)
		}
		st.done = true
		st.optional = optional
		st.skippedPlatform = false

		snap := l.Snapshots[it.depPath]
		if snap == nil {
			snap = l.Snapshots[pkgID]
		}
		if snap == nil {
			continue
		}
		for depName, ver := range snap.Dependencies {
			if err := enqueue(depName, ver, optional); err != nil {
				return nil, err
			}
		}
		for depName, ver := range snap.OptionalDependencies {
			if err := enqueue(depName, ver, true); err != nil {
				return nil, err
			}
		}
	}
	return out, nil
}

func isLocalVersion(version string) bool {
	return strings.HasPrefix(version, "link:") ||
		strings.HasPrefix(version, "workspace:") ||
		strings.HasPrefix(version, "file:")
}

func localRef(l *lock.Lock, lockRoot, linkName, version, depPath string, optional bool) (PackageRef, error) {
	rel := version
	switch {
	case strings.HasPrefix(version, "link:"):
		rel = strings.TrimPrefix(version, "link:")
	case strings.HasPrefix(version, "file:"):
		rel = strings.TrimPrefix(version, "file:")
	case strings.HasPrefix(version, "workspace:"):
		// workspace:* without a path — resolve via importers / packages name.
		return resolveWorkspaceStar(l, lockRoot, linkName, version, depPath, optional)
	}
	localPath := rel
	if lockRoot != "" && !filepath.IsAbs(rel) {
		// pnpm link: paths are relative to the *importer* directory, not the
		// lock root. depPath is "name@link:../../packages/lib" for importer
		// apps/api → resolve from lockRoot/apps/api.
		base := lockRoot
		if importerDir := importerDirFromLinkDep(l, lockRoot, linkName, version); importerDir != "" {
			base = importerDir
		}
		localPath = filepath.Clean(filepath.Join(base, filepath.FromSlash(rel)))
	}
	name, ver := linkName, "0.0.0"
	if pj, err := readNameVersion(localPath); err == nil {
		if pj.name != "" {
			name = pj.name
		}
		if pj.version != "" {
			ver = pj.version
		}
	}
	pkgID := name + "@" + ver
	return PackageRef{
		DepPath:   depPath,
		PackageID: pkgID,
		Name:      name,
		Version:   ver,
		Optional:  optional,
		LocalPath: localPath,
		IsLocal:   true,
	}, nil
}

// importerDirFromLinkDep finds the importer directory that declares linkName
// with the given link:/file: version, so relative paths resolve correctly.
func importerDirFromLinkDep(l *lock.Lock, lockRoot, linkName, version string) string {
	for key, imp := range l.Importers {
		if imp == nil {
			continue
		}
		check := func(deps map[string]lock.ImporterDep) bool {
			if d, ok := deps[linkName]; ok && d.Version == version {
				return true
			}
			return false
		}
		if check(imp.Dependencies) || check(imp.OptionalDependencies) {
			if key == "" || key == "." {
				return lockRoot
			}
			return filepath.Join(lockRoot, filepath.FromSlash(key))
		}
	}
	return ""
}

func resolveWorkspaceStar(l *lock.Lock, lockRoot, linkName, version, depPath string, optional bool) (PackageRef, error) {
	// Prefer an importer whose package.json name matches linkName.
	if lockRoot != "" {
		for key := range l.Importers {
			if key == "" || key == "." {
				continue
			}
			dir := filepath.Join(lockRoot, filepath.FromSlash(key))
			pj, err := readNameVersion(dir)
			if err != nil {
				continue
			}
			if pj.name == linkName {
				ver := pj.version
				if ver == "" {
					ver = "0.0.0"
				}
				return PackageRef{
					DepPath:   depPath,
					PackageID: linkName + "@" + ver,
					Name:      linkName,
					Version:   ver,
					Optional:  optional,
					LocalPath: dir,
					IsLocal:   true,
				}, nil
			}
		}
	}
	return PackageRef{}, fmt.Errorf("workspace dependency %q (%s) could not be resolved to a workspace package directory\nHint: ensure the package is listed in pnpm-workspace.yaml and appears as an importer in the lock", linkName, version)
}

type nameVer struct {
	name, version string
}

func readNameVersion(dir string) (nameVer, error) {
	b, err := osReadFile(filepath.Join(dir, "package.json"))
	if err != nil {
		return nameVer{}, err
	}
	// Tiny parse to avoid importing encoding/json cycles in tests — use json.
	return parseNameVersionJSON(b)
}

// osReadFile / parseNameVersionJSON are thin wrappers so tests can stay simple.
var osReadFile = func(path string) ([]byte, error) {
	return readFile(path)
}

func gitArchiveURL(r lock.Resolution) string {
	repo := r.Repo
	commit := r.Commit
	if repo == "" || commit == "" {
		return ""
	}
	// Normalize git@github.com:org/repo.git and https://github.com/org/repo.git
	repo = strings.TrimSuffix(repo, ".git")
	repo = strings.TrimPrefix(repo, "git+")
	if strings.HasPrefix(repo, "git@github.com:") {
		repo = "https://github.com/" + strings.TrimPrefix(repo, "git@github.com:")
	}
	if strings.Contains(repo, "github.com/") {
		// https://github.com/org/repo → codeload archive
		parts := strings.Split(repo, "github.com/")
		if len(parts) == 2 {
			path := strings.TrimSuffix(parts[1], "/")
			return fmt.Sprintf("https://codeload.github.com/%s/tar.gz/%s", path, commit)
		}
	}
	return ""
}

func stripPatchHash(pkgID string) string {
	if i := strings.Index(pkgID, "(patch_hash="); i >= 0 {
		return pkgID[:i]
	}
	return pkgID
}

// DirectDeps returns production direct dependencies for an importer as
// (top-level link name, resolved dep path) pairs. Link names may be aliases.
func DirectDeps(l *lock.Lock, importerKey string) []DirectDep {
	imp := l.Importers[importerKey]
	if imp == nil {
		return nil
	}
	var out []DirectDep
	add := func(name string, d lock.ImporterDep) {
		if d.Version == "" {
			return
		}
		out = append(out, DirectDep{
			LinkName: name,
			DepPath:  DepPathFrom(name, d.Version),
		})
	}
	for name, d := range imp.Dependencies {
		add(name, d)
	}
	for name, d := range imp.OptionalDependencies {
		add(name, d)
	}
	sort.Slice(out, func(i, j int) bool {
		if out[i].LinkName != out[j].LinkName {
			return out[i].LinkName < out[j].LinkName
		}
		return out[i].DepPath < out[j].DepPath
	})
	return out
}

// DirectNames returns production direct dependency link names for an importer.
func DirectNames(l *lock.Lock, importerKey string) []string {
	deps := DirectDeps(l, importerKey)
	names := make([]string, 0, len(deps))
	for _, d := range deps {
		names = append(names, d.LinkName)
	}
	return names
}

func platformMatch(p *lock.Package, plat Platform) bool {
	if len(p.OS) > 0 && !containsOrAny(p.OS, plat.OS) {
		return false
	}
	if len(p.CPU) > 0 && !containsOrAny(p.CPU, plat.CPU) {
		return false
	}
	if len(p.Libc) > 0 && plat.Libc != "" && !containsOrAny(p.Libc, plat.Libc) {
		return false
	}
	return true
}

func containsOrAny(list []string, want string) bool {
	for _, v := range list {
		if v == want || v == "*" {
			return true
		}
		if strings.HasPrefix(v, "!") && v[1:] == want {
			return false
		}
	}
	onlyExclusions := true
	for _, v := range list {
		if !strings.HasPrefix(v, "!") {
			onlyExclusions = false
			break
		}
	}
	return onlyExclusions
}

func muslOnly(p *lock.Package) bool {
	if len(p.Libc) == 0 {
		return false
	}
	hasMusl, hasGlibc := false, false
	for _, v := range p.Libc {
		switch v {
		case "musl":
			hasMusl = true
		case "glibc":
			hasGlibc = true
		}
	}
	return hasMusl && !hasGlibc
}

// DepPathFrom builds a snapshots key from a dependency name + version field.
// Handles aliases where version is already a package id (e.g. name
// "strip-ansi-cjs" with version "strip-ansi@6.0.1").
func DepPathFrom(name, version string) string {
	if strings.HasPrefix(version, "link:") || strings.HasPrefix(version, "file:") {
		return name + "@" + version
	}
	if strings.HasPrefix(version, "workspace:") {
		return name + "@" + version
	}
	if strings.HasPrefix(version, name+"@") {
		return version
	}
	if strings.HasPrefix(version, "npm:") {
		version = strings.TrimPrefix(version, "npm:")
	}
	if looksLikePackageID(version) {
		return version
	}
	return name + "@" + version
}

func looksLikePackageID(s string) bool {
	if s == "" {
		return false
	}
	if strings.HasPrefix(s, "@") {
		rest := s[1:]
		at := strings.IndexByte(rest, '@')
		return at > 0 && strings.Contains(rest[:at], "/")
	}
	if s[0] >= '0' && s[0] <= '9' {
		return false
	}
	at := strings.IndexByte(s, '@')
	if at <= 0 {
		return false
	}
	if paren := strings.IndexByte(s, '('); paren >= 0 && paren < at {
		return false
	}
	return true
}

func depPathFrom(name, version string) string { return DepPathFrom(name, version) }

func splitNameVersion(id string) (name, version string, err error) {
	if strings.HasPrefix(id, "@") {
		i := strings.LastIndex(id, "@")
		if i <= 0 {
			return "", "", fmt.Errorf("bad package id %q", id)
		}
		return id[:i], id[i+1:], nil
	}
	i := strings.Index(id, "@")
	if i <= 0 {
		return "", "", fmt.Errorf("bad package id %q", id)
	}
	return id[:i], id[i+1:], nil
}

func defaultRegistryTarball(name, version string) string {
	base := name
	if i := strings.LastIndex(name, "/"); i >= 0 {
		base = name[i+1:]
	}
	escaped := strings.ReplaceAll(name, "/", "%2F")
	return fmt.Sprintf("https://registry.npmjs.org/%s/-/%s-%s.tgz", escaped, base, version)
}

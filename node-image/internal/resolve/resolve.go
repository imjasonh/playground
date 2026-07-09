package resolve

import (
	"fmt"
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

// Closure returns the production dependency closure for an importer.
func Closure(l *lock.Lock, importerKey string, plat Platform) ([]PackageRef, error) {
	imp := l.Importers[importerKey]
	if imp == nil {
		return nil, fmt.Errorf("importer %q not found in lockfile", importerKey)
	}
	type item struct {
		depPath  string
		optional bool
	}
	var queue []item
	state := map[string]*visitState{}

	enqueue := func(name, version string, optional bool) error {
		if version == "" || name == "" {
			return nil
		}
		if strings.HasPrefix(version, "link:") || strings.HasPrefix(version, "workspace:") || strings.HasPrefix(version, "file:") {
			return fmt.Errorf("importer dependency %q resolves to %q; workspace/link/file dependencies are not supported in image builds\nHint: bundle the workspace package into the app (e.g. tsc project references / bundler), publish it to a registry, or point node-image at a package that only depends on registry tarballs", name, version)
		}
		depPath := depPathFrom(name, version)
		st := state[depPath]
		if st == nil {
			state[depPath] = &visitState{optional: optional, outIdx: -1}
			queue = append(queue, item{depPath: depPath, optional: optional})
			return nil
		}
		if st.optional && !optional {
			// Upgrade optional → required.
			if st.skippedPlatform {
				return fmt.Errorf("required package %s does not support %s/%s (libc=%s)\nHint: this package was first reached as optional and skipped for this platform, but is also required via another path", depPath, plat.OS, plat.CPU, plat.Libc)
			}
			st.optional = false
			if st.done {
				if st.outIdx >= 0 {
					// Will be updated by caller after we have out; mark for re-queue
					// of children as required by re-enqueueing this node.
				}
				st.done = false
				queue = append(queue, item{depPath: depPath, optional: false})
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
		// Prefer required if upgraded while sitting in queue.
		optional := st.optional
		if st.done && optional {
			continue
		}
		if st.done && !optional {
			// Reprocessing after upgrade: refresh Optional flag and children.
			if st.outIdx >= 0 {
				out[st.outIdx].Optional = false
			}
		}

		pkgID := lock.PackageIDFromDepPath(it.depPath)
		pkgID = stripPatchHash(pkgID)
		pkg := l.Packages[pkgID]
		if pkg == nil {
			return nil, fmt.Errorf("package %s (from %s) missing from lock packages", pkgID, it.depPath)
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
		if tarball == "" {
			tarball = defaultRegistryTarball(name, version)
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
	if strings.HasPrefix(s, "@") {
		rest := s[1:]
		return strings.Count(rest, "@") >= 1 && strings.Contains(rest, "/")
	}
	if i := strings.IndexByte(s, '@'); i > 0 {
		return true
	}
	return false
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

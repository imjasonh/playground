package resolve

import (
	"fmt"
	"runtime"
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
	seen := map[string]bool{}

	enqueue := func(name, version string, optional bool) {
		if version == "" || name == "" {
			return
		}
		// Importer/snapshot values are usually "1.2.3" or "1.2.3(peer@1)",
		// not a full package id. Form the dep path as name@version…
		depPath := depPathFrom(name, version)
		if seen[depPath] {
			return
		}
		seen[depPath] = true
		queue = append(queue, item{depPath: depPath, optional: optional})
	}

	for name, d := range imp.Dependencies {
		enqueue(name, d.Version, false)
	}
	for name, d := range imp.OptionalDependencies {
		enqueue(name, d.Version, true)
	}
	// production only: skip DevDependencies

	var out []PackageRef
	for i := 0; i < len(queue); i++ {
		it := queue[i]
		pkgID := lock.PackageIDFromDepPath(it.depPath)
		pkg := l.Packages[pkgID]
		if pkg == nil {
			return nil, fmt.Errorf("package %s (from %s) missing from lock packages", pkgID, it.depPath)
		}
		if !platformMatch(pkg, plat) {
			if it.optional {
				continue
			}
			return nil, fmt.Errorf("required package %s does not support %s/%s (libc=%s)\nHint: this often means a native optional dependency was promoted to required, or the lock was generated on another OS. Re-lock on linux or adjust optionalDependencies", pkgID, plat.OS, plat.CPU, plat.Libc)
		}
		if muslOnly(pkg) && plat.Libc == "glibc" && !it.optional {
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
		ref := PackageRef{
			DepPath:   it.depPath,
			PackageID: pkgID,
			Name:      name,
			Version:   version,
			Integrity: pkg.Resolution.Integrity,
			Tarball:   tarball,
			Optional:  it.optional,
		}
		out = append(out, ref)

		snap := l.Snapshots[it.depPath]
		if snap == nil {
			// some locks only key snapshots by package id
			snap = l.Snapshots[pkgID]
		}
		if snap == nil {
			continue
		}
		for depName, ver := range snap.Dependencies {
			_ = depName
			enqueue(depName, ver, it.optional)
		}
		for depName, ver := range snap.OptionalDependencies {
			enqueue(depName, ver, true)
		}
	}
	return out, nil
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
		// pnpm uses "!win32" style exclusions
		if strings.HasPrefix(v, "!") && v[1:] == want {
			return false
		}
	}
	// if only exclusions present, allow when not excluded
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

// depPathFrom builds a snapshots key from a dependency name + version field.
func depPathFrom(name, version string) string {
	if strings.HasPrefix(version, name+"@") {
		return version
	}
	return name + "@" + version
}

func splitNameVersion(id string) (name, version string, err error) {
	// @scope/name@version or name@version
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
	// https://registry.npmjs.org/<name>/-/<basename>-<version>.tgz
	base := name
	if i := strings.LastIndex(name, "/"); i >= 0 {
		base = name[i+1:]
	}
	escaped := strings.ReplaceAll(name, "/", "%2F")
	return fmt.Sprintf("https://registry.npmjs.org/%s/-/%s-%s.tgz", escaped, base, version)
}

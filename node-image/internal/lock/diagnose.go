package lock

import (
	"fmt"
	"sort"
	"strings"
)

// Finding is one lock/resolve concern for diagnostics.
type Finding struct {
	Severity string // "error" or "warning"
	Code     string
	Message  string
	Hint     string
}

// Report collects findings for a selected importer (or the whole lock when
// importerKey is empty and AllPackages is true).
type Report struct {
	Findings []Finding
}

// HasErrors reports whether any finding is severity error.
func (r *Report) HasErrors() bool {
	for _, f := range r.Findings {
		if f.Severity == "error" {
			return true
		}
	}
	return false
}

// String formats all findings for stderr.
func (r *Report) String() string {
	if r == nil || len(r.Findings) == 0 {
		return "node-image diagnose: no issues found\n"
	}
	var b strings.Builder
	fmt.Fprintf(&b, "node-image diagnose: %d issue(s)\n", len(r.Findings))
	for i, f := range r.Findings {
		fmt.Fprintf(&b, "  %d. [%s] %s: %s\n", i+1, f.Severity, f.Code, f.Message)
		if f.Hint != "" {
			fmt.Fprintf(&b, "     Hint: %s\n", f.Hint)
		}
	}
	return b.String()
}

// DiagnoseOptions controls Diagnose.
type DiagnoseOptions struct {
	// ImporterKey selects which importer's prod closure to validate.
	// Empty means only lock-global notes (no per-package reachability filter).
	ImporterKey string
	// AllPackages when true (and ImporterKey empty) scans every packages entry.
	AllPackages bool
}

// Diagnose walks the lock and returns all findings instead of failing on the first.
// When ImporterKey is set, package-level issues are reported only for packages
// reachable from that importer's production dependencies (and optional deps).
func (l *Lock) Diagnose(opt DiagnoseOptions) *Report {
	r := &Report{}
	if l == nil {
		r.Findings = append(r.Findings, Finding{
			Severity: "error",
			Code:     "nil-lock",
			Message:  "lock is nil",
		})
		return r
	}

	reachable := map[string]bool{}
	if opt.ImporterKey != "" {
		reachable = l.reachablePackageIDs(opt.ImporterKey)
		if l.Importers[opt.ImporterKey] == nil {
			r.Findings = append(r.Findings, Finding{
				Severity: "error",
				Code:     "missing-importer",
				Message:  fmt.Sprintf("importer %q not found", opt.ImporterKey),
				Hint:     "point node-image at a workspace package directory that appears under importers in pnpm-lock.yaml",
			})
		}
	}

	if len(l.PatchedDependencies) > 0 {
		names := sortedKeys(l.PatchedDependencies)
		r.Findings = append(r.Findings, Finding{
			Severity: "warning",
			Code:     "patched-dependencies",
			Message:  fmt.Sprintf("lock records patchedDependencies (%s)", strings.Join(names, ", ")),
			Hint:     "node-image applies lock-recorded patches during extract when packaging",
		})
	}
	if len(l.Overrides) > 0 {
		r.Findings = append(r.Findings, Finding{
			Severity: "warning",
			Code:     "overrides",
			Message:  "lock records pnpm.overrides (graph already resolved in snapshots)",
			Hint:     "overrides are honored via the lock snapshot graph; no extra action needed",
		})
	}
	if len(l.Catalogs) > 0 {
		r.Findings = append(r.Findings, Finding{
			Severity: "warning",
			Code:     "catalogs",
			Message:  "lock records catalogs (specifiers should already be expanded on importer edges)",
			Hint:     "unresolved catalog: literals in the selected closure are errors",
		})
	}

	consider := func(id string, p *Package) {
		if p == nil {
			return
		}
		if opt.ImporterKey != "" && !reachable[PackageIDFromDepPath(id)] && !reachable[id] {
			// Also allow bare id without peer/patch suffix.
			base := PackageIDFromDepPath(id)
			base = stripPatchHashID(base)
			if !reachable[base] {
				return
			}
		}
		if p.Resolution.Type == "git" || strings.HasPrefix(p.Resolution.Tarball, "git+") {
			r.Findings = append(r.Findings, Finding{
				Severity: "warning",
				Code:     "git-dependency",
				Message:  fmt.Sprintf("package %s uses a git resolution", id),
				Hint:     "node-image fetches git/archive tarballs when integrity is present",
			})
		}
		if p.Resolution.Type == "directory" || p.Resolution.Directory != "" {
			r.Findings = append(r.Findings, Finding{
				Severity: "warning",
				Code:     "directory-dependency",
				Message:  fmt.Sprintf("package %s uses a directory resolution (%s)", id, p.Resolution.Directory),
				Hint:     "workspace/directory packages are materialized from the source tree",
			})
		}
		if strings.HasPrefix(p.Resolution.Tarball, "file:") || strings.HasPrefix(p.Resolution.Tarball, "link:") {
			r.Findings = append(r.Findings, Finding{
				Severity: "warning",
				Code:     "local-tarball",
				Message:  fmt.Sprintf("package %s uses local tarball %s", id, p.Resolution.Tarball),
			})
		}
		if p.Resolution.Integrity == "" && p.Resolution.Tarball == "" && p.Resolution.Type != "directory" && p.Resolution.Directory == "" {
			r.Findings = append(r.Findings, Finding{
				Severity: "error",
				Code:     "missing-integrity",
				Message:  fmt.Sprintf("package %s is missing integrity/tarball", id),
				Hint:     "run `pnpm install` to refresh the lock, or ensure the dependency resolves from a registry",
			})
		}
	}

	if opt.ImporterKey != "" || opt.AllPackages {
		ids := make([]string, 0, len(l.Packages))
		for id := range l.Packages {
			ids = append(ids, id)
		}
		sort.Strings(ids)
		for _, id := range ids {
			consider(id, l.Packages[id])
		}
	}

	// Unresolved catalog: only when the *version* field is still catalog:
	// (specifier may remain "catalog:" after pnpm expands version to a concrete pin).
	if opt.ImporterKey != "" {
		if imp := l.Importers[opt.ImporterKey]; imp != nil {
			checkCatalog := func(name, version string) {
				if strings.HasPrefix(version, "catalog:") {
					r.Findings = append(r.Findings, Finding{
						Severity: "error",
						Code:     "unresolved-catalog",
						Message:  fmt.Sprintf("dependency %q still has unresolved catalog version %q", name, version),
						Hint:     "re-lock with pnpm so catalog: expands to a concrete version",
					})
				}
			}
			for name, d := range imp.Dependencies {
				checkCatalog(name, d.Version)
			}
			for name, d := range imp.OptionalDependencies {
				checkCatalog(name, d.Version)
			}
		}
	}

	sort.Slice(r.Findings, func(i, j int) bool {
		if r.Findings[i].Severity != r.Findings[j].Severity {
			// errors first
			return r.Findings[i].Severity < r.Findings[j].Severity
		}
		return r.Findings[i].Code < r.Findings[j].Code
	})
	return r
}

func (l *Lock) reachablePackageIDs(importerKey string) map[string]bool {
	out := map[string]bool{}
	imp := l.Importers[importerKey]
	if imp == nil {
		return out
	}
	type item struct {
		depPath string
	}
	seen := map[string]bool{}
	var queue []item
	enqueue := func(name, version string) {
		if name == "" || version == "" {
			return
		}
		if strings.HasPrefix(version, "link:") || strings.HasPrefix(version, "workspace:") || strings.HasPrefix(version, "file:") {
			// Local packages don't appear under packages: — mark a synthetic id.
			out[name+"@"+version] = true
			return
		}
		depPath := name + "@" + version
		if strings.HasPrefix(version, name+"@") || looksLikePkgID(version) {
			depPath = version
			if strings.HasPrefix(version, "npm:") {
				depPath = strings.TrimPrefix(version, "npm:")
			}
		}
		if seen[depPath] {
			return
		}
		seen[depPath] = true
		queue = append(queue, item{depPath: depPath})
	}
	for name, d := range imp.Dependencies {
		enqueue(name, d.Version)
	}
	for name, d := range imp.OptionalDependencies {
		enqueue(name, d.Version)
	}
	for i := 0; i < len(queue); i++ {
		dp := queue[i].depPath
		pkgID := PackageIDFromDepPath(dp)
		pkgID = stripPatchHashID(pkgID)
		out[pkgID] = true
		out[dp] = true
		snap := l.Snapshots[dp]
		if snap == nil {
			snap = l.Snapshots[pkgID]
		}
		if snap == nil {
			continue
		}
		for depName, ver := range snap.Dependencies {
			enqueue(depName, ver)
		}
		for depName, ver := range snap.OptionalDependencies {
			enqueue(depName, ver)
		}
	}
	return out
}

func stripPatchHashID(pkgID string) string {
	if i := strings.Index(pkgID, "(patch_hash="); i >= 0 {
		return pkgID[:i]
	}
	return pkgID
}

func looksLikePkgID(s string) bool {
	if s == "" || (s[0] >= '0' && s[0] <= '9') {
		return false
	}
	if strings.HasPrefix(s, "@") {
		rest := s[1:]
		at := strings.IndexByte(rest, '@')
		return at > 0 && strings.Contains(rest[:at], "/")
	}
	return strings.Contains(s, "@")
}

func sortedKeys[T any](m map[string]T) []string {
	keys := make([]string, 0, len(m))
	for k := range m {
		keys = append(keys, k)
	}
	sort.Strings(keys)
	return keys
}

// PatchedEntry is one patchedDependencies value.
type PatchedEntry struct {
	Hash string `yaml:"hash"`
	Path string `yaml:"path"`
}

// PatchedLookup returns the patch entry for a package id like "ms@2.1.3".
func (l *Lock) PatchedLookup(packageID string) (PatchedEntry, bool) {
	if l == nil || l.PatchedDependencies == nil {
		return PatchedEntry{}, false
	}
	raw, ok := l.PatchedDependencies[packageID]
	if !ok {
		// Try without peer/patch suffix.
		base := stripPatchHashID(PackageIDFromDepPath(packageID))
		raw, ok = l.PatchedDependencies[base]
		if !ok {
			return PatchedEntry{}, false
		}
	}
	switch v := raw.(type) {
	case PatchedEntry:
		return v, true
	case map[string]any:
		e := PatchedEntry{}
		if h, ok := v["hash"].(string); ok {
			e.Hash = h
		}
		if p, ok := v["path"].(string); ok {
			e.Path = p
		}
		return e, e.Path != ""
	default:
		return PatchedEntry{}, false
	}
}

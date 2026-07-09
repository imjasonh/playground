package lock

import (
	"fmt"
	"os"
	"strings"

	"gopkg.in/yaml.v3"
)

// Lock is a parsed pnpm-lock.yaml (v9).
type Lock struct {
	LockfileVersion string                    `yaml:"lockfileVersion"`
	Importers       map[string]*Importer      `yaml:"importers"`
	Packages        map[string]*Package       `yaml:"packages"`
	Snapshots       map[string]*Snapshot      `yaml:"snapshots"`
}

// Importer is one workspace package / project root entry.
type Importer struct {
	Dependencies         map[string]ImporterDep `yaml:"dependencies"`
	DevDependencies      map[string]ImporterDep `yaml:"devDependencies"`
	OptionalDependencies map[string]ImporterDep `yaml:"optionalDependencies"`
}

// ImporterDep is a direct dependency pin from an importer.
type ImporterDep struct {
	Specifier string `yaml:"specifier"`
	Version   string `yaml:"version"`
}

// Package is metadata for a package id (name@version).
type Package struct {
	Resolution   Resolution      `yaml:"resolution"`
	Engines      map[string]string `yaml:"engines"`
	CPU          []string        `yaml:"cpu"`
	OS           []string        `yaml:"os"`
	Libc         []string        `yaml:"libc"`
	Deprecated   string          `yaml:"deprecated"`
	HasBin       bool            `yaml:"hasBin"`
	RequiresBuild bool           `yaml:"requiresBuild"`
}

// Resolution holds fetch identity.
type Resolution struct {
	Integrity string `yaml:"integrity"`
	Tarball   string `yaml:"tarball"`
	Type      string `yaml:"type"`
	Directory string `yaml:"directory"`
}

// Snapshot is the resolved dependency graph node (may include peer suffixes).
type Snapshot struct {
	Dependencies         map[string]string `yaml:"dependencies"`
	OptionalDependencies map[string]string `yaml:"optionalDependencies"`
}

// ParseFile reads and validates a pnpm-lock.yaml.
func ParseFile(path string) (*Lock, error) {
	b, err := os.ReadFile(path)
	if err != nil {
		return nil, err
	}
	return Parse(b)
}

// Parse parses lockfile bytes.
func Parse(b []byte) (*Lock, error) {
	var l Lock
	if err := yaml.Unmarshal(b, &l); err != nil {
		return nil, fmt.Errorf("parse pnpm-lock.yaml: %w", err)
	}
	ver := strings.TrimSpace(l.LockfileVersion)
	// YAML may parse 9.0 as number into string oddly; accept "9.0" / "9".
	if !strings.HasPrefix(ver, "9") {
		return nil, fmt.Errorf("unsupported pnpm lockfileVersion %q (alpha supports v9 only)", ver)
	}
	if l.Importers == nil {
		l.Importers = map[string]*Importer{}
	}
	if l.Packages == nil {
		l.Packages = map[string]*Package{}
	}
	if l.Snapshots == nil {
		l.Snapshots = map[string]*Snapshot{}
	}
	if err := l.checkUnsupported(); err != nil {
		return nil, err
	}
	return &l, nil
}

func (l *Lock) checkUnsupported() error {
	for id, p := range l.Packages {
		if p == nil {
			continue
		}
		if p.Resolution.Type == "git" || strings.HasPrefix(p.Resolution.Tarball, "git+") {
			return fmt.Errorf("package %s uses a git dependency, which node-image does not support yet\nHint: publish the package to an npm registry (or vendor a tarball with integrity) and re-lock with pnpm", id)
		}
		if p.Resolution.Type == "directory" || p.Resolution.Directory != "" {
			return fmt.Errorf("package %s uses a directory/file dependency, which node-image does not support yet\nHint: for workspace packages, point node-image at that package directory (it will use the parent lock); otherwise pack and publish the dependency", id)
		}
		if p.Resolution.Integrity == "" && p.Resolution.Tarball == "" {
			return fmt.Errorf("package %s is missing integrity/tarball in the lockfile\nHint: run `pnpm install` to refresh pnpm-lock.yaml, and ensure the dependency resolves from a registry", id)
		}
	}
	return nil
}

// PackageIDFromDepPath strips peer-suffix from a snapshot/dep path key.
// e.g. "foo@1.0.0(bar@2.0.0)" → "foo@1.0.0"
func PackageIDFromDepPath(depPath string) string {
	if i := strings.IndexByte(depPath, '('); i >= 0 {
		return depPath[:i]
	}
	return depPath
}

// FindLockfile walks from dir upward looking for pnpm-lock.yaml.
// Returns lock path and the directory containing it (lock root).
func FindLockfile(dir string) (lockPath, lockRoot string, err error) {
	cur, err := absClean(dir)
	if err != nil {
		return "", "", err
	}
	for {
		candidate := cur + string(os.PathSeparator) + "pnpm-lock.yaml"
		if st, err := os.Stat(candidate); err == nil && !st.IsDir() {
			return candidate, cur, nil
		}
		parent := parentDir(cur)
		if parent == cur {
			return "", "", fmt.Errorf("pnpm-lock.yaml not found starting from %s\nHint: run `pnpm install` in the app (or workspace root) to create pnpm-lock.yaml, or `pnpm import` from another lockfile", dir)
		}
		cur = parent
	}
}

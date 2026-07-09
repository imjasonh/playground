package layout

import (
	"fmt"
	"path"
	"path/filepath"
	"strings"
	"unicode"
)

// validNodeModulesName reports whether name is a safe single node_modules entry
// (unscoped package, scoped @scope/name, or a simple alias). Rejects path
// traversal and empty segments. Matches npm package-name shape closely enough
// that normal lockfiles pass; crafted "../" link names fail closed.
func validNodeModulesName(name string) bool {
	name = strings.TrimSpace(name)
	if name == "" || name == "." || name == ".." {
		return false
	}
	if strings.Contains(name, "\\") || strings.Contains(name, "\x00") {
		return false
	}
	// Disallow absolute and parent traversal in any form.
	if filepath.IsAbs(name) || strings.HasPrefix(name, "/") {
		return false
	}
	for _, part := range strings.Split(filepath.ToSlash(name), "/") {
		if part == "" || part == "." || part == ".." {
			return false
		}
		for _, r := range part {
			if r < 0x20 || r == 0x7f {
				return false
			}
		}
	}
	slash := strings.Count(name, "/")
	if strings.HasPrefix(name, "@") {
		// @scope/name only (exactly one slash)
		if slash != 1 {
			return false
		}
		scope, pkg, _ := strings.Cut(name[1:], "/")
		return isNPMNameSegment(scope) && isNPMNameSegment(pkg)
	}
	if slash != 0 {
		return false
	}
	return isNPMNameSegment(name)
}

func isNPMNameSegment(s string) bool {
	if s == "" || len(s) > 214 {
		return false
	}
	if s[0] == '.' || s[0] == '_' {
		return false
	}
	for _, r := range s {
		if unicode.IsLetter(r) || unicode.IsDigit(r) {
			continue
		}
		switch r {
		case '-', '_', '.', '+':
			continue
		default:
			return false
		}
	}
	return true
}

// validBinName is the left-hand side of package.json#bin (the command name
// under node_modules/.bin). Must be a single path segment.
func validBinName(name string) bool {
	if name == "" || name == "." || name == ".." {
		return false
	}
	if strings.ContainsAny(name, `/\`) || strings.Contains(name, "\x00") {
		return false
	}
	return !strings.Contains(name, "..")
}

// safeBinRel returns a cleaned package-relative bin target, or false if it
// would escape the package directory. Mirrors pnpm's is-subdir check: bin
// targets must resolve under the package root.
func safeBinRel(rel string) (string, bool) {
	rel = strings.TrimSpace(rel)
	if rel == "" {
		return "", false
	}
	rel = filepath.ToSlash(rel)
	if filepath.IsAbs(rel) || strings.HasPrefix(rel, "/") {
		return "", false
	}
	clean := path.Clean(rel)
	if clean == ".." || strings.HasPrefix(clean, "../") {
		return "", false
	}
	return clean, true
}

// safeLayerRel rejects layer paths that escape via ".." or absolute form.
func safeLayerRel(rel string) error {
	rel = filepath.ToSlash(rel)
	if rel == "" {
		return fmt.Errorf("empty layer path")
	}
	if filepath.IsAbs(rel) || strings.HasPrefix(rel, "/") {
		return fmt.Errorf("absolute layer path %q", rel)
	}
	for _, part := range strings.Split(rel, "/") {
		if part == ".." {
			return fmt.Errorf("layer path escapes with ..: %q", rel)
		}
		if part == "" {
			return fmt.Errorf("empty segment in layer path %q", rel)
		}
	}
	return nil
}

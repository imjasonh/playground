// Package pathglob matches slash-separated file paths against globs
// that include `**` (zero or more directories).
package pathglob

import (
	"fmt"
	"path"
	"strings"
)

// Match reports whether name matches pattern. Both sides are
// slash-normalized; `**` matches zero or more path segments. The
// pattern is tried against the full path and every `/`-suffix, so
// `ios/**/project.yml` matches `ios/project.yml` and
// `/abs/ios/nested/project.yml`.
func Match(pattern, name string) bool {
	if pattern == "" {
		return false
	}
	pat := split(pattern)
	if len(pat) == 0 {
		return false
	}
	for _, candidate := range suffixes(name) {
		if matchSegs(pat, candidate) {
			return true
		}
	}
	return false
}

// Valid reports whether pattern is a usable glob. Empty patterns and
// malformed character classes (the same errors path.Match returns)
// are rejected.
func Valid(pattern string) error {
	if strings.TrimSpace(pattern) == "" {
		return fmt.Errorf("empty glob")
	}
	for _, seg := range split(pattern) {
		if seg == "**" {
			continue
		}
		if _, err := path.Match(seg, "x"); err != nil {
			return err
		}
	}
	return nil
}

func split(p string) []string {
	p = strings.ReplaceAll(p, `\`, "/")
	p = strings.TrimPrefix(p, "./")
	p = strings.Trim(p, "/")
	if p == "" {
		return nil
	}
	return strings.Split(p, "/")
}

func suffixes(name string) [][]string {
	segs := split(name)
	if len(segs) == 0 {
		return nil
	}
	out := make([][]string, 0, len(segs))
	for i := 0; i < len(segs); i++ {
		out = append(out, segs[i:])
	}
	return out
}

func matchSegs(pat, nam []string) bool {
	for len(pat) > 0 {
		if pat[0] == "**" {
			for len(pat) > 0 && pat[0] == "**" {
				pat = pat[1:]
			}
			if len(pat) == 0 {
				return true
			}
			for i := 0; i <= len(nam); i++ {
				if matchSegs(pat, nam[i:]) {
					return true
				}
			}
			return false
		}
		if len(nam) == 0 {
			return false
		}
		ok, err := path.Match(pat[0], nam[0])
		if err != nil || !ok {
			return false
		}
		pat = pat[1:]
		nam = nam[1:]
	}
	return len(nam) == 0
}

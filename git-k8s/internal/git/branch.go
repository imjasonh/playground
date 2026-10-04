package git

import "strings"

// ValidBranch reports whether git accepts name as a branch name.
func ValidBranch(name string) bool {
	if name == "" || name == "@" || name[0] == '-' || strings.HasSuffix(name, ".") ||
		strings.Contains(name, "..") || strings.Contains(name, "@{") || strings.ContainsAny(name, " ~^:?*[\\") ||
		strings.ContainsFunc(name, func(r rune) bool { return r < 0x20 || r == 0x7f }) {
		return false
	}
	for part := range strings.SplitSeq(name, "/") {
		if part == "" || part[0] == '.' || strings.HasSuffix(part, ".lock") {
			return false
		}
	}
	return true
}

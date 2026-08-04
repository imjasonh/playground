// Package image validates OCI image references for deploy.
package image

import (
	"fmt"
	"regexp"
	"strings"
)

// digestPinnedRE matches a reference that pins an image by sha256 digest.
// Accepts repo@sha256:… and repo:tag@sha256:….
var digestPinnedRE = regexp.MustCompile(`(?i)@sha256:([0-9a-f]{64})$`)

// ValidateDigestPinned rejects unpinned tags and malformed digests.
func ValidateDigestPinned(ref string) error {
	ref = strings.TrimSpace(ref)
	if ref == "" {
		return fmt.Errorf("image is empty")
	}
	if strings.ContainsAny(ref, " \t\n\r") {
		return fmt.Errorf("image must not contain whitespace")
	}
	m := digestPinnedRE.FindStringSubmatch(ref)
	if m == nil {
		return fmt.Errorf("image must be digest-pinned (repo@sha256:<64 hex>), got %q", ref)
	}
	// Reject "@sha256:…" with no repository.
	prefix := ref[:len(ref)-len(m[0])]
	if prefix == "" {
		return fmt.Errorf("image missing repository before digest")
	}
	return nil
}

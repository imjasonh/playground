// Package image validates OCI image references for deploy.
package image

import (
	"fmt"
	"regexp"
	"strings"

	"github.com/google/go-containerregistry/pkg/name"
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
	if _, err := name.NewDigest(ref, name.StrictValidation); err != nil {
		return fmt.Errorf("invalid image reference: %w", err)
	}
	return nil
}

// ValidateAllowedRegistry applies an operator-owned registry allowlist after
// syntax/digest validation. Entries are exact hosts or "*.suffix" patterns.
// Empty allowed leaves the policy disabled for explicit local development.
func ValidateAllowedRegistry(ref string, allowed []string) error {
	if err := ValidateDigestPinned(ref); err != nil {
		return err
	}
	if len(allowed) == 0 {
		return nil
	}
	digest, err := name.NewDigest(strings.TrimSpace(ref), name.StrictValidation)
	if err != nil {
		return err
	}
	host := strings.ToLower(digest.Context().RegistryStr())
	for _, raw := range allowed {
		entry := strings.ToLower(strings.TrimSpace(raw))
		if entry == host {
			return nil
		}
		if suffix, ok := strings.CutPrefix(entry, "*."); ok &&
			strings.HasSuffix(host, "."+suffix) && host != suffix {
			return nil
		}
	}
	return fmt.Errorf("registry %q is not allowed", host)
}

// ParseRegistryAllowlist parses a comma-separated registry host policy.
func ParseRegistryAllowlist(raw string) []string {
	var out []string
	for _, item := range strings.Split(raw, ",") {
		if item = strings.ToLower(strings.TrimSpace(item)); item != "" {
			out = append(out, item)
		}
	}
	return out
}

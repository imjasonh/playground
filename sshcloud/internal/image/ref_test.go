package image

import (
	"strings"
	"testing"
)

func TestValidateDigestPinned(t *testing.T) {
	t.Parallel()
	digest := "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"
	ok := []string{
		"ghcr.io/me/app@sha256:" + digest,
		"ghcr.io/me/app:v1@sha256:" + digest,
		"docker.io/library/alpine@sha256:" + digest,
	}
	for _, ref := range ok {
		if err := ValidateDigestPinned(ref); err != nil {
			t.Fatalf("%q: %v", ref, err)
		}
	}
	bad := []string{
		"",
		"ghcr.io/me/app:latest",
		"ghcr.io/me/app",
		"@sha256:" + digest,
		"ghcr.io/me/app@sha256:deadbeef",
		"ghcr.io/me/app @sha256:" + digest,
	}
	for _, ref := range bad {
		if err := ValidateDigestPinned(ref); err == nil {
			t.Fatalf("expected error for %q", ref)
		}
	}
}

func TestValidateAllowedRegistry(t *testing.T) {
	t.Parallel()
	digest := strings.Repeat("a", 64)
	for _, ref := range []string{
		"ghcr.io/me/app@sha256:" + digest,
		"us-central1-docker.pkg.dev/project/repo/app@sha256:" + digest,
	} {
		if err := ValidateAllowedRegistry(ref, []string{"ghcr.io", "*.pkg.dev"}); err != nil {
			t.Fatalf("%s: %v", ref, err)
		}
	}
	err := ValidateAllowedRegistry("10.20.0.4:5000/app@sha256:"+digest, []string{"ghcr.io", "*.pkg.dev"})
	if err == nil || !strings.Contains(err.Error(), "not allowed") {
		t.Fatalf("expected registry rejection, got %v", err)
	}
}

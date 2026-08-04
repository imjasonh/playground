package image

import "testing"

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

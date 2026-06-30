package registry

import (
	"testing"

	v1 "github.com/google/go-containerregistry/pkg/v1"
)

func TestSplitPlatform(t *testing.T) {
	cases := []struct {
		in                string
		os, arch, variant string
	}{
		{"linux/amd64", "linux", "amd64", ""},
		{"linux/arm/v7", "linux", "arm", "v7"},
		{"linux", "linux", "", ""},
		{"", "", "", ""},
	}
	for _, c := range cases {
		os, arch, variant := splitPlatform(c.in)
		if os != c.os || arch != c.arch || variant != c.variant {
			t.Errorf("splitPlatform(%q) = (%q,%q,%q), want (%q,%q,%q)", c.in, os, arch, variant, c.os, c.arch, c.variant)
		}
	}
}

func TestIsAttestation(t *testing.T) {
	att := v1.Descriptor{Platform: &v1.Platform{OS: "unknown", Architecture: "unknown"}}
	if !isAttestation(att) {
		t.Error("unknown/unknown should be an attestation")
	}
	real := v1.Descriptor{Platform: &v1.Platform{OS: "linux", Architecture: "amd64"}}
	if isAttestation(real) {
		t.Error("linux/amd64 should not be an attestation")
	}
	if isAttestation(v1.Descriptor{}) {
		t.Error("descriptor without platform should not be an attestation")
	}
}

func TestPickPlatform(t *testing.T) {
	children := []v1.Descriptor{
		{Platform: &v1.Platform{OS: "linux", Architecture: "amd64"}},
		{Platform: &v1.Platform{OS: "linux", Architecture: "arm", Variant: "v7"}},
		{Platform: &v1.Platform{OS: "unknown", Architecture: "unknown"}},
	}
	if _, err := pickPlatform(children, "linux/amd64"); err != nil {
		t.Errorf("pickPlatform amd64: %v", err)
	}
	if _, err := pickPlatform(children, "linux/arm/v7"); err != nil {
		t.Errorf("pickPlatform arm/v7: %v", err)
	}
	if _, err := pickPlatform(children, "windows/amd64"); err == nil {
		t.Error("expected error for windows/amd64")
	}
}

func TestDigestFile(t *testing.T) {
	if got := digestFile("sha256:abc123"); got != "sha256-abc123" {
		t.Errorf("digestFile = %q, want sha256-abc123", got)
	}
}

func TestHashKeyStable(t *testing.T) {
	a := hashKey("index.docker.io/library/nginx")
	b := hashKey("index.docker.io/library/nginx")
	c := hashKey("index.docker.io/library/redis")
	if a != b {
		t.Error("hashKey should be deterministic")
	}
	if a == c {
		t.Error("different inputs should hash differently")
	}
	if len(a) != 64 {
		t.Errorf("hashKey length = %d, want 64 (sha256 hex)", len(a))
	}
}

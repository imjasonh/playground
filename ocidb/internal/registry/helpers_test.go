package registry

import (
	"archive/tar"
	"bytes"
	"compress/gzip"
	"io"
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

func TestNormalizeTarPath(t *testing.T) {
	cases := map[string]string{
		"etc/os-release":   "/etc/os-release",
		"./etc/os-release": "/etc/os-release",
		"/etc/os-release":  "/etc/os-release",
		"etc/":             "/etc/",
		"":                 "/",
	}
	for in, want := range cases {
		if got := normalizeTarPath(in); got != want {
			t.Errorf("normalizeTarPath(%q) = %q, want %q", in, got, want)
		}
	}
}

func TestTarType(t *testing.T) {
	cases := map[byte]string{
		tar.TypeReg:     "file",
		tar.TypeDir:     "dir",
		tar.TypeSymlink: "symlink",
		tar.TypeLink:    "hardlink",
		tar.TypeFifo:    "fifo",
		byte('Z'):       "other",
	}
	for flag, want := range cases {
		if got := tarType(flag); got != want {
			t.Errorf("tarType(%q) = %q, want %q", flag, got, want)
		}
	}
}

func TestDecompressAndWalkTOC(t *testing.T) {
	// Uncompressed input is passed through unchanged.
	rc, err := decompress([]byte("plain bytes"))
	if err != nil {
		t.Fatal(err)
	}
	b, _ := io.ReadAll(rc)
	rc.Close()
	if string(b) != "plain bytes" {
		t.Errorf("raw decompress = %q, want %q", b, "plain bytes")
	}

	// A gzipped tar round-trips through decompress + walkTOC.
	var buf bytes.Buffer
	zw := gzip.NewWriter(&buf)
	tw := tar.NewWriter(zw)
	_ = tw.WriteHeader(&tar.Header{Name: "a.txt", Mode: 0o644, Size: 3, Typeflag: tar.TypeReg})
	_, _ = tw.Write([]byte("abc"))
	_ = tw.WriteHeader(&tar.Header{Name: "d/", Mode: 0o755, Typeflag: tar.TypeDir})
	_ = tw.Close()
	_ = zw.Close()

	toc, err := walkTOC(buf.Bytes())
	if err != nil {
		t.Fatalf("walkTOC: %v", err)
	}
	if len(toc) != 2 {
		t.Fatalf("toc len = %d, want 2", len(toc))
	}
	if toc[0].Path != "/a.txt" || toc[0].Type != "file" || toc[0].Size != 3 {
		t.Errorf("entry0 = %+v, want /a.txt file size 3", toc[0])
	}
	if toc[1].Path != "/d/" || toc[1].Type != "dir" {
		t.Errorf("entry1 = %+v, want /d/ dir", toc[1])
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

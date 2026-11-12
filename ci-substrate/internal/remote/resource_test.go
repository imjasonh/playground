package remote

import (
	"testing"

	repb "github.com/bazelbuild/remote-apis/build/bazel/remote/execution/v2"
)

func fakeDigest(hash string, size int64) *repb.Digest {
	return &repb.Digest{Hash: hash, SizeBytes: size}
}

func TestReadResourceRoundTrip(t *testing.T) {
	cases := []string{"", "tenant-a", "shared/nested"}
	for _, inst := range cases {
		d := fakeDigest("abc123", 42)
		name := ReadResourceName(inst, d)
		gotInst, gotD, err := ParseReadResource(name)
		if err != nil {
			t.Fatalf("ParseReadResource(%q): %v", name, err)
		}
		if gotInst != inst {
			t.Errorf("instance = %q, want %q", gotInst, inst)
		}
		if gotD.GetHash() != "abc123" || gotD.GetSizeBytes() != 42 {
			t.Errorf("digest = %v", gotD)
		}
	}
}

func TestWriteResourceRoundTrip(t *testing.T) {
	d := fakeDigest("deadbeef", 7)
	name := WriteResourceName("tenant-b", "uuid-1", d)
	gotInst, gotD, err := ParseWriteResource(name)
	if err != nil {
		t.Fatalf("ParseWriteResource(%q): %v", name, err)
	}
	if gotInst != "tenant-b" {
		t.Errorf("instance = %q, want tenant-b", gotInst)
	}
	if gotD.GetHash() != "deadbeef" || gotD.GetSizeBytes() != 7 {
		t.Errorf("digest = %v", gotD)
	}
}

func TestParseRejectsGarbage(t *testing.T) {
	if _, _, err := ParseReadResource("tenant-a/nope/abc/1"); err == nil {
		t.Error("ParseReadResource accepted a name without a blobs segment")
	}
	if _, _, err := ParseWriteResource("tenant-a/blobs/abc/1"); err == nil {
		t.Error("ParseWriteResource accepted a read-style name")
	}
	if _, _, err := ParseReadResource("tenant-a/blobs/abc/notanumber"); err == nil {
		t.Error("ParseReadResource accepted a non-numeric size")
	}
}

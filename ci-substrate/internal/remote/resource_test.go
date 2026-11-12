package remote

import (
	"testing"

	"github.com/imjasonh/playground/ci-substrate/internal/digest"
)

func TestReadResourceRoundTrip(t *testing.T) {
	cases := []string{"", "tenant-a", "shared/nested"}
	for _, inst := range cases {
		d := digest.FromBytes([]byte("read resource"))
		name := ReadResourceName(inst, d)
		gotInst, gotD, err := ParseReadResource(name)
		if err != nil {
			t.Fatalf("ParseReadResource(%q): %v", name, err)
		}
		if gotInst != inst {
			t.Errorf("instance = %q, want %q", gotInst, inst)
		}
		if digest.Key(gotD) != digest.Key(d) {
			t.Errorf("digest = %v", gotD)
		}
	}
}

func TestWriteResourceRoundTrip(t *testing.T) {
	d := digest.FromBytes([]byte("write resource"))
	name := WriteResourceName("tenant-b", "uuid-1", d)
	gotInst, gotD, err := ParseWriteResource(name)
	if err != nil {
		t.Fatalf("ParseWriteResource(%q): %v", name, err)
	}
	if gotInst != "tenant-b" {
		t.Errorf("instance = %q, want tenant-b", gotInst)
	}
	if digest.Key(gotD) != digest.Key(d) {
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
	if _, _, err := ParseReadResource("tenant-a/blobs/" + digest.FromBytes(nil).GetHash() + "/notanumber"); err == nil {
		t.Error("ParseReadResource accepted a non-numeric size")
	}
	if _, _, err := ParseReadResource("tenant-a/blobs/../../etc/passwd/1"); err == nil {
		t.Error("ParseReadResource accepted a path-traversal hash")
	}
}

package remote

import (
	"testing"

	repb "github.com/bazelbuild/remote-apis/build/bazel/remote/execution/v2"

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

func TestCompressedResources(t *testing.T) {
	d := digest.FromBytes([]byte("compressed payload"))
	for _, tc := range []struct {
		inst string
		comp repb.Compressor_Value
	}{
		{"", repb.Compressor_ZSTD},
		{"tenant-a", repb.Compressor_ZSTD},
		{"shared/nested", repb.Compressor_DEFLATE},
	} {
		rname := CompressedReadResourceName(tc.inst, tc.comp, d)
		gotInst, gotD, gotC, err := ParseReadResourceCompressed(rname)
		if err != nil {
			t.Fatalf("ParseReadResourceCompressed(%q): %v", rname, err)
		}
		if gotInst != tc.inst || digest.Key(gotD) != digest.Key(d) || gotC != tc.comp {
			t.Errorf("got (%q, %v, %v), want (%q, %v, %v)", gotInst, gotD, gotC, tc.inst, d, tc.comp)
		}

		wname := CompressedWriteResourceName(tc.inst, "uuid-9", tc.comp, d)
		gotInst, gotD, gotC, err = ParseWriteResourceCompressed(wname)
		if err != nil {
			t.Fatalf("ParseWriteResourceCompressed(%q): %v", wname, err)
		}
		if gotInst != tc.inst || digest.Key(gotD) != digest.Key(d) || gotC != tc.comp {
			t.Errorf("write got (%q, %v, %v), want (%q, %v, %v)", gotInst, gotD, gotC, tc.inst, d, tc.comp)
		}
	}

	// Optional sha256 digest function path segment is accepted.
	withFn := "tenant-a/compressed-blobs/zstd/sha256/" + d.GetHash() + "/18"
	if inst, gotD, comp, err := ParseReadResourceCompressed(withFn); err != nil || inst != "tenant-a" || comp != repb.Compressor_ZSTD || digest.Key(gotD) != digest.Key(d) {
		t.Errorf("ParseReadResourceCompressed with sha256 = (%q, %v, %v, %v)", inst, gotD, comp, err)
	}
}

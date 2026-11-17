package digest

import (
	"slices"
	"strings"
	"testing"

	repb "github.com/bazelbuild/remote-apis/build/bazel/remote/execution/v2"
)

func TestFromBytesEmpty(t *testing.T) {
	// The SHA-256 of the empty string is a fixed, well-known constant.
	const wantEmpty = "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
	d := FromBytes(nil)
	if d.GetHash() != wantEmpty {
		t.Errorf("hash = %s, want %s", d.GetHash(), wantEmpty)
	}
	if d.GetSizeBytes() != 0 {
		t.Errorf("size = %d, want 0", d.GetSizeBytes())
	}
}

func TestVerify(t *testing.T) {
	b := []byte("hello remote execution")
	d := FromBytes(b)

	if err := Verify(d, b); err != nil {
		t.Fatalf("Verify of matching bytes: %v", err)
	}

	t.Run("tampered content keeps size", func(t *testing.T) {
		poisoned := append([]byte(nil), b...)
		poisoned[0] ^= 0xff
		if err := Verify(d, poisoned); err == nil {
			t.Error("Verify accepted tampered bytes of the same length")
		}
	})

	t.Run("truncated", func(t *testing.T) {
		if err := Verify(d, b[:len(b)-1]); err == nil {
			t.Error("Verify accepted truncated bytes")
		}
	})
}

func TestValidate(t *testing.T) {
	if err := Validate(FromBytes([]byte("ok"))); err != nil {
		t.Errorf("Validate of a real digest: %v", err)
	}
	for _, d := range []*repb.Digest{
		nil,
		{Hash: "deadbeef", SizeBytes: 1},
		{Hash: "../" + FromBytes(nil).GetHash()[3:], SizeBytes: 0},
		{Hash: strings.ToUpper(FromBytes(nil).GetHash()), SizeBytes: 0},
		{Hash: FromBytes(nil).GetHash(), SizeBytes: -1},
	} {
		if err := Validate(d); err == nil {
			t.Errorf("Validate(%v) accepted a malformed digest", d)
		}
	}
}

func TestBatches(t *testing.T) {
	for _, tc := range []struct {
		name     string
		sizes    []int64
		maxCount int
		maxBytes int64
		want     []int
	}{
		{name: "empty", maxCount: 2, maxBytes: 10},
		{name: "one run", sizes: []int64{1, 2, 3}, maxCount: 3, maxBytes: 10, want: []int{3}},
		{name: "count", sizes: []int64{1, 1, 1, 1, 1}, maxCount: 2, maxBytes: 10, want: []int{2, 2, 1}},
		{name: "bytes", sizes: []int64{4, 4, 4, 1}, maxCount: 10, maxBytes: 8, want: []int{2, 2}},
		{name: "oversized alone", sizes: []int64{1, 20, 1}, maxCount: 10, maxBytes: 8, want: []int{1, 1, 1}},
		{name: "oversized first", sizes: []int64{20, 1, 1}, maxCount: 10, maxBytes: 8, want: []int{1, 2}},
	} {
		t.Run(tc.name, func(t *testing.T) {
			var ds []*repb.Digest
			for _, s := range tc.sizes {
				ds = append(ds, &repb.Digest{SizeBytes: s})
			}
			var got []int
			var flat []*repb.Digest
			for _, b := range Batches(ds, tc.maxCount, tc.maxBytes) {
				got = append(got, len(b))
				flat = append(flat, b...)
			}
			if !slices.Equal(got, tc.want) {
				t.Errorf("run lengths = %v, want %v", got, tc.want)
			}
			if !slices.Equal(flat, ds) {
				t.Error("runs don't hold ds in order")
			}
		})
	}
}

func TestKeyIgnoresTenant(t *testing.T) {
	b := []byte("shared base layer")
	// Two independently computed digests of the same bytes must collide, so a
	// shared blob is one cache entry no matter which tenant asked first.
	if k1, k2 := Key(FromBytes(b)), Key(FromBytes(b)); k1 != k2 {
		t.Errorf("keys differ for identical content: %s vs %s", k1, k2)
	}
	if Key(FromBytes(b)) == Key(&repb.Digest{Hash: "deadbeef", SizeBytes: 1}) {
		t.Error("keys collided for different content")
	}
}

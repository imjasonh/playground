// Package digest computes and verifies content-addressable digests in the
// form the Bazel Remote Execution API uses: a lowercase hex SHA-256 and a
// byte count.
package digest

import (
	"crypto/sha256"
	"encoding/hex"
	"fmt"

	repb "github.com/bazelbuild/remote-apis/build/bazel/remote/execution/v2"
)

// FromBytes returns the digest of b.
func FromBytes(b []byte) *repb.Digest {
	sum := sha256.Sum256(b)
	return &repb.Digest{Hash: hex.EncodeToString(sum[:]), SizeBytes: int64(len(b))}
}

// Validate reports whether d is a well-formed SHA-256 digest: 64 lowercase hex
// characters and a non-negative size. Stores use the hash as a file name, so
// every digest that arrives from a client must pass this before it touches
// disk.
func Validate(d *repb.Digest) error {
	if d == nil {
		return fmt.Errorf("missing digest")
	}
	h := d.GetHash()
	if len(h) != sha256.Size*2 {
		return fmt.Errorf("invalid hash %q: want %d hex characters", h, sha256.Size*2)
	}
	for _, c := range h {
		if (c < '0' || c > '9') && (c < 'a' || c > 'f') {
			return fmt.Errorf("invalid hash %q: want lowercase hex", h)
		}
	}
	if d.GetSizeBytes() < 0 {
		return fmt.Errorf("invalid size %d", d.GetSizeBytes())
	}
	return nil
}

// Verify reports whether b matches d in both size and SHA-256 hash. It is the
// cryptographic check every cache and store runs before trusting bytes it did
// not produce itself, so a tampered or truncated blob never passes as its
// digest.
func Verify(d *repb.Digest, b []byte) error {
	if got := int64(len(b)); got != d.GetSizeBytes() {
		return fmt.Errorf("size mismatch for %s: have %d bytes", d.GetHash(), got)
	}
	sum := sha256.Sum256(b)
	if got := hex.EncodeToString(sum[:]); got != d.GetHash() {
		return fmt.Errorf("hash mismatch: want %s, have %s", d.GetHash(), got)
	}
	return nil
}

// Key is a stable map key that identifies a blob by content alone, independent
// of any tenant. Two tenants that hold identical bytes share one key, which is
// what lets a content-addressed cache serve both from a single copy.
func Key(d *repb.Digest) string {
	return fmt.Sprintf("%s/%d", d.GetHash(), d.GetSizeBytes())
}

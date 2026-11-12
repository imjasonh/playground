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

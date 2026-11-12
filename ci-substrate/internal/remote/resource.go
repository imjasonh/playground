package remote

import (
	"fmt"
	"strconv"
	"strings"

	repb "github.com/bazelbuild/remote-apis/build/bazel/remote/execution/v2"

	"github.com/imjasonh/playground/ci-substrate/internal/digest"
)

// MaxBatchBytes is the largest total payload the batch CAS methods accept.
// Larger blobs must use the ByteStream API, and the client routes uploads and
// reads by it. It sits below gRPC's default 4 MiB message limit because that
// limit also counts the digests and framing around the data.
const MaxBatchBytes = 4*1024*1024 - 64*1024

// parseDigest splits a "hash/size" pair from a ByteStream resource name.
func parseDigest(hash, size string) (*repb.Digest, error) {
	n, err := strconv.ParseInt(size, 10, 64)
	if err != nil {
		return nil, fmt.Errorf("bad size %q: %w", size, err)
	}
	d := &repb.Digest{Hash: hash, SizeBytes: n}
	if err := digest.Validate(d); err != nil {
		return nil, err
	}
	return d, nil
}

// ParseReadResource parses a ByteStream read resource name of the form
// "{instance_name}/blobs/{hash}/{size}". The instance name may be empty or
// contain slashes.
func ParseReadResource(name string) (instance string, d *repb.Digest, err error) {
	parts := strings.Split(name, "/")
	for i := 0; i+2 < len(parts); i++ {
		if parts[i] == "blobs" {
			d, err := parseDigest(parts[i+1], parts[i+2])
			if err != nil {
				return "", nil, err
			}
			return strings.Join(parts[:i], "/"), d, nil
		}
	}
	return "", nil, fmt.Errorf("invalid read resource %q", name)
}

// ParseWriteResource parses a ByteStream write resource name of the form
// "{instance_name}/uploads/{uuid}/blobs/{hash}/{size}{/optional}".
func ParseWriteResource(name string) (instance string, d *repb.Digest, err error) {
	parts := strings.Split(name, "/")
	for i := 0; i+4 < len(parts); i++ {
		if parts[i] == "uploads" && parts[i+2] == "blobs" {
			d, err := parseDigest(parts[i+3], parts[i+4])
			if err != nil {
				return "", nil, err
			}
			return strings.Join(parts[:i], "/"), d, nil
		}
	}
	return "", nil, fmt.Errorf("invalid write resource %q", name)
}

// ReadResourceName formats a ByteStream read resource name.
func ReadResourceName(instance string, d *repb.Digest) string {
	if instance == "" {
		return fmt.Sprintf("blobs/%s/%d", d.GetHash(), d.GetSizeBytes())
	}
	return fmt.Sprintf("%s/blobs/%s/%d", instance, d.GetHash(), d.GetSizeBytes())
}

// WriteResourceName formats a ByteStream write resource name with the given
// upload UUID.
func WriteResourceName(instance, uuid string, d *repb.Digest) string {
	if instance == "" {
		return fmt.Sprintf("uploads/%s/blobs/%s/%d", uuid, d.GetHash(), d.GetSizeBytes())
	}
	return fmt.Sprintf("%s/uploads/%s/blobs/%s/%d", instance, uuid, d.GetHash(), d.GetSizeBytes())
}

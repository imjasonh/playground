package remote

import (
	"fmt"
	"strconv"
	"strings"

	repb "github.com/bazelbuild/remote-apis/build/bazel/remote/execution/v2"
)

// MaxBatchBytes is the largest blob the batch CAS methods accept. Larger blobs
// must use the ByteStream API. It also decides how the runner routes an
// upload: small blobs go through BatchUpdateBlobs, large ones through
// ByteStream.Write.
const MaxBatchBytes = 4 * 1024 * 1024

// parseDigest splits a "hash/size" pair from a ByteStream resource name.
func parseDigest(hash, size string) (*repb.Digest, error) {
	n, err := strconv.ParseInt(size, 10, 64)
	if err != nil {
		return nil, fmt.Errorf("bad size %q: %w", size, err)
	}
	return &repb.Digest{Hash: hash, SizeBytes: n}, nil
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

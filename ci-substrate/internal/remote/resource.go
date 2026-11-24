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

// batchSendBytes and batchSendCount bound one BatchReadBlobs or
// BatchUpdateBlobs call the client makes. The payload stays under
// MaxBatchBytes, and the count stays small, because each blob adds a digest
// and a status to the response and gRPC's default receive limit is 4 MiB.
const batchSendBytes = 2 << 20

const batchSendCount = 256

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

// parseDigestParts parses "{digest_function/}{hash}/{size}" starting at parts.
func parseDigestParts(parts []string) (*repb.Digest, error) {
	if len(parts) < 2 {
		return nil, fmt.Errorf("incomplete digest path")
	}
	if strings.EqualFold(parts[0], "sha256") {
		if len(parts) < 3 {
			return nil, fmt.Errorf("incomplete sha256 digest path")
		}
		return parseDigest(parts[1], parts[2])
	}
	return parseDigest(parts[0], parts[1])
}

func parseCompressorName(name string) (repb.Compressor_Value, error) {
	switch strings.ToLower(name) {
	case "zstd":
		return repb.Compressor_ZSTD, nil
	case "deflate":
		return repb.Compressor_DEFLATE, nil
	default:
		return repb.Compressor_IDENTITY, fmt.Errorf("unsupported compressor %q", name)
	}
}

func compressorName(c repb.Compressor_Value) string {
	switch c {
	case repb.Compressor_ZSTD:
		return "zstd"
	case repb.Compressor_DEFLATE:
		return "deflate"
	default:
		return ""
	}
}

// ParseReadResource parses an uncompressed ByteStream read resource name of
// the form "{instance_name}/blobs/{hash}/{size}".
func ParseReadResource(name string) (instance string, d *repb.Digest, err error) {
	instance, d, comp, err := ParseReadResourceCompressed(name)
	if err != nil {
		return "", nil, err
	}
	if comp != repb.Compressor_IDENTITY {
		return "", nil, fmt.Errorf("unexpected compressed read resource %q", name)
	}
	return instance, d, nil
}

// ParseReadResourceCompressed parses a ByteStream read resource name in either
// uncompressed ("{instance}/blobs/{digest_fn/}{hash}/{size}") or compressed
// ("{instance}/compressed-blobs/{compressor}/{digest_fn/}{hash}/{size}") form.
func ParseReadResourceCompressed(name string) (instance string, d *repb.Digest, comp repb.Compressor_Value, err error) {
	parts := strings.Split(name, "/")
	for i := 0; i < len(parts); i++ {
		switch parts[i] {
		case "blobs":
			d, err := parseDigestParts(parts[i+1:])
			if err != nil {
				return "", nil, repb.Compressor_IDENTITY, err
			}
			return strings.Join(parts[:i], "/"), d, repb.Compressor_IDENTITY, nil
		case "compressed-blobs":
			if i+3 >= len(parts) {
				return "", nil, repb.Compressor_IDENTITY, fmt.Errorf("invalid compressed read resource %q", name)
			}
			c, err := parseCompressorName(parts[i+1])
			if err != nil {
				return "", nil, repb.Compressor_IDENTITY, err
			}
			d, err := parseDigestParts(parts[i+2:])
			if err != nil {
				return "", nil, repb.Compressor_IDENTITY, err
			}
			return strings.Join(parts[:i], "/"), d, c, nil
		}
	}
	return "", nil, repb.Compressor_IDENTITY, fmt.Errorf("invalid read resource %q", name)
}

// ParseWriteResource parses an uncompressed ByteStream write resource name of
// the form "{instance_name}/uploads/{uuid}/blobs/{hash}/{size}{/optional}".
func ParseWriteResource(name string) (instance string, d *repb.Digest, err error) {
	instance, d, comp, err := ParseWriteResourceCompressed(name)
	if err != nil {
		return "", nil, err
	}
	if comp != repb.Compressor_IDENTITY {
		return "", nil, fmt.Errorf("unexpected compressed write resource %q", name)
	}
	return instance, d, nil
}

// ParseWriteResourceCompressed parses a ByteStream write resource name in
// either uncompressed ("{instance}/uploads/{uuid}/blobs/{digest_fn/}{hash}/{size}{/opt}")
// or compressed ("{instance}/uploads/{uuid}/compressed-blobs/{compressor}/{digest_fn/}{hash}/{size}{/opt}")
// form.
func ParseWriteResourceCompressed(name string) (instance string, d *repb.Digest, comp repb.Compressor_Value, err error) {
	parts := strings.Split(name, "/")
	for i := 0; i+2 < len(parts); i++ {
		if parts[i] != "uploads" {
			continue
		}
		switch parts[i+2] {
		case "blobs":
			d, err := parseDigestParts(parts[i+3:])
			if err != nil {
				return "", nil, repb.Compressor_IDENTITY, err
			}
			return strings.Join(parts[:i], "/"), d, repb.Compressor_IDENTITY, nil
		case "compressed-blobs":
			if i+5 >= len(parts) {
				return "", nil, repb.Compressor_IDENTITY, fmt.Errorf("invalid compressed write resource %q", name)
			}
			c, err := parseCompressorName(parts[i+3])
			if err != nil {
				return "", nil, repb.Compressor_IDENTITY, err
			}
			d, err := parseDigestParts(parts[i+4:])
			if err != nil {
				return "", nil, repb.Compressor_IDENTITY, err
			}
			return strings.Join(parts[:i], "/"), d, c, nil
		}
	}
	return "", nil, repb.Compressor_IDENTITY, fmt.Errorf("invalid write resource %q", name)
}

// ReadResourceName formats a ByteStream read resource name.
func ReadResourceName(instance string, d *repb.Digest) string {
	if instance == "" {
		return fmt.Sprintf("blobs/%s/%d", d.GetHash(), d.GetSizeBytes())
	}
	return fmt.Sprintf("%s/blobs/%s/%d", instance, d.GetHash(), d.GetSizeBytes())
}

// CompressedReadResourceName formats a compressed ByteStream read resource name.
func CompressedReadResourceName(instance string, comp repb.Compressor_Value, d *repb.Digest) string {
	if comp == repb.Compressor_IDENTITY {
		return ReadResourceName(instance, d)
	}
	if instance == "" {
		return fmt.Sprintf("compressed-blobs/%s/%s/%d", compressorName(comp), d.GetHash(), d.GetSizeBytes())
	}
	return fmt.Sprintf("%s/compressed-blobs/%s/%s/%d", instance, compressorName(comp), d.GetHash(), d.GetSizeBytes())
}

// WriteResourceName formats a ByteStream write resource name with the given
// upload UUID.
func WriteResourceName(instance, uuid string, d *repb.Digest) string {
	if instance == "" {
		return fmt.Sprintf("uploads/%s/blobs/%s/%d", uuid, d.GetHash(), d.GetSizeBytes())
	}
	return fmt.Sprintf("%s/uploads/%s/blobs/%s/%d", instance, uuid, d.GetHash(), d.GetSizeBytes())
}

// CompressedWriteResourceName formats a compressed ByteStream write resource name.
func CompressedWriteResourceName(instance, uuid string, comp repb.Compressor_Value, d *repb.Digest) string {
	if comp == repb.Compressor_IDENTITY {
		return WriteResourceName(instance, uuid, d)
	}
	if instance == "" {
		return fmt.Sprintf("uploads/%s/compressed-blobs/%s/%s/%d", uuid, compressorName(comp), d.GetHash(), d.GetSizeBytes())
	}
	return fmt.Sprintf("%s/uploads/%s/compressed-blobs/%s/%s/%d", instance, uuid, compressorName(comp), d.GetHash(), d.GetSizeBytes())
}

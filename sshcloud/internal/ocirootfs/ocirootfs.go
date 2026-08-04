// Package ocirootfs materializes digest-pinned OCI images into ext4 rootfs images.
package ocirootfs

import (
	"context"
	"fmt"
	"os"
	"path/filepath"
	"strings"

	"github.com/google/go-containerregistry/pkg/name"
	v1 "github.com/google/go-containerregistry/pkg/v1"
	"github.com/google/go-containerregistry/pkg/v1/remote"

	"github.com/imjasonh/playground/sshcloud/internal/image"
	"github.com/imjasonh/playground/sshcloud/internal/rootfs"
)

const (
	defaultSizeMB               = 512
	defaultMaxUncompressedBytes = 1 << 30 // 1 GiB
)

// Options control Materialize.
type Options struct {
	// CacheDir is a digest-addressed ext4 cache. Empty uses os.TempDir.
	CacheDir string
	// SizeMB is the ext4 image size. Zero defaults to 512.
	SizeMB int
	// MaxUncompressedBytes caps unpacked layer bytes. Zero defaults to 1 GiB.
	MaxUncompressedBytes int64
}

// Materialize pulls ref (must be repo@sha256:64hex), unpacks layers with OCI
// whiteout handling, builds an ext4 filesystem image, caches it, and returns
// the ext4 path. The platform kernel is not taken from the image.
func Materialize(ctx context.Context, ref string, opt Options) (string, error) {
	if err := image.ValidateDigestPinned(ref); err != nil {
		return "", err
	}
	digest, err := name.NewDigest(strings.TrimSpace(ref))
	if err != nil {
		return "", fmt.Errorf("parse image ref: %w", err)
	}
	hex := strings.TrimPrefix(strings.ToLower(digest.DigestStr()), "sha256:")
	if len(hex) != 64 {
		return "", fmt.Errorf("image digest hex must be 64 characters")
	}

	if opt.CacheDir == "" {
		opt.CacheDir = filepath.Join(os.TempDir(), "sshcloud-ocirootfs")
	}
	if opt.SizeMB <= 0 {
		opt.SizeMB = defaultSizeMB
	}
	if opt.MaxUncompressedBytes <= 0 {
		opt.MaxUncompressedBytes = defaultMaxUncompressedBytes
	}
	if err := os.MkdirAll(opt.CacheDir, 0o755); err != nil {
		return "", err
	}

	cachePath := filepath.Join(opt.CacheDir, hex+".ext4")
	if st, err := os.Stat(cachePath); err == nil && st.Size() > 0 && st.Mode().IsRegular() {
		return cachePath, nil
	}

	img, err := remote.Image(digest, remote.WithContext(ctx), remote.WithPlatform(v1.Platform{
		Architecture: "amd64",
		OS:           "linux",
	}))
	if err != nil {
		return "", fmt.Errorf("pull %s: %w", ref, err)
	}

	unpackDir, err := os.MkdirTemp(opt.CacheDir, "unpack-"+hex[:12]+"-*")
	if err != nil {
		return "", err
	}
	defer os.RemoveAll(unpackDir)

	if err := Unpack(img, unpackDir, opt.MaxUncompressedBytes); err != nil {
		return "", err
	}

	tmpOut, err := os.CreateTemp(opt.CacheDir, hex+".ext4.tmp-*")
	if err != nil {
		return "", err
	}
	tmpPath := tmpOut.Name()
	_ = tmpOut.Close()
	defer os.Remove(tmpPath)

	if err := rootfs.BuildFromDir(unpackDir, tmpPath, opt.SizeMB); err != nil {
		return "", fmt.Errorf("build ext4: %w", err)
	}
	if err := os.Rename(tmpPath, cachePath); err != nil {
		return "", err
	}
	return cachePath, nil
}

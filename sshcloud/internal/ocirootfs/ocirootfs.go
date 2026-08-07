// Package ocirootfs materializes digest-pinned OCI images into ext4 rootfs images.
package ocirootfs

import (
	"context"
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
	"strings"
	"sync"

	"github.com/google/go-containerregistry/pkg/authn"
	"github.com/google/go-containerregistry/pkg/name"
	v1 "github.com/google/go-containerregistry/pkg/v1"
	gcrgoogle "github.com/google/go-containerregistry/pkg/v1/google"
	"github.com/google/go-containerregistry/pkg/v1/remote"

	"github.com/imjasonh/playground/sshcloud/internal/guestinit"
	"github.com/imjasonh/playground/sshcloud/internal/image"
	"github.com/imjasonh/playground/sshcloud/internal/rootfs"
)

var materializeLocks sync.Map

const (
	defaultSizeMB               = 512
	defaultMaxUncompressedBytes = 1 << 30 // 1 GiB
	materializerSchema          = 2
)

// Options control Materialize.
type Options struct {
	// CacheDir is a digest-addressed ext4 cache. Empty uses os.TempDir.
	CacheDir string
	// MaxCacheBytes is the hard ext4-cache budget. Zero defaults to 8 GiB;
	// least-recently-used digest pairs are removed before a new build.
	MaxCacheBytes int64
	// SizeMB is the ext4 image size. Zero defaults to 512.
	SizeMB int
	// MaxUncompressedBytes caps unpacked layer bytes. Zero defaults to 1 GiB.
	MaxUncompressedBytes int64
}

// Result is a cached ext4 rootfs plus the image's PID 1 spec.
type Result struct {
	Rootfs string
	Spec   guestinit.Spec
	// Release ends the cache-entry lease after the caller has cloned Rootfs.
	// Callers must invoke it; otherwise eviction remains conservatively blocked.
	Release func()
}

// Materialize pulls ref (must be repo@sha256:64hex), unpacks layers with OCI
// whiteout handling, builds an ext4 filesystem image, caches it, and returns
// the ext4 path plus Entrypoint/Cmd/Env/WorkingDir. The platform kernel is
// not taken from the image.
func Materialize(ctx context.Context, ref string, opt Options) (Result, error) {
	if err := image.ValidateDigestPinned(ref); err != nil {
		return Result{}, err
	}
	digest, err := name.NewDigest(strings.TrimSpace(ref))
	if err != nil {
		return Result{}, fmt.Errorf("parse image ref: %w", err)
	}
	hex := strings.TrimPrefix(strings.ToLower(digest.DigestStr()), "sha256:")
	if len(hex) != 64 {
		return Result{}, fmt.Errorf("image digest hex must be 64 characters")
	}

	if opt.CacheDir == "" {
		opt.CacheDir = filepath.Join(os.TempDir(), "sshcloud-ocirootfs")
	}
	if opt.SizeMB <= 0 {
		opt.SizeMB = defaultSizeMB
	}
	if opt.MaxCacheBytes <= 0 {
		opt.MaxCacheBytes = DefaultCacheBytes
	}
	if opt.MaxUncompressedBytes <= 0 {
		opt.MaxUncompressedBytes = defaultMaxUncompressedBytes
	}
	if err := os.MkdirAll(opt.CacheDir, 0o755); err != nil {
		return Result{}, err
	}

	cacheBase := fmt.Sprintf("%s-v%d-%dm", hex, materializerSchema, opt.SizeMB)
	cachePath := filepath.Join(opt.CacheDir, cacheBase+".ext4")
	specPath := filepath.Join(opt.CacheDir, cacheBase+".boot.json")
	markCacheEntryActive(cacheBase)
	releaseOnReturn := true
	defer func() {
		if releaseOnReturn {
			unmarkCacheEntryActive(cacheBase)
		}
	}()
	leasedResult := func(spec guestinit.Spec) Result {
		releaseOnReturn = false
		var once sync.Once
		return Result{
			Rootfs: cachePath,
			Spec:   spec,
			Release: func() {
				once.Do(func() { unmarkCacheEntryActive(cacheBase) })
			},
		}
	}
	lockValue, _ := materializeLocks.LoadOrStore(cachePath, &sync.Mutex{})
	lock := lockValue.(*sync.Mutex)
	lock.Lock()
	defer lock.Unlock()
	if st, err := os.Stat(cachePath); err == nil && st.Size() > 0 && st.Mode().IsRegular() {
		spec, err := loadOrFetchSpec(ctx, digest, specPath)
		if err != nil {
			return Result{}, err
		}
		if err := enforceRootfsCacheLimit(opt.CacheDir, opt.MaxCacheBytes, cacheBase); err != nil {
			return Result{}, err
		}
		touchCacheEntry(cachePath, specPath)
		return leasedResult(spec), nil
	}
	maxSizeMB := (opt.MaxCacheBytes - maxBootSpecBytes) >> 20
	if maxSizeMB <= 0 || int64(opt.SizeMB) > maxSizeMB {
		return Result{}, fmt.Errorf(
			"configured %d MiB rootfs cannot fit within %d-byte cache limit",
			opt.SizeMB, opt.MaxCacheBytes,
		)
	}
	expectedCacheBytes := int64(opt.SizeMB)<<20 + maxBootSpecBytes
	if err := reserveRootfsCacheSpace(opt.CacheDir, opt.MaxCacheBytes, expectedCacheBytes, cacheBase); err != nil {
		return Result{}, err
	}
	reservationHeld := true
	defer func() {
		if reservationHeld {
			releaseRootfsCacheSpace(cacheBase)
		}
	}()

	img, err := pullLinuxAmd64(ctx, digest)
	if err != nil {
		return Result{}, err
	}
	spec, err := specFromImage(img)
	if err != nil {
		return Result{}, err
	}

	unpackDir, err := os.MkdirTemp(opt.CacheDir, "unpack-"+hex[:12]+"-*")
	if err != nil {
		return Result{}, err
	}
	defer os.RemoveAll(unpackDir)

	if err := Unpack(img, unpackDir, opt.MaxUncompressedBytes); err != nil {
		return Result{}, err
	}
	usage, err := directoryBytes(unpackDir)
	if err != nil {
		return Result{}, err
	}
	// Reserve 25% plus 32 MiB for ext4 metadata and runtime writes.
	requiredBytes := usage + usage/4 + int64(32<<20)
	if requiredBytes > int64(opt.SizeMB)<<20 {
		return Result{}, fmt.Errorf("image requires at least %d MiB rootfs with runtime headroom; configured %d MiB",
			(requiredBytes+(1<<20)-1)>>20, opt.SizeMB)
	}

	tmpOut, err := os.CreateTemp(opt.CacheDir, hex+".ext4.tmp-*")
	if err != nil {
		return Result{}, err
	}
	tmpPath := tmpOut.Name()
	_ = tmpOut.Close()
	defer os.Remove(tmpPath)

	if err := rootfs.BuildFromDir(unpackDir, tmpPath, opt.SizeMB); err != nil {
		return Result{}, fmt.Errorf("build ext4: %w", err)
	}
	if err := os.Rename(tmpPath, cachePath); err != nil {
		return Result{}, err
	}
	if err := guestinit.WriteFile(specPath, spec); err != nil {
		return Result{}, err
	}
	releaseRootfsCacheSpace(cacheBase)
	reservationHeld = false
	touchCacheEntry(cachePath, specPath)
	if err := enforceRootfsCacheLimit(opt.CacheDir, opt.MaxCacheBytes, cacheBase); err != nil {
		return Result{}, err
	}
	return leasedResult(spec), nil
}

func directoryBytes(root string) (int64, error) {
	var total int64
	err := filepath.WalkDir(root, func(path string, entry os.DirEntry, err error) error {
		if err != nil {
			return err
		}
		if entry.Type().IsRegular() {
			info, err := entry.Info()
			if err != nil {
				return err
			}
			total += info.Size()
		}
		return nil
	})
	return total, err
}

func loadOrFetchSpec(ctx context.Context, digest name.Digest, specPath string) (guestinit.Spec, error) {
	if st, err := os.Stat(specPath); err == nil && st.Size() > 0 {
		if st.Size() > maxBootSpecBytes {
			return guestinit.Spec{}, fmt.Errorf("cached boot spec exceeds %d-byte limit", maxBootSpecBytes)
		}
		return guestinit.LoadFile(specPath)
	}
	img, err := pullLinuxAmd64(ctx, digest)
	if err != nil {
		return guestinit.Spec{}, err
	}
	spec, err := specFromImage(img)
	if err != nil {
		return guestinit.Spec{}, err
	}
	if err := guestinit.WriteFile(specPath, spec); err != nil {
		return guestinit.Spec{}, err
	}
	return spec, nil
}

func pullLinuxAmd64(ctx context.Context, digest name.Digest) (v1.Image, error) {
	img, err := remote.Image(
		digest,
		remote.WithContext(ctx),
		remote.WithAuthFromKeychain(authn.NewMultiKeychain(gcrgoogle.Keychain, authn.DefaultKeychain)),
		remote.WithPlatform(v1.Platform{
			Architecture: "amd64",
			OS:           "linux",
		}),
	)
	if err != nil {
		return nil, fmt.Errorf("pull %s: %w", digest.String(), err)
	}
	return img, nil
}

func specFromImage(img v1.Image) (guestinit.Spec, error) {
	cfg, err := img.ConfigFile()
	if err != nil {
		return guestinit.Spec{}, fmt.Errorf("image config: %w", err)
	}
	if cfg == nil {
		return guestinit.Spec{}, fmt.Errorf("image config is empty")
	}
	if cfg.OS != "" && cfg.OS != "linux" {
		return guestinit.Spec{}, fmt.Errorf("image OS %q is not supported (want linux)", cfg.OS)
	}
	if cfg.Architecture != "" && cfg.Architecture != "amd64" {
		return guestinit.Spec{}, fmt.Errorf("image architecture %q is not supported (want amd64)", cfg.Architecture)
	}
	switch strings.TrimSpace(cfg.Config.User) {
	case "", "0", "0:0", "root", "root:root":
	default:
		return guestinit.Spec{}, fmt.Errorf("image User %q is not supported; SSH apps currently run as guest root", cfg.Config.User)
	}
	if len(cfg.Config.Volumes) != 0 {
		return guestinit.Spec{}, fmt.Errorf("OCI declared volumes are not supported")
	}
	spec := guestinit.Spec{
		Entrypoint: append([]string{}, cfg.Config.Entrypoint...),
		Cmd:        append([]string{}, cfg.Config.Cmd...),
		Env:        append([]string{}, cfg.Config.Env...),
		WorkingDir: cfg.Config.WorkingDir,
	}
	if err := spec.Validate(); err != nil {
		return guestinit.Spec{}, err
	}
	encoded, err := json.Marshal(spec)
	if err != nil {
		return guestinit.Spec{}, err
	}
	if len(encoded)+1 > maxBootSpecBytes {
		return guestinit.Spec{}, fmt.Errorf("OCI boot spec exceeds %d-byte limit", maxBootSpecBytes)
	}
	return spec, nil
}

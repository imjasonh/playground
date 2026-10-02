// Package image builds container images that add one static executable to
// a base image, and pushes them, with go-containerregistry.
package image

import (
	"archive/tar"
	"bytes"
	"context"
	"fmt"
	"io"
	"os"
	pathpkg "path"
	"slices"
	"strings"
	"time"

	"github.com/google/go-containerregistry/pkg/authn"
	"github.com/google/go-containerregistry/pkg/name"
	v1 "github.com/google/go-containerregistry/pkg/v1"
	"github.com/google/go-containerregistry/pkg/v1/empty"
	"github.com/google/go-containerregistry/pkg/v1/mutate"
	"github.com/google/go-containerregistry/pkg/v1/remote"
	"github.com/google/go-containerregistry/pkg/v1/tarball"
	"github.com/google/go-containerregistry/pkg/v1/types"
)

// An Executable is a file built for one platform.
type Executable struct {
	Platform v1.Platform
	File     string
}

// An Image is a static executable on a base image.
type Image struct {
	// Base is the reference of the base image, such as
	// "cgr.dev/chainguard/static:latest". It must have an image for the
	// platform of every executable.
	Base string
	// Repository is where to push the image, such as "ghcr.io/you/app".
	Repository string
	// Tag, if set, also names the image in Repository.
	Tag string
	// Path is where the executable goes, such as "/app/website". It
	// becomes the image's entrypoint.
	Path        string
	Executables []Executable
}

// epoch is the time recorded in images, fixed so that the same inputs give
// the same digest.
var epoch = v1.Time{Time: time.Unix(0, 0).UTC()}

// Push builds im, pushes it to im.Repository with credentials from docker
// login or podman login, and returns its reference by digest. The
// reference names an index with one image per platform.
func Push(ctx context.Context, im Image) (string, error) {
	opts := []remote.Option{remote.WithContext(ctx), remote.WithAuthFromKeychain(authn.DefaultKeychain), remote.WithUserAgent("kube-generate")}
	if !strings.HasPrefix(im.Path, "/") {
		return "", fmt.Errorf("image: path %q must be absolute", im.Path)
	}
	base, err := name.ParseReference(im.Base)
	if err != nil {
		return "", fmt.Errorf("image: %w", err)
	}
	repo, err := name.NewRepository(im.Repository)
	if err != nil {
		return "", fmt.Errorf("image: %w", err)
	}
	desc, err := remote.Get(base, opts...)
	if err != nil {
		return "", fmt.Errorf("image: reading %s: %w", base, err)
	}
	// pick returns the base's image for a platform and its full platform.
	var pick func(v1.Platform) (v1.Image, *v1.Platform, error)
	if desc.MediaType.IsIndex() {
		idx, err := desc.ImageIndex()
		if err != nil {
			return "", err
		}
		man, err := idx.IndexManifest()
		if err != nil {
			return "", err
		}
		pick = func(p v1.Platform) (v1.Image, *v1.Platform, error) {
			for _, d := range man.Manifests {
				if d.Platform != nil && d.Platform.Satisfies(p) {
					img, err := idx.Image(d.Digest)
					return img, d.Platform, err
				}
			}
			return nil, nil, fmt.Errorf("image: %s has no image for %s", base, p)
		}
	} else {
		img, err := desc.Image()
		if err != nil {
			return "", err
		}
		cf, err := img.ConfigFile()
		if err != nil {
			return "", err
		}
		if len(im.Executables) != 1 {
			return "", fmt.Errorf("image: %s has one platform, so it can't be the base of an image for %d", base, len(im.Executables))
		}
		pick = func(p v1.Platform) (v1.Image, *v1.Platform, error) {
			if bp := cf.Platform(); bp != nil && bp.Satisfies(p) {
				return img, bp, nil
			}
			return nil, nil, fmt.Errorf("image: %s isn't for %s", base, p)
		}
	}

	out := mutate.IndexMediaType(empty.Index, types.OCIImageIndex)
	exes := slices.SortedFunc(slices.Values(im.Executables), func(a, b Executable) int {
		return strings.Compare(a.Platform.String(), b.Platform.String())
	})
	for _, exe := range exes {
		b, p, err := pick(exe.Platform)
		if err != nil {
			return "", err
		}
		img, err := addExecutable(b, im.Path, exe.File, base.String(), desc.Digest.String())
		if err != nil {
			return "", fmt.Errorf("image: building for %s: %w", exe.Platform, err)
		}
		if mt, _ := img.MediaType(); mt == types.DockerManifestSchema2 {
			out = mutate.IndexMediaType(out, types.DockerManifestList)
		}
		out = mutate.AppendManifests(out, mutate.IndexAddendum{Add: img, Descriptor: v1.Descriptor{Platform: p}})
	}
	digest, err := out.Digest()
	if err != nil {
		return "", err
	}
	byDigest := repo.Digest(digest.String())
	var ref name.Reference = byDigest
	if im.Tag != "" {
		ref = repo.Tag(im.Tag)
	}
	if err := remote.WriteIndex(ref, out, opts...); err != nil {
		return "", fmt.Errorf("image: pushing %s: %w", ref, err)
	}
	return byDigest.String(), nil
}

// addExecutable adds a layer that holds file at path to base, and makes it
// the entrypoint.
func addExecutable(base v1.Image, path, file, baseName, baseDigest string) (v1.Image, error) {
	mt, err := base.MediaType()
	if err != nil {
		return nil, err
	}
	layerType := types.DockerLayer
	if mt == types.OCIManifestSchema1 {
		layerType = types.OCILayer
	}
	contents, err := tarOf(path, file)
	if err != nil {
		return nil, err
	}
	layer, err := layerFrom(contents, layerType)
	if err != nil {
		return nil, err
	}
	img, err := mutate.Append(base, mutate.Addendum{
		Layer:     layer,
		MediaType: layerType,
		History:   v1.History{Created: epoch, CreatedBy: "kube generate", Comment: path},
	})
	if err != nil {
		return nil, err
	}
	cf, err := img.ConfigFile()
	if err != nil {
		return nil, err
	}
	cf = cf.DeepCopy()
	cf.Config.Entrypoint = []string{path}
	cf.Config.Cmd = nil
	if cf.Config.User == "" {
		// Chainguard's nonroot user, so pods can require a non-root user
		// on any base.
		cf.Config.User = "65532"
	}
	if img, err = mutate.ConfigFile(img, cf); err != nil {
		return nil, err
	}
	if img, err = mutate.CreatedAt(img, epoch); err != nil {
		return nil, err
	}
	if mt == types.OCIManifestSchema1 {
		img = mutate.Annotations(img, map[string]string{
			"org.opencontainers.image.base.name":   baseName,
			"org.opencontainers.image.base.digest": baseDigest,
		}).(v1.Image)
	}
	return img, nil
}

func layerFrom(b []byte, mt types.MediaType) (v1.Layer, error) {
	return tarball.LayerFromOpener(func() (io.ReadCloser, error) {
		return io.NopCloser(bytes.NewReader(b)), nil
	}, tarball.WithMediaType(mt))
}

// tarOf returns a tar that holds file at path, executable by any user, with
// fixed owners and times.
func tarOf(path, file string) ([]byte, error) {
	f, err := os.Open(file) // #nosec G304 -- an executable the program just built.
	if err != nil {
		return nil, err
	}
	defer f.Close()
	fi, err := f.Stat()
	if err != nil {
		return nil, err
	}
	var buf bytes.Buffer
	tw := tar.NewWriter(&buf)
	name := strings.TrimPrefix(path, "/")
	var dirs []string
	for d := pathpkg.Dir(name); d != "."; d = pathpkg.Dir(d) {
		dirs = append(dirs, d)
	}
	slices.Reverse(dirs)
	for _, d := range dirs {
		if err := tw.WriteHeader(&tar.Header{Typeflag: tar.TypeDir, Name: d + "/", Mode: 0o755, ModTime: epoch.Time}); err != nil {
			return nil, err
		}
	}
	if err := tw.WriteHeader(&tar.Header{Typeflag: tar.TypeReg, Name: name, Mode: 0o755, Size: fi.Size(), ModTime: epoch.Time}); err != nil {
		return nil, err
	}
	if _, err := io.Copy(tw, f); err != nil {
		return nil, err
	}
	if err := tw.Close(); err != nil {
		return nil, err
	}
	return buf.Bytes(), nil
}

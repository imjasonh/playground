package publish

import (
	"bytes"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"strings"

	"github.com/google/go-containerregistry/pkg/authn"
	"github.com/google/go-containerregistry/pkg/name"
	v1 "github.com/google/go-containerregistry/pkg/v1"
	"github.com/google/go-containerregistry/pkg/v1/empty"
	"github.com/google/go-containerregistry/pkg/v1/mutate"
	"github.com/google/go-containerregistry/pkg/v1/remote"
	"github.com/google/go-containerregistry/pkg/v1/tarball"
	"github.com/google/go-containerregistry/pkg/v1/types"
	"github.com/imjasonh/playground/node-image/internal/layer"
)

// PlatformImage pairs an image with its platform for index assembly.
type PlatformImage struct {
	Platform v1.Platform
	Image    v1.Image
}

// Options controls image assembly.
type Options struct {
	Base       string
	Workdir    string
	User       string
	Entrypoint []string
	Cmd        []string
	Platform   v1.Platform
}

// LayerFiles is one OCI layer's files.
type LayerFiles struct {
	Files []layer.File
}

// BuildImage appends layers onto base and returns the image.
func BuildImage(opts Options, layers []LayerFiles) (v1.Image, error) {
	baseRef, err := name.ParseReference(opts.Base, name.WeakValidation)
	if err != nil {
		return nil, err
	}
	base, err := remote.Image(baseRef, remote.WithAuthFromKeychain(authn.DefaultKeychain), remote.WithPlatform(opts.Platform))
	if err != nil {
		return nil, fmt.Errorf("pull base %s: %w", opts.Base, err)
	}
	return appendAndConfigure(base, opts, layers)
}

// EmptyImage builds from scratch (tests / offline).
func EmptyImage(opts Options, layers []LayerFiles) (v1.Image, error) {
	return appendAndConfigure(empty.Image, opts, layers)
}

func appendAndConfigure(base v1.Image, opts Options, layers []LayerFiles) (v1.Image, error) {
	var add []mutate.Addendum
	for _, lf := range layers {
		l, err := layerFromFiles(lf.Files)
		if err != nil {
			return nil, err
		}
		add = append(add, mutate.Addendum{Layer: l, MediaType: types.OCILayer})
	}
	img, err := mutate.Append(base, add...)
	if err != nil {
		return nil, err
	}
	cfg, err := img.ConfigFile()
	if err != nil {
		return nil, err
	}
	cfg = cfg.DeepCopy()
	if opts.Workdir != "" {
		cfg.Config.WorkingDir = opts.Workdir
	}
	if opts.User != "" {
		cfg.Config.User = opts.User
	}
	if len(opts.Entrypoint) > 0 {
		cfg.Config.Entrypoint = opts.Entrypoint
	}
	if len(opts.Cmd) > 0 {
		cfg.Config.Cmd = opts.Cmd
	}
	if opts.Platform.OS != "" {
		cfg.OS = opts.Platform.OS
	}
	if opts.Platform.Architecture != "" {
		cfg.Architecture = opts.Platform.Architecture
	}
	return mutate.ConfigFile(img, cfg)
}

func layerFromFiles(files []layer.File) (v1.Layer, error) {
	_, _, compressed, err := layer.CompressedDigest(files)
	if err != nil {
		return nil, err
	}
	return tarball.LayerFromOpener(func() (io.ReadCloser, error) {
		return io.NopCloser(bytes.NewReader(compressed)), nil
	})
}

// WriteDigestSummary writes digest + layer digests for offline tests.
func WriteDigestSummary(dir string, img v1.Image) (string, error) {
	if err := os.MkdirAll(dir, 0o755); err != nil {
		return "", err
	}
	d, err := img.Digest()
	if err != nil {
		return "", err
	}
	if err := os.WriteFile(filepath.Join(dir, "digest"), []byte(d.String()), 0o644); err != nil {
		return "", err
	}
	layers, err := img.Layers()
	if err != nil {
		return "", err
	}
	var b strings.Builder
	for _, l := range layers {
		ld, err := l.Digest()
		if err != nil {
			return "", err
		}
		b.WriteString(ld.String())
		b.WriteByte('\n')
	}
	if err := os.WriteFile(filepath.Join(dir, "layers"), []byte(b.String()), 0o644); err != nil {
		return "", err
	}
	return d.String(), nil
}

// MakeIndex builds an OCI image index from per-platform images.
func MakeIndex(images []PlatformImage) (v1.ImageIndex, error) {
	if len(images) == 0 {
		return nil, fmt.Errorf("no images for index")
	}
	idx := mutate.AppendManifests(empty.Index, platformAdds(images)...)
	return idx, nil
}

func platformAdds(images []PlatformImage) []mutate.IndexAddendum {
	adds := make([]mutate.IndexAddendum, 0, len(images))
	for _, pi := range images {
		p := pi.Platform
		adds = append(adds, mutate.IndexAddendum{
			Add: pi.Image,
			Descriptor: v1.Descriptor{
				Platform: &p,
			},
		})
	}
	return adds
}

// WriteIndexSummary writes the index digest and per-platform image digests.
func WriteIndexSummary(dir string, idx v1.ImageIndex) (string, error) {
	if err := os.MkdirAll(dir, 0o755); err != nil {
		return "", err
	}
	d, err := idx.Digest()
	if err != nil {
		return "", err
	}
	if err := os.WriteFile(filepath.Join(dir, "digest"), []byte(d.String()), 0o644); err != nil {
		return "", err
	}
	mf, err := idx.IndexManifest()
	if err != nil {
		return "", err
	}
	var b strings.Builder
	for _, m := range mf.Manifests {
		plat := "unknown"
		if m.Platform != nil {
			plat = m.Platform.OS + "/" + m.Platform.Architecture
		}
		b.WriteString(plat)
		b.WriteByte('\t')
		b.WriteString(m.Digest.String())
		b.WriteByte('\n')
	}
	if err := os.WriteFile(filepath.Join(dir, "platforms"), []byte(b.String()), 0o644); err != nil {
		return "", err
	}
	return d.String(), nil
}

// Push pushes img to repo with tags; returns repo@sha256:…
func Push(repo string, tags []string, img v1.Image) (string, error) {
	ref, err := name.ParseReference(repo, name.WeakValidation)
	if err != nil {
		return "", err
	}
	repoName := ref.Context()
	tag := "latest"
	if len(tags) > 0 {
		tag = tags[0]
	}
	dst := repoName.Tag(tag)
	if err := remote.Write(dst, img, remote.WithAuthFromKeychain(authn.DefaultKeychain)); err != nil {
		return "", err
	}
	d, err := img.Digest()
	if err != nil {
		return "", err
	}
	for _, t := range tags[1:] {
		if err := remote.Tag(repoName.Tag(t), img, remote.WithAuthFromKeychain(authn.DefaultKeychain)); err != nil {
			return "", err
		}
	}
	return fmt.Sprintf("%s@%s", repoName.Name(), d.String()), nil
}

// PushIndex pushes an image index with tags; returns repo@sha256:…
func PushIndex(repo string, tags []string, idx v1.ImageIndex) (string, error) {
	ref, err := name.ParseReference(repo, name.WeakValidation)
	if err != nil {
		return "", err
	}
	repoName := ref.Context()
	tag := "latest"
	if len(tags) > 0 {
		tag = tags[0]
	}
	dst := repoName.Tag(tag)
	if err := remote.WriteIndex(dst, idx, remote.WithAuthFromKeychain(authn.DefaultKeychain)); err != nil {
		return "", err
	}
	d, err := idx.Digest()
	if err != nil {
		return "", err
	}
	for _, t := range tags[1:] {
		if err := remote.Tag(repoName.Tag(t), idx, remote.WithAuthFromKeychain(authn.DefaultKeychain)); err != nil {
			return "", err
		}
	}
	return fmt.Sprintf("%s@%s", repoName.Name(), d.String()), nil
}

// ParsePlatform converts "linux/amd64" into v1.Platform.
func ParsePlatform(s string) (v1.Platform, error) {
	parts := strings.Split(s, "/")
	if len(parts) != 2 {
		return v1.Platform{}, fmt.Errorf("bad platform %q", s)
	}
	arch := parts[1]
	switch arch {
	case "x64":
		arch = "amd64"
	}
	return v1.Platform{OS: parts[0], Architecture: arch}, nil
}

// ResolveCPU maps GOARCH/OCI arch to pnpm cpu field.
func ResolveCPU(arch string) string {
	switch arch {
	case "amd64", "x86_64":
		return "x64"
	default:
		return arch
	}
}

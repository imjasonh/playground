package publish

import (
	"fmt"
	"io"
	"net"
	"os"
	"path/filepath"
	"strings"

	"github.com/google/go-containerregistry/pkg/authn"
	"github.com/google/go-containerregistry/pkg/name"
	v1 "github.com/google/go-containerregistry/pkg/v1"
	"github.com/google/go-containerregistry/pkg/v1/daemon"
	"github.com/google/go-containerregistry/pkg/v1/empty"
	"github.com/google/go-containerregistry/pkg/v1/mutate"
	"github.com/google/go-containerregistry/pkg/v1/remote"
	"github.com/google/go-containerregistry/pkg/v1/tarball"
	"github.com/google/go-containerregistry/pkg/v1/types"
	"github.com/imjasonh/playground/node-image/internal/layer"
)

// LocalRegistry is the registry host used when loading into a local Docker daemon.
const LocalRegistry = "node-image.local"

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
	Env        []string // KEY=VAL entries merged into image config
	Platform   v1.Platform
	// BlobCache, when set, tees each compressed layer blob to a local cache
	// keyed by DiffID so Digest()/upload reopeners skip recompression.
	BlobCache *layer.BlobCache
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
	add := make([]mutate.Addendum, len(layers))
	type result struct {
		i int
		l v1.Layer
		e error
	}
	ch := make(chan result, len(layers))
	for i, lf := range layers {
		i, lf := i, lf
		go func() {
			l, err := layerFromFiles(lf.Files, opts.BlobCache)
			ch <- result{i: i, l: l, e: err}
		}()
	}
	for range layers {
		r := <-ch
		if r.e != nil {
			return nil, r.e
		}
		add[r.i] = mutate.Addendum{Layer: r.l, MediaType: types.OCILayer}
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
	if len(opts.Env) > 0 {
		cfg.Config.Env = mergeEnv(cfg.Config.Env, opts.Env)
	}
	if opts.Platform.OS != "" {
		cfg.OS = opts.Platform.OS
	}
	if opts.Platform.Architecture != "" {
		cfg.Architecture = opts.Platform.Architecture
	}
	return mutate.ConfigFile(img, cfg)
}

// mergeEnv overlays overrides onto base (same KEY wins from overrides).
func mergeEnv(base, overrides []string) []string {
	m := map[string]string{}
	order := make([]string, 0, len(base)+len(overrides))
	for _, e := range base {
		k, _, ok := strings.Cut(e, "=")
		if !ok {
			continue
		}
		if _, exists := m[k]; !exists {
			order = append(order, k)
		}
		m[k] = e[len(k)+1:]
	}
	for _, e := range overrides {
		k, _, ok := strings.Cut(e, "=")
		if !ok {
			continue
		}
		if _, exists := m[k]; !exists {
			order = append(order, k)
		}
		m[k] = e[len(k)+1:]
	}
	out := make([]string, 0, len(order))
	for _, k := range order {
		out = append(out, k+"="+m[k])
	}
	return out
}

// layerFromFiles returns a layer that streams deterministic tar+gzip.
// When cache is non-nil, warm hits return a CachedBlob-backed layer that
// exposes known DiffID/Digest without gunzip/rehash (the big warm-path win).
func layerFromFiles(files []layer.File, cache *layer.BlobCache) (v1.Layer, error) {
	files = append([]layer.File(nil), files...)
	if cache != nil {
		blob, err := cache.Ensure(files)
		if err != nil {
			return nil, err
		}
		return layer.LayerFromCachedBlob(blob)
	}
	opener := func() (io.ReadCloser, error) {
		pr, pw := io.Pipe()
		go func() {
			pw.CloseWithError(layer.WriteCompressed(pw, files))
		}()
		return pr, nil
	}
	return tarball.LayerFromOpener(opener, tarball.WithMediaType(types.OCILayer))
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

// Push pushes img to repo with tags; returns the fully resolved repo@sha256:… ref.
// That string is the only thing `node-image build` prints on stdout so
// `docker run --rm $(node-image build …)` works.
func Push(repo string, tags []string, img v1.Image) (string, error) {
	repoName, err := parseRepository(repo)
	if err != nil {
		return "", err
	}
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

// PushIndex pushes an image index with tags; returns the fully resolved repo@sha256:… ref.
func PushIndex(repo string, tags []string, idx v1.ImageIndex) (string, error) {
	repoName, err := parseRepository(repo)
	if err != nil {
		return "", err
	}
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

// LoadLocal writes img into the local Docker daemon and returns a runnable
// tag reference (node-image.local/…:tag). Docker does not populate RepoDigests
// for daemon-loaded images, so a digest ref would trigger a failed registry pull.
func LoadLocal(repo string, tags []string, img v1.Image) (string, error) {
	localRepo, err := localRepository(repo)
	if err != nil {
		return "", err
	}
	tag := "latest"
	if len(tags) > 0 {
		tag = tags[0]
	}
	dst := localRepo.Tag(tag)
	if _, err := daemon.Write(dst, img); err != nil {
		return "", fmt.Errorf("load into docker daemon: %w\nHint: is the Docker daemon running? Try `docker info`", err)
	}
	for _, t := range tags[1:] {
		if err := daemon.Tag(dst, localRepo.Tag(t)); err != nil {
			return "", fmt.Errorf("tag %s: %w", t, err)
		}
	}
	return dst.Name(), nil
}

func parseRepository(repo string) (name.Repository, error) {
	opts := []name.Option{name.WeakValidation}
	if insecureHost(repo) {
		opts = append(opts, name.Insecure)
	}
	ref, err := name.ParseReference(repo, opts...)
	if err != nil {
		return name.Repository{}, err
	}
	return ref.Context(), nil
}

// LocalRepoName returns the daemon repository name for --local loads.
func LocalRepoName(repo string) (string, error) {
	r, err := localRepository(repo)
	if err != nil {
		return "", err
	}
	return r.Name(), nil
}

func localRepository(repo string) (name.Repository, error) {
	path := strings.TrimSpace(repo)
	if path == "" {
		path = "app"
	}
	// Strip a registry host if present so we always land under node-image.local.
	if strings.Contains(path, "/") {
		first, rest, ok := strings.Cut(path, "/")
		if ok && (strings.Contains(first, ".") || strings.Contains(first, ":") || first == "localhost") {
			path = rest
		}
	}
	path = strings.Trim(path, "/")
	if path == "" {
		path = "app"
	}
	full := LocalRegistry + "/" + path
	return name.NewRepository(full, name.WeakValidation)
}

func insecureHost(repo string) bool {
	host := repo
	if i := strings.Index(repo, "/"); i >= 0 {
		host = repo[:i]
	}
	h := host
	if hh, _, err := net.SplitHostPort(host); err == nil {
		h = hh
	}
	switch h {
	case "localhost", "127.0.0.1", "::1":
		return true
	}
	return strings.HasSuffix(h, ".local")
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

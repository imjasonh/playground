// Package registry is a small, cache-backed client for reading public OCI
// registries (Docker Hub by default) via go-containerregistry.
//
// Everything it fetches is written to a local on-disk cache so that repeated
// queries -- and the many overlapping lookups a single SQL query can trigger --
// do not needlessly hit registry rate limits. Content addressed by digest
// (manifests and config blobs) is cached forever; mutable lookups (tag lists
// and tag->digest resolution) are cached with a TTL.
package registry

import (
	"bytes"
	"context"
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"strings"
	"sync"
	"time"

	"github.com/google/go-containerregistry/pkg/authn"
	"github.com/google/go-containerregistry/pkg/name"
	v1 "github.com/google/go-containerregistry/pkg/v1"
	"github.com/google/go-containerregistry/pkg/v1/remote"
	"github.com/google/go-containerregistry/pkg/v1/types"
)

// DefaultTTL is how long mutable lookups (tag lists, tag->digest) stay fresh.
const DefaultTTL = 6 * time.Hour

// DefaultPlatform is used when a query does not constrain the platform.
const DefaultPlatform = "linux/amd64"

// Manifest is a raw manifest (image manifest or image index) plus its
// descriptor metadata.
type Manifest struct {
	Ref       string
	Digest    string
	MediaType string
	Size      int64
	Raw       []byte
}

// Backend performs the actual registry I/O behind the cache. The default
// implementation talks to a real registry via go-containerregistry; tests (and
// any caller wanting a different transport) can supply their own via
// Options.Backend.
type Backend interface {
	// ListTags returns the tags of a repository (e.g. "index.docker.io/library/nginx").
	ListTags(repo string) ([]string, error)
	// GetManifest resolves a reference and returns its raw manifest + descriptor.
	GetManifest(ref string) (Manifest, error)
	// GetBlob fetches a blob (e.g. a config blob) by digest from a repository.
	GetBlob(repo, digest string) ([]byte, error)
}

// Client reads a registry through a local on-disk cache.
type Client struct {
	dir string
	ttl time.Duration
	be  Backend

	mu     sync.Mutex
	hits   int
	misses int
}

// Options configures a Client.
type Options struct {
	// Dir is the cache directory. Required.
	Dir string
	// TTL bounds how long mutable lookups are reused. Zero uses DefaultTTL;
	// a negative value disables expiry (cache never considered stale).
	TTL time.Duration
	// Context is passed to all registry requests.
	Context context.Context
	// UserAgent is sent on registry requests.
	UserAgent string
	// Keychain authenticates requests. Nil uses the default keychain, which
	// honours `docker login` credentials and otherwise falls back to
	// anonymous access (subject to stricter rate limits).
	Keychain authn.Keychain
	// Backend overrides the registry I/O implementation. Nil uses a
	// go-containerregistry-backed default.
	Backend Backend
}

// New builds a Client backed by go-containerregistry.
func New(opts Options) (*Client, error) {
	if opts.Dir == "" {
		return nil, fmt.Errorf("registry: cache Dir is required")
	}
	if err := os.MkdirAll(opts.Dir, 0o755); err != nil {
		return nil, fmt.Errorf("registry: create cache dir: %w", err)
	}
	ttl := opts.TTL
	if ttl == 0 {
		ttl = DefaultTTL
	}
	ctx := opts.Context
	if ctx == nil {
		ctx = context.Background()
	}
	kc := opts.Keychain
	if kc == nil {
		kc = authn.DefaultKeychain
	}
	ua := opts.UserAgent
	if ua == "" {
		ua = "ocidb"
	}
	be := opts.Backend
	if be == nil {
		be = &remoteBackend{ctx: ctx, keychain: kc, userAgent: ua}
	}
	return &Client{
		dir: opts.Dir,
		ttl: ttl,
		be:  be,
	}, nil
}

// Stats reports cache hit/miss counts accumulated over the client's lifetime.
func (c *Client) Stats() (hits, misses int) {
	c.mu.Lock()
	defer c.mu.Unlock()
	return c.hits, c.misses
}

func (c *Client) hit()  { c.mu.Lock(); c.hits++; c.mu.Unlock() }
func (c *Client) miss() { c.mu.Lock(); c.misses++; c.mu.Unlock() }

// Tags returns the tag list for a repository (e.g. "library/nginx" or "nginx").
func (c *Client) Tags(repoInput string) ([]string, error) {
	repo, err := name.NewRepository(repoInput)
	if err != nil {
		return nil, fmt.Errorf("parse repository %q: %w", repoInput, err)
	}
	key := repo.Name()
	path := c.cachePath("tags", hashKey(key)+".json")

	var env tagsEnvelope
	if c.readFresh(path, &env, &env.FetchedAt) {
		c.hit()
		return env.Tags, nil
	}
	c.miss()
	tags, err := c.be.ListTags(key)
	if err != nil {
		return nil, err
	}
	_ = c.writeJSON(path, tagsEnvelope{Repo: key, FetchedAt: time.Now(), Tags: tags})
	return tags, nil
}

// Manifest returns the manifest (image or index) for a reference. Digest
// references are served from the permanent content-addressed cache; tag
// references resolve through a TTL-bounded tag->digest record.
func (c *Client) Manifest(refInput string) (Manifest, error) {
	ref, err := name.ParseReference(refInput)
	if err != nil {
		return Manifest{}, fmt.Errorf("parse reference %q: %w", refInput, err)
	}
	full := ref.Name()

	if dref, ok := ref.(name.Digest); ok {
		if m, ok := c.loadManifestByDigest(dref.DigestStr()); ok {
			c.hit()
			m.Ref = full
			return m, nil
		}
		c.miss()
		return c.fetchManifest(ref)
	}

	var env refEnvelope
	if c.readFresh(c.cachePath("refs", hashKey(full)+".json"), &env, &env.FetchedAt) {
		if m, ok := c.loadManifestByDigest(env.Digest); ok {
			c.hit()
			m.Ref = full
			return m, nil
		}
	}
	c.miss()
	return c.fetchManifest(ref)
}

func (c *Client) fetchManifest(ref name.Reference) (Manifest, error) {
	m, err := c.be.GetManifest(ref.Name())
	if err != nil {
		return Manifest{}, err
	}
	m.Ref = ref.Name()
	_ = c.writeJSON(c.cachePath("manifests", digestFile(m.Digest)+".json"), manifestEnvelope{
		Digest:    m.Digest,
		MediaType: m.MediaType,
		Size:      m.Size,
		Raw:       json.RawMessage(m.Raw),
	})
	if _, isDigest := ref.(name.Digest); !isDigest {
		_ = c.writeJSON(c.cachePath("refs", hashKey(ref.Name())+".json"), refEnvelope{
			Ref:       ref.Name(),
			FetchedAt: time.Now(),
			Digest:    m.Digest,
			MediaType: m.MediaType,
			Size:      m.Size,
		})
	}
	return m, nil
}

func (c *Client) loadManifestByDigest(digest string) (Manifest, bool) {
	b, err := os.ReadFile(c.cachePath("manifests", digestFile(digest)+".json"))
	if err != nil {
		return Manifest{}, false
	}
	var env manifestEnvelope
	if err := json.Unmarshal(b, &env); err != nil {
		return Manifest{}, false
	}
	return Manifest{
		Digest:    env.Digest,
		MediaType: env.MediaType,
		Size:      env.Size,
		Raw:       []byte(env.Raw),
	}, true
}

// Blob returns a blob (used for config blobs) by digest. Blobs are immutable,
// so they are cached forever.
func (c *Client) Blob(repo, digest string) ([]byte, error) {
	path := c.cachePath("blobs", digestFile(digest))
	if b, err := os.ReadFile(path); err == nil {
		c.hit()
		return b, nil
	}
	c.miss()
	b, err := c.be.GetBlob(repo, digest)
	if err != nil {
		return nil, err
	}
	_ = c.writeBytes(path, b)
	return b, nil
}

// ManifestView is a parsed manifest: either an image index (with Children) or
// an image manifest (with ConfigDigest and Layers).
type ManifestView struct {
	Ref           string
	Digest        string
	MediaType     string
	Size          int64
	SchemaVersion int64
	IsIndex       bool
	ConfigDigest  string          // image manifests only
	Layers        []v1.Descriptor // image manifests only
	Children      []v1.Descriptor // indexes only (carry .Platform)
	Annotations   map[string]string
	Raw           []byte
}

// ManifestView fetches and parses the manifest for a reference.
func (c *Client) ManifestView(refInput string) (*ManifestView, error) {
	m, err := c.Manifest(refInput)
	if err != nil {
		return nil, err
	}
	mv := &ManifestView{
		Ref:       m.Ref,
		Digest:    m.Digest,
		MediaType: m.MediaType,
		Size:      m.Size,
		Raw:       m.Raw,
	}
	if types.MediaType(m.MediaType).IsIndex() {
		idx, err := v1.ParseIndexManifest(bytes.NewReader(m.Raw))
		if err != nil {
			return nil, fmt.Errorf("parse index %s: %w", m.Ref, err)
		}
		mv.IsIndex = true
		mv.SchemaVersion = idx.SchemaVersion
		mv.Children = idx.Manifests
		mv.Annotations = idx.Annotations
		return mv, nil
	}
	mf, err := v1.ParseManifest(bytes.NewReader(m.Raw))
	if err != nil {
		return nil, fmt.Errorf("parse manifest %s: %w", m.Ref, err)
	}
	mv.SchemaVersion = mf.SchemaVersion
	mv.ConfigDigest = mf.Config.Digest.String()
	mv.Layers = mf.Layers
	mv.Annotations = mf.Annotations
	return mv, nil
}

// ImageView is a fully resolved image: the platform-specific manifest plus its
// parsed config file.
type ImageView struct {
	Ref            string
	Platform       string
	ManifestDigest string
	MediaType      string
	ConfigDigest   string
	ManifestSize   int64
	Layers         []v1.Descriptor
	Config         *v1.ConfigFile
}

// ResolveImage resolves a reference to a single platform image and parses its
// config. For an index, the platform (e.g. "linux/arm64") selects a child
// manifest; "" means DefaultPlatform. For a plain image manifest the platform
// argument is ignored.
func (c *Client) ResolveImage(refInput, platform string) (*ImageView, error) {
	if platform == "" {
		platform = DefaultPlatform
	}
	mv, err := c.ManifestView(refInput)
	if err != nil {
		return nil, err
	}
	ref, err := name.ParseReference(refInput)
	if err != nil {
		return nil, fmt.Errorf("parse reference %q: %w", refInput, err)
	}
	repo := ref.Context().Name()

	iv := &ImageView{Ref: mv.Ref, Platform: platform}
	imgMV := mv
	if mv.IsIndex {
		child, err := pickPlatform(mv.Children, platform)
		if err != nil {
			return nil, fmt.Errorf("%s: %w", mv.Ref, err)
		}
		imgMV, err = c.ManifestView(repo + "@" + child.Digest.String())
		if err != nil {
			return nil, err
		}
		if imgMV.IsIndex {
			return nil, fmt.Errorf("%s: nested index is not supported", mv.Ref)
		}
	}
	iv.ManifestDigest = imgMV.Digest
	iv.MediaType = imgMV.MediaType
	iv.ConfigDigest = imgMV.ConfigDigest
	iv.ManifestSize = imgMV.Size
	iv.Layers = imgMV.Layers

	cfgBytes, err := c.Blob(repo, iv.ConfigDigest)
	if err != nil {
		return nil, err
	}
	cfg, err := v1.ParseConfigFile(bytes.NewReader(cfgBytes))
	if err != nil {
		return nil, fmt.Errorf("parse config %s: %w", iv.ConfigDigest, err)
	}
	iv.Config = cfg
	return iv, nil
}

// Platforms returns the platforms a reference is built for. For an index this
// is the set of (non-attestation) child platforms; for a plain image it is the
// single platform recorded in the config.
func (c *Client) Platforms(refInput string) ([]v1.Descriptor, error) {
	mv, err := c.ManifestView(refInput)
	if err != nil {
		return nil, err
	}
	if mv.IsIndex {
		out := make([]v1.Descriptor, 0, len(mv.Children))
		for _, d := range mv.Children {
			if isAttestation(d) {
				continue
			}
			out = append(out, d)
		}
		return out, nil
	}
	// Plain image manifest: synthesize one descriptor from the config.
	iv, err := c.ResolveImage(refInput, "")
	if err != nil {
		return nil, err
	}
	d := v1.Descriptor{
		MediaType: types.MediaType(mv.MediaType),
		Size:      mv.Size,
		Platform: &v1.Platform{
			OS:           iv.Config.OS,
			Architecture: iv.Config.Architecture,
			Variant:      iv.Config.Variant,
			OSVersion:    iv.Config.OSVersion,
		},
	}
	if h, err := v1.NewHash(mv.Digest); err == nil {
		d.Digest = h
	}
	return []v1.Descriptor{d}, nil
}

// pickPlatform chooses the index child matching platform ("os/arch[/variant]").
func pickPlatform(children []v1.Descriptor, platform string) (v1.Descriptor, error) {
	wantOS, wantArch, wantVariant := splitPlatform(platform)
	var available []string
	for _, d := range children {
		if d.Platform == nil || isAttestation(d) {
			continue
		}
		available = append(available, d.Platform.String())
		if d.Platform.OS == wantOS && d.Platform.Architecture == wantArch &&
			(wantVariant == "" || d.Platform.Variant == wantVariant) {
			return d, nil
		}
	}
	return v1.Descriptor{}, fmt.Errorf("no image for platform %q (available: %s)", platform, strings.Join(available, ", "))
}

func splitPlatform(p string) (os, arch, variant string) {
	parts := strings.Split(p, "/")
	if len(parts) > 0 {
		os = parts[0]
	}
	if len(parts) > 1 {
		arch = parts[1]
	}
	if len(parts) > 2 {
		variant = parts[2]
	}
	return os, arch, variant
}

// isAttestation reports whether a child descriptor is a buildkit attestation
// manifest (platform "unknown/unknown") rather than a runnable image.
func isAttestation(d v1.Descriptor) bool {
	if d.Platform == nil {
		return false
	}
	return d.Platform.OS == "unknown" || d.Platform.Architecture == "unknown"
}

// --- cache plumbing ---------------------------------------------------------

type tagsEnvelope struct {
	Repo      string    `json:"repo"`
	FetchedAt time.Time `json:"fetchedAt"`
	Tags      []string  `json:"tags"`
}

type refEnvelope struct {
	Ref       string    `json:"ref"`
	FetchedAt time.Time `json:"fetchedAt"`
	Digest    string    `json:"digest"`
	MediaType string    `json:"mediaType"`
	Size      int64     `json:"size"`
}

type manifestEnvelope struct {
	Digest    string          `json:"digest"`
	MediaType string          `json:"mediaType"`
	Size      int64           `json:"size"`
	Raw       json.RawMessage `json:"raw"`
}

func (c *Client) cachePath(parts ...string) string {
	return filepath.Join(append([]string{c.dir}, parts...)...)
}

// readFresh loads JSON into out and reports whether it exists and is fresh.
// fetchedAt must point at out's timestamp field (populated by Unmarshal).
func (c *Client) readFresh(path string, out any, fetchedAt *time.Time) bool {
	b, err := os.ReadFile(path)
	if err != nil {
		return false
	}
	if err := json.Unmarshal(b, out); err != nil {
		return false
	}
	if c.ttl < 0 {
		return true
	}
	return time.Since(*fetchedAt) <= c.ttl
}

func (c *Client) writeJSON(path string, v any) error {
	b, err := json.MarshalIndent(v, "", "  ")
	if err != nil {
		return err
	}
	return c.writeBytes(path, b)
}

func (c *Client) writeBytes(path string, b []byte) error {
	if err := os.MkdirAll(filepath.Dir(path), 0o755); err != nil {
		return err
	}
	tmp, err := os.CreateTemp(filepath.Dir(path), ".tmp-*")
	if err != nil {
		return err
	}
	tmpName := tmp.Name()
	if _, err := tmp.Write(b); err != nil {
		tmp.Close()
		os.Remove(tmpName)
		return err
	}
	if err := tmp.Close(); err != nil {
		os.Remove(tmpName)
		return err
	}
	return os.Rename(tmpName, path)
}

func hashKey(s string) string {
	sum := sha256.Sum256([]byte(s))
	return hex.EncodeToString(sum[:])
}

// digestFile turns "sha256:abc..." into a filesystem-safe "sha256-abc...".
func digestFile(digest string) string {
	return strings.ReplaceAll(digest, ":", "-")
}

// --- live backend -----------------------------------------------------------

var _ Backend = (*remoteBackend)(nil)

type remoteBackend struct {
	ctx       context.Context
	keychain  authn.Keychain
	userAgent string
}

func (b *remoteBackend) options() []remote.Option {
	return []remote.Option{
		remote.WithContext(b.ctx),
		remote.WithAuthFromKeychain(b.keychain),
		remote.WithUserAgent(b.userAgent),
	}
}

func (b *remoteBackend) ListTags(repoStr string) ([]string, error) {
	repo, err := name.NewRepository(repoStr)
	if err != nil {
		return nil, fmt.Errorf("parse repository %q: %w", repoStr, err)
	}
	tags, err := remote.List(repo, b.options()...)
	if err != nil {
		return nil, fmt.Errorf("list tags for %q: %w", repoStr, err)
	}
	return tags, nil
}

func (b *remoteBackend) GetManifest(refStr string) (Manifest, error) {
	ref, err := name.ParseReference(refStr)
	if err != nil {
		return Manifest{}, fmt.Errorf("parse reference %q: %w", refStr, err)
	}
	desc, err := remote.Get(ref, b.options()...)
	if err != nil {
		return Manifest{}, fmt.Errorf("get manifest %q: %w", refStr, err)
	}
	return Manifest{
		Ref:       ref.Name(),
		Digest:    desc.Digest.String(),
		MediaType: string(desc.MediaType),
		Size:      desc.Size,
		Raw:       desc.Manifest,
	}, nil
}

func (b *remoteBackend) GetBlob(repoStr, digest string) ([]byte, error) {
	dig, err := name.NewDigest(repoStr + "@" + digest)
	if err != nil {
		return nil, fmt.Errorf("parse digest %q: %w", repoStr+"@"+digest, err)
	}
	layer, err := remote.Layer(dig, b.options()...)
	if err != nil {
		return nil, fmt.Errorf("fetch blob %q: %w", digest, err)
	}
	rc, err := layer.Compressed()
	if err != nil {
		return nil, fmt.Errorf("open blob %q: %w", digest, err)
	}
	defer rc.Close()
	return io.ReadAll(rc)
}

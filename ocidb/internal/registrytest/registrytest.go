// Package registrytest provides an in-memory registry.Backend with a small,
// deterministic fixture so the rest of ocidb can be tested without touching the
// network. The fixture mimics Docker Hub: a multi-arch index (linux/amd64 +
// linux/arm64 + a buildkit attestation) under index.docker.io/library/demo, and
// a single-arch repo under index.docker.io/library/single.
package registrytest

import (
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"sync"
	"time"

	v1 "github.com/google/go-containerregistry/pkg/v1"
	"github.com/google/go-containerregistry/pkg/v1/types"

	"github.com/imjasonh/playground/ocidb/internal/registry"
)

// Repository names used by the fixture (fully normalized, as the client sees them).
const (
	DemoRepo   = "index.docker.io/library/demo"
	SingleRepo = "index.docker.io/library/single"
)

// Created is the fixed build timestamp baked into every fixture image.
var Created = time.Date(2024, 3, 4, 5, 6, 7, 0, time.UTC)

// Fake is an in-memory registry.Backend. It records how many network-style
// calls it received so tests can assert that the cache is doing its job.
type Fake struct {
	mu        sync.Mutex
	tags      map[string][]string
	manifests map[string]registry.Manifest
	blobs     map[string][]byte

	ManifestCalls int
	BlobCalls     int
	TagCalls      int
}

var _ registry.Backend = (*Fake)(nil)

func (f *Fake) ListTags(repo string) ([]string, error) {
	f.mu.Lock()
	defer f.mu.Unlock()
	f.TagCalls++
	t, ok := f.tags[repo]
	if !ok {
		return nil, fmt.Errorf("fake: no tags for %q", repo)
	}
	return append([]string(nil), t...), nil
}

func (f *Fake) GetManifest(ref string) (registry.Manifest, error) {
	f.mu.Lock()
	defer f.mu.Unlock()
	f.ManifestCalls++
	m, ok := f.manifests[ref]
	if !ok {
		return registry.Manifest{}, fmt.Errorf("fake: no manifest for %q", ref)
	}
	return m, nil
}

func (f *Fake) GetBlob(repo, digest string) ([]byte, error) {
	f.mu.Lock()
	defer f.mu.Unlock()
	f.BlobCalls++
	b, ok := f.blobs[repo+"@"+digest]
	if !ok {
		return nil, fmt.Errorf("fake: no blob %s@%s", repo, digest)
	}
	return append([]byte(nil), b...), nil
}

// Calls returns the cumulative call counts.
func (f *Fake) Calls() (manifests, blobs, tags int) {
	f.mu.Lock()
	defer f.mu.Unlock()
	return f.ManifestCalls, f.BlobCalls, f.TagCalls
}

// New builds the fixture Fake.
func New() *Fake {
	f := &Fake{
		tags:      map[string][]string{},
		manifests: map[string]registry.Manifest{},
		blobs:     map[string][]byte{},
	}

	// Two single-arch images that the index points at.
	amd := f.addImage(DemoRepo, "amd64", "", []int64{1000, 2000})
	arm := f.addImage(DemoRepo, "arm64", "v8", []int64{1100, 2100})

	// A buildkit attestation child (platform unknown/unknown) that should be
	// ignored by platform listing and resolution.
	att := buildImage("unknown", "", []int64{1})
	attMf := att.manifestBytes
	attDigest := digestOf(attMf)

	idx := v1.IndexManifest{
		SchemaVersion: 2,
		MediaType:     types.DockerManifestList,
		Manifests: []v1.Descriptor{
			{MediaType: types.DockerManifestSchema2, Size: int64(len(amd.manifestBytes)), Digest: mustHash(amd.manifestDigest), Platform: &v1.Platform{OS: "linux", Architecture: "amd64"}},
			{MediaType: types.DockerManifestSchema2, Size: int64(len(arm.manifestBytes)), Digest: mustHash(arm.manifestDigest), Platform: &v1.Platform{OS: "linux", Architecture: "arm64", Variant: "v8"}},
			{MediaType: types.OCIManifestSchema1, Size: int64(len(attMf)), Digest: mustHash(attDigest), Platform: &v1.Platform{OS: "unknown", Architecture: "unknown"}},
		},
	}
	idxBytes, _ := json.Marshal(idx)
	idxDigest := digestOf(idxBytes)
	idxManifest := registry.Manifest{Digest: idxDigest, MediaType: string(types.DockerManifestList), Size: int64(len(idxBytes)), Raw: idxBytes}

	f.tags[DemoRepo] = []string{"latest", "1.0", "2.0", "2.1"}
	f.manifests[DemoRepo+":latest"] = idxManifest
	f.manifests[DemoRepo+"@"+idxDigest] = idxManifest

	// A plain single-arch repo (no index).
	single := f.addImage(SingleRepo, "amd64", "", []int64{4242})
	f.tags[SingleRepo] = []string{"latest"}
	f.manifests[SingleRepo+":latest"] = registry.Manifest{
		Digest:    single.manifestDigest,
		MediaType: string(types.DockerManifestSchema2),
		Size:      int64(len(single.manifestBytes)),
		Raw:       single.manifestBytes,
	}

	return f
}

type builtImage struct {
	manifestBytes  []byte
	manifestDigest string
	configBytes    []byte
	configDigest   string
}

// addImage builds an image, registers its manifest (addressable by digest under
// repo) and its config blob, and returns the build for wiring into an index.
func (f *Fake) addImage(repo, arch, variant string, layerSizes []int64) builtImage {
	img := buildImage(arch, variant, layerSizes)
	f.manifests[repo+"@"+img.manifestDigest] = registry.Manifest{
		Digest:    img.manifestDigest,
		MediaType: string(types.DockerManifestSchema2),
		Size:      int64(len(img.manifestBytes)),
		Raw:       img.manifestBytes,
	}
	f.blobs[repo+"@"+img.configDigest] = img.configBytes
	return img
}

func buildImage(arch, variant string, layerSizes []int64) builtImage {
	cfg := v1.ConfigFile{
		Architecture: arch,
		Variant:      variant,
		OS:           "linux",
		Created:      v1.Time{Time: Created},
		Author:       "ocidb-test",
		Config: v1.Config{
			User:         "1000",
			WorkingDir:   "/app",
			Env:          []string{"PATH=/usr/local/bin:/usr/bin", "DEMO=1"},
			Entrypoint:   []string{"/entrypoint.sh"},
			Cmd:          []string{"sh"},
			ExposedPorts: map[string]struct{}{"80/tcp": {}},
			Labels: map[string]string{
				"maintainer":                     "ocidb",
				"org.opencontainers.image.title": "demo",
			},
		},
		History: []v1.History{
			{Created: v1.Time{Time: Created}, CreatedBy: "ADD rootfs / # buildkit"},
			{Created: v1.Time{Time: Created}, CreatedBy: "RUN apk add --no-cache demo"},
			{Created: v1.Time{Time: Created}, CreatedBy: `CMD ["sh"]`, EmptyLayer: true},
		},
	}
	cfgBytes, _ := json.Marshal(cfg)
	cfgDigest := digestOf(cfgBytes)

	layers := make([]v1.Descriptor, len(layerSizes))
	for i, sz := range layerSizes {
		layers[i] = v1.Descriptor{
			MediaType: types.DockerLayer,
			Size:      sz,
			Digest:    mustHash(digestOf([]byte(fmt.Sprintf("%s-%s-layer-%d", arch, variant, i)))),
		}
	}
	mf := v1.Manifest{
		SchemaVersion: 2,
		MediaType:     types.DockerManifestSchema2,
		Config:        v1.Descriptor{MediaType: types.DockerConfigJSON, Size: int64(len(cfgBytes)), Digest: mustHash(cfgDigest)},
		Layers:        layers,
	}
	mfBytes, _ := json.Marshal(mf)
	return builtImage{
		manifestBytes:  mfBytes,
		manifestDigest: digestOf(mfBytes),
		configBytes:    cfgBytes,
		configDigest:   cfgDigest,
	}
}

func digestOf(b []byte) string {
	sum := sha256.Sum256(b)
	return "sha256:" + hex.EncodeToString(sum[:])
}

func mustHash(d string) v1.Hash {
	h, err := v1.NewHash(d)
	if err != nil {
		panic(err)
	}
	return h
}

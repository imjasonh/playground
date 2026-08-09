// Package publish pushes a WebAssembly module to a registry.
//
// What goes up is an OCI artifact, not an image: there is no root filesystem
// and nothing to exec, just one blob that happens to be a wasm module. That is
// why the ordinary tools do not fit — `docker push` and `crane push` both want
// a filesystem to tar up — and why the manifest is assembled here by hand. The
// registry work itself (auth, blob upload, digest verification) is
// go-containerregistry's.
//
// The shape below is what the iOS Wasm Service experiment looks for: an
// artifactType that says wasm, an empty config, and a single layer whose media
// type says wasm.
package publish

import (
	"bytes"
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"maps"
	"slices"

	"github.com/google/go-containerregistry/pkg/name"
	v1 "github.com/google/go-containerregistry/pkg/v1"
	"github.com/google/go-containerregistry/pkg/v1/remote"
	"github.com/google/go-containerregistry/pkg/v1/static"
	"github.com/google/go-containerregistry/pkg/v1/types"
)

const (
	// ArtifactType marks the whole manifest as carrying a wasm module. Nothing
	// has standardized this; it is the spelling in circulation.
	ArtifactType = "application/vnd.wasm.config.v0+json"

	// LayerMediaType is the module blob's type, and the one registered with
	// IANA for WebAssembly.
	LayerMediaType = "application/wasm"

	// TitleAnnotation names the blob. A puller that recognizes none of the
	// media types above can still find the module by its file name.
	TitleAnnotation = "org.opencontainers.image.title"

	// emptyConfigMediaType is OCI 1.1's stand-in for "there is no config".
	// An artifact has no image config to point at, but the manifest schema
	// requires the field, so it points at the two bytes `{}`.
	emptyConfigMediaType = "application/vnd.oci.empty.v1+json"
)

var emptyConfig = static.NewLayer([]byte("{}"), emptyConfigMediaType)

// Artifact is a manifest and the blobs it names, ready to push.
//
// It implements remote.Taggable over its own manifest bytes rather than
// letting go-containerregistry marshal a v1.Manifest for it, so the digest a
// caller prints is a digest of exactly what was uploaded.
type Artifact struct {
	manifest v1.Manifest
	raw      []byte
	module   v1.Layer
}

// Build assembles the artifact around a module. Given the same module,
// title, and annotations it produces the same bytes, and therefore the same
// digest, on every run: nothing in here reads the clock.
func Build(module []byte, title string, annotations map[string]string) (*Artifact, error) {
	if len(module) == 0 {
		return nil, errors.New("module is empty")
	}

	layer := static.NewLayer(module, LayerMediaType)
	layerDescriptor, err := describe(layer)
	if err != nil {
		return nil, fmt.Errorf("describe module: %w", err)
	}
	if title != "" {
		layerDescriptor.Annotations = map[string]string{TitleAnnotation: title}
	}

	configDescriptor, err := describe(emptyConfig)
	if err != nil {
		return nil, fmt.Errorf("describe config: %w", err)
	}
	// Inlining the two bytes lets a client skip a request for a blob whose
	// contents are a foregone conclusion.
	configDescriptor.Data = []byte("{}")

	manifest := v1.Manifest{
		SchemaVersion: 2,
		MediaType:     types.OCIManifestSchema1,
		ArtifactType:  ArtifactType,
		Config:        configDescriptor,
		Layers:        []v1.Descriptor{layerDescriptor},
	}
	if len(annotations) > 0 {
		manifest.Annotations = maps.Clone(annotations)
	}

	raw, err := json.Marshal(manifest)
	if err != nil {
		return nil, fmt.Errorf("marshal manifest: %w", err)
	}
	return &Artifact{manifest: manifest, raw: raw, module: layer}, nil
}

// Manifest returns the assembled manifest.
func (a *Artifact) Manifest() v1.Manifest { return a.manifest }

// RawManifest satisfies remote.Taggable.
func (a *Artifact) RawManifest() ([]byte, error) { return a.raw, nil }

// MediaType tells remote.Put what Content-Type to send. Without it the push
// would be labelled a Docker schema 2 manifest, which this is not.
func (a *Artifact) MediaType() (types.MediaType, error) { return types.OCIManifestSchema1, nil }

// Digest is the digest of the manifest bytes, which is what a tag resolves to.
func (a *Artifact) Digest() (v1.Hash, error) {
	hash, _, err := v1.SHA256(bytes.NewReader(a.raw))
	return hash, err
}

// Pretty renders the manifest for a human to read.
func (a *Artifact) Pretty() (string, error) {
	var out bytes.Buffer
	if err := json.Indent(&out, a.raw, "", "  "); err != nil {
		return "", err
	}
	return out.String(), nil
}

// Push uploads the artifact to repo under every tag and returns the digest
// reference. The digest is the useful half of the answer: a tag can move and
// a digest cannot, so that is the string worth recording.
func Push(ctx context.Context, repo string, tags []string, artifact *Artifact, options ...remote.Option) (string, error) {
	if len(tags) == 0 {
		return "", errors.New("no tags to push")
	}
	repository, err := name.NewRepository(repo)
	if err != nil {
		return "", fmt.Errorf("parse %q: %w", repo, err)
	}
	options = append(slices.Clone(options), remote.WithContext(ctx))

	// Blobs first. A registry rejects a manifest naming a blob it does not
	// have, and rightly — that would be a reference to nothing.
	for _, blob := range []v1.Layer{emptyConfig, artifact.module} {
		if err := remote.WriteLayer(repository, blob, options...); err != nil {
			return "", fmt.Errorf("upload blob: %w", err)
		}
	}
	for _, tag := range tags {
		if err := remote.Put(repository.Tag(tag), artifact, options...); err != nil {
			return "", fmt.Errorf("push %s:%s: %w", repository.Name(), tag, err)
		}
	}

	digest, err := artifact.Digest()
	if err != nil {
		return "", err
	}
	return repository.Digest(digest.String()).Name(), nil
}

func describe(layer v1.Layer) (v1.Descriptor, error) {
	digest, err := layer.Digest()
	if err != nil {
		return v1.Descriptor{}, err
	}
	size, err := layer.Size()
	if err != nil {
		return v1.Descriptor{}, err
	}
	mediaType, err := layer.MediaType()
	if err != nil {
		return v1.Descriptor{}, err
	}
	return v1.Descriptor{MediaType: mediaType, Size: size, Digest: digest}, nil
}

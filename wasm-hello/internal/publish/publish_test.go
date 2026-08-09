package publish_test

import (
	"context"
	"encoding/json"
	"io"
	"log"
	"net/http/httptest"
	"net/url"
	"strings"
	"testing"

	"github.com/google/go-containerregistry/pkg/name"
	"github.com/google/go-containerregistry/pkg/registry"
	v1 "github.com/google/go-containerregistry/pkg/v1"
	"github.com/google/go-containerregistry/pkg/v1/remote"
	"github.com/imjasonh/playground/wasm-hello/internal/publish"
)

// A wasm module's first eight bytes, which is all any of this cares about.
var module = append([]byte("\x00asm\x01\x00\x00\x00"), []byte("pretend this is a Go service")...)

func TestManifestIsAWasmArtifact(t *testing.T) {
	artifact, err := publish.Build(module, "hello.wasm", map[string]string{
		"org.opencontainers.image.source": "https://github.com/imjasonh/playground",
	})
	if err != nil {
		t.Fatalf("Build: %v", err)
	}
	manifest := artifact.Manifest()

	if manifest.ArtifactType != publish.ArtifactType {
		t.Errorf("artifactType = %q, want %q", manifest.ArtifactType, publish.ArtifactType)
	}
	if got := string(manifest.MediaType); got != "application/vnd.oci.image.manifest.v1+json" {
		t.Errorf("mediaType = %q", got)
	}
	// An artifact points at the empty descriptor rather than an image config,
	// which is how a client tells there is no filesystem here.
	if got := string(manifest.Config.MediaType); got != "application/vnd.oci.empty.v1+json" {
		t.Errorf("config mediaType = %q", got)
	}
	if len(manifest.Layers) != 1 {
		t.Fatalf("got %d layers, want 1", len(manifest.Layers))
	}
	layer := manifest.Layers[0]
	if got := string(layer.MediaType); got != publish.LayerMediaType {
		t.Errorf("layer mediaType = %q, want %q", got, publish.LayerMediaType)
	}
	if got, want := layer.Size, int64(len(module)); got != want {
		t.Errorf("layer size = %d, want %d", got, want)
	}
	if got := layer.Annotations[publish.TitleAnnotation]; got != "hello.wasm" {
		t.Errorf("layer title = %q", got)
	}
	if got := manifest.Annotations["org.opencontainers.image.source"]; got == "" {
		t.Error("manifest annotations were dropped")
	}
}

// The digest has to be a digest of the bytes that go over the wire, or a
// caller pinning by digest pins something that was never published.
func TestDigestMatchesTheBytesPushed(t *testing.T) {
	artifact, err := publish.Build(module, "hello.wasm", nil)
	if err != nil {
		t.Fatalf("Build: %v", err)
	}
	raw, err := artifact.RawManifest()
	if err != nil {
		t.Fatalf("RawManifest: %v", err)
	}
	want, _, err := v1.SHA256(strings.NewReader(string(raw)))
	if err != nil {
		t.Fatal(err)
	}
	got, err := artifact.Digest()
	if err != nil {
		t.Fatalf("Digest: %v", err)
	}
	if got != want {
		t.Errorf("Digest = %s, want %s", got, want)
	}
}

func TestBuildIsReproducible(t *testing.T) {
	annotations := map[string]string{"b": "2", "a": "1"}
	first, err := publish.Build(module, "hello.wasm", annotations)
	if err != nil {
		t.Fatalf("Build: %v", err)
	}
	second, err := publish.Build(module, "hello.wasm", map[string]string{"a": "1", "b": "2"})
	if err != nil {
		t.Fatalf("Build: %v", err)
	}
	firstDigest, err := first.Digest()
	if err != nil {
		t.Fatal(err)
	}
	secondDigest, err := second.Digest()
	if err != nil {
		t.Fatal(err)
	}
	if firstDigest != secondDigest {
		t.Errorf("same inputs produced %s and %s", firstDigest, secondDigest)
	}
}

func TestEmptyModuleIsRefused(t *testing.T) {
	if _, err := publish.Build(nil, "hello.wasm", nil); err == nil {
		t.Error("Build accepted an empty module")
	}
}

// The whole trip: push to a registry, then pull it back the way the phone
// does — resolve the tag, read the manifest, fetch the layer it names.
func TestPushedArtifactPullsBack(t *testing.T) {
	repo := startRegistry(t) + "/wasm-hello"

	artifact, err := publish.Build(module, "hello.wasm", map[string]string{
		"org.opencontainers.image.revision": "abc123",
	})
	if err != nil {
		t.Fatalf("Build: %v", err)
	}

	reference, err := publish.Push(context.Background(), repo, []string{"latest", "abc123"}, artifact)
	if err != nil {
		t.Fatalf("Push: %v", err)
	}
	digest, err := artifact.Digest()
	if err != nil {
		t.Fatal(err)
	}
	if want := repo + "@" + digest.String(); reference != want {
		t.Errorf("Push returned %q, want %q", reference, want)
	}

	for _, tag := range []string{"latest", "abc123"} {
		ref, err := name.NewTag(repo + ":" + tag)
		if err != nil {
			t.Fatal(err)
		}
		descriptor, err := remote.Get(ref)
		if err != nil {
			t.Fatalf("get %s: %v", tag, err)
		}
		if descriptor.Digest != digest {
			t.Errorf("%s resolved to %s, want %s", tag, descriptor.Digest, digest)
		}

		var pulled v1.Manifest
		if err := json.Unmarshal(descriptor.Manifest, &pulled); err != nil {
			t.Fatalf("unmarshal manifest: %v", err)
		}
		if pulled.ArtifactType != publish.ArtifactType {
			t.Errorf("artifactType survived as %q", pulled.ArtifactType)
		}

		blob, err := remote.Layer(ref.Context().Digest(pulled.Layers[0].Digest.String()))
		if err != nil {
			t.Fatalf("layer: %v", err)
		}
		reader, err := blob.Compressed()
		if err != nil {
			t.Fatalf("open layer: %v", err)
		}
		defer reader.Close()
		var got strings.Builder
		if _, err := io.Copy(&got, reader); err != nil {
			t.Fatalf("read layer: %v", err)
		}
		if got.String() != string(module) {
			t.Error("the module that came back is not the one that went up")
		}
	}
}

func startRegistry(t *testing.T) string {
	t.Helper()
	server := httptest.NewServer(registry.New(registry.Logger(log.New(io.Discard, "", 0))))
	t.Cleanup(server.Close)
	parsed, err := url.Parse(server.URL)
	if err != nil {
		t.Fatal(err)
	}
	return parsed.Host
}

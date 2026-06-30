package registry_test

import (
	"strings"
	"testing"
	"time"

	"github.com/imjasonh/playground/ocidb/internal/registry"
	"github.com/imjasonh/playground/ocidb/internal/registrytest"
)

func newClient(t *testing.T, f registry.Backend, ttl time.Duration) *registry.Client {
	t.Helper()
	c, err := registry.New(registry.Options{Dir: t.TempDir(), TTL: ttl, Backend: f})
	if err != nil {
		t.Fatalf("registry.New: %v", err)
	}
	return c
}

func TestTagsCaching(t *testing.T) {
	f := registrytest.New()
	c := newClient(t, f, registry.DefaultTTL)

	for i := 0; i < 3; i++ {
		tags, err := c.Tags("demo")
		if err != nil {
			t.Fatalf("Tags: %v", err)
		}
		if got, want := strings.Join(tags, ","), "latest,1.0,2.0,2.1"; got != want {
			t.Fatalf("tags = %q, want %q", got, want)
		}
	}
	if _, _, tagCalls := f.Calls(); tagCalls != 1 {
		t.Fatalf("tag network calls = %d, want 1 (rest should be cached)", tagCalls)
	}
	if hits, misses := c.Stats(); hits != 2 || misses != 1 {
		t.Fatalf("stats = (%d hits, %d misses), want (2, 1)", hits, misses)
	}
}

func TestTagsTTLExpiry(t *testing.T) {
	f := registrytest.New()
	c := newClient(t, f, time.Nanosecond) // expires effectively immediately

	if _, err := c.Tags("demo"); err != nil {
		t.Fatal(err)
	}
	time.Sleep(2 * time.Millisecond)
	if _, err := c.Tags("demo"); err != nil {
		t.Fatal(err)
	}
	if _, _, tagCalls := f.Calls(); tagCalls != 2 {
		t.Fatalf("tag network calls = %d, want 2 (cache should have expired)", tagCalls)
	}
}

func TestManifestViewIndex(t *testing.T) {
	c := newClient(t, registrytest.New(), registry.DefaultTTL)
	mv, err := c.ManifestView("demo")
	if err != nil {
		t.Fatalf("ManifestView: %v", err)
	}
	if !mv.IsIndex {
		t.Fatalf("expected an index")
	}
	if len(mv.Children) != 3 {
		t.Fatalf("children = %d, want 3 (2 platforms + 1 attestation)", len(mv.Children))
	}
	if !strings.HasPrefix(mv.Digest, "sha256:") {
		t.Fatalf("digest = %q, want sha256:...", mv.Digest)
	}
}

func TestManifestViewSingleArch(t *testing.T) {
	c := newClient(t, registrytest.New(), registry.DefaultTTL)
	mv, err := c.ManifestView("single")
	if err != nil {
		t.Fatalf("ManifestView: %v", err)
	}
	if mv.IsIndex {
		t.Fatalf("single should not be an index")
	}
	if len(mv.Layers) != 1 {
		t.Fatalf("layers = %d, want 1", len(mv.Layers))
	}
	if mv.ConfigDigest == "" {
		t.Fatalf("expected a config digest")
	}
}

func TestPlatformsExcludesAttestation(t *testing.T) {
	c := newClient(t, registrytest.New(), registry.DefaultTTL)
	descs, err := c.Platforms("demo")
	if err != nil {
		t.Fatalf("Platforms: %v", err)
	}
	if len(descs) != 2 {
		t.Fatalf("platforms = %d, want 2 (attestation excluded)", len(descs))
	}
	got := map[string]bool{}
	for _, d := range descs {
		got[d.Platform.String()] = true
	}
	if !got["linux/amd64"] || !got["linux/arm64/v8"] {
		t.Fatalf("platforms = %v, want linux/amd64 and linux/arm64/v8", got)
	}
}

func TestResolveImageDefaultPlatform(t *testing.T) {
	c := newClient(t, registrytest.New(), registry.DefaultTTL)
	iv, err := c.ResolveImage("demo", "")
	if err != nil {
		t.Fatalf("ResolveImage: %v", err)
	}
	if iv.Config.Architecture != "amd64" {
		t.Fatalf("architecture = %q, want amd64 (default platform)", iv.Config.Architecture)
	}
	if len(iv.Layers) != 2 {
		t.Fatalf("layers = %d, want 2", len(iv.Layers))
	}
	if iv.Config.Created.Time.UTC() != registrytest.Created {
		t.Fatalf("created = %v, want %v", iv.Config.Created.Time.UTC(), registrytest.Created)
	}
}

func TestResolveImageSelectsPlatform(t *testing.T) {
	c := newClient(t, registrytest.New(), registry.DefaultTTL)
	iv, err := c.ResolveImage("demo", "linux/arm64")
	if err != nil {
		t.Fatalf("ResolveImage: %v", err)
	}
	if iv.Config.Architecture != "arm64" {
		t.Fatalf("architecture = %q, want arm64", iv.Config.Architecture)
	}
	if iv.Config.Variant != "v8" {
		t.Fatalf("variant = %q, want v8", iv.Config.Variant)
	}
}

func TestResolveImageUnknownPlatform(t *testing.T) {
	c := newClient(t, registrytest.New(), registry.DefaultTTL)
	_, err := c.ResolveImage("demo", "linux/ppc64le")
	if err == nil {
		t.Fatal("expected an error for an unavailable platform")
	}
	if !strings.Contains(err.Error(), "linux/amd64") {
		t.Fatalf("error %q should list available platforms", err)
	}
}

func TestContentAddressedCachedForever(t *testing.T) {
	f := registrytest.New()
	// Negative TTL would only affect mutable lookups; digest content is always
	// permanent. Use the default TTL and resolve twice.
	c := newClient(t, f, registry.DefaultTTL)

	if _, err := c.ResolveImage("demo", ""); err != nil {
		t.Fatal(err)
	}
	m1, b1, _ := f.Calls()
	if m1 != 2 || b1 != 1 {
		t.Fatalf("first resolve: %d manifest + %d blob calls, want 2 + 1", m1, b1)
	}
	if _, err := c.ResolveImage("demo", ""); err != nil {
		t.Fatal(err)
	}
	m2, b2, _ := f.Calls()
	if m2 != m1 || b2 != b1 {
		t.Fatalf("second resolve hit the network: manifest %d->%d, blob %d->%d", m1, m2, b1, b2)
	}
}

func TestNewRequiresDir(t *testing.T) {
	if _, err := registry.New(registry.Options{}); err == nil {
		t.Fatal("expected error when Dir is empty")
	}
}

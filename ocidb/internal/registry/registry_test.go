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

func TestLayerTOCAndCaching(t *testing.T) {
	f := registrytest.New()
	c := newClient(t, f, registry.DefaultTTL)
	iv, err := c.ResolveImage("demo", "")
	if err != nil {
		t.Fatal(err)
	}
	dig := iv.Layers[0].Digest.String()

	toc, err := c.LayerTOC("demo", dig)
	if err != nil {
		t.Fatalf("LayerTOC: %v", err)
	}
	byPath := map[string]registry.TarEntry{}
	for _, e := range toc {
		byPath[e.Path] = e
	}
	if e, ok := byPath["/etc/os-release"]; !ok || e.Type != "file" {
		t.Errorf("/etc/os-release = %+v, want a file entry", e)
	}
	if e, ok := byPath["/etc/"]; !ok || e.Type != "dir" {
		t.Errorf("/etc/ = %+v, want a dir entry", e)
	}
	if e, ok := byPath["/bin/sh"]; !ok || e.Type != "symlink" || e.Linkname != "busybox" {
		t.Errorf("/bin/sh = %+v, want symlink -> busybox", e)
	}

	// The TOC is cached by digest, so a second call must not refetch the blob.
	_, blobsBefore, _ := f.Calls()
	if _, err := c.LayerTOC("demo", dig); err != nil {
		t.Fatal(err)
	}
	_, blobsAfter, _ := f.Calls()
	if blobsAfter != blobsBefore {
		t.Fatalf("second LayerTOC fetched %d blobs, want 0 (cached)", blobsAfter-blobsBefore)
	}
}

func TestReadLayerFiles(t *testing.T) {
	c := newClient(t, registrytest.New(), registry.DefaultTTL)
	iv, err := c.ResolveImage("demo", "")
	if err != nil {
		t.Fatal(err)
	}
	dig := iv.Layers[0].Digest.String()

	one, err := c.ReadLayerFiles("demo", dig, map[string]bool{"/etc/os-release": true}, 0)
	if err != nil {
		t.Fatalf("ReadLayerFiles(one): %v", err)
	}
	if len(one) != 1 || !strings.Contains(string(one["/etc/os-release"]), "Demo Linux (amd64)") {
		t.Fatalf("single read = %v, want just os-release", one)
	}

	all, err := c.ReadLayerFiles("demo", dig, nil, 0)
	if err != nil {
		t.Fatalf("ReadLayerFiles(all): %v", err)
	}
	if _, ok := all["/etc/os-release"]; !ok {
		t.Error("full read missing /etc/os-release")
	}
	if _, ok := all["/etc/"]; ok {
		t.Error("a directory should not appear as a file body")
	}
	if _, ok := all["/bin/sh"]; ok {
		t.Error("a symlink should not appear as a file body")
	}

	// A tiny size cap drops file bodies larger than it.
	capped, err := c.ReadLayerFiles("demo", dig, nil, 4)
	if err != nil {
		t.Fatal(err)
	}
	if _, ok := capped["/etc/os-release"]; ok {
		t.Error("os-release exceeds the 4-byte cap and should be skipped")
	}
}

func TestOverlay(t *testing.T) {
	file := func(p string) registry.TarEntry { return registry.TarEntry{Path: p, Type: "file"} }
	dir := func(p string) registry.TarEntry { return registry.TarEntry{Path: p, Type: "dir"} }

	layers := [][]registry.TarEntry{
		{ // layer 0 (base)
			file("/a"),
			file("/b"),
			dir("/dir/"),
			file("/dir/x"),
			dir("/op/"),
			file("/op/low"),
		},
		{ // layer 1: replace /a, delete /dir/x via whiteout
			file("/a"),
			file("/dir/.wh.x"),
		},
		{ // layer 2: opaque-clear /op lower contents, add /op/new
			file("/op/.wh..wh..opq"),
			file("/op/new"),
		},
	}
	info := registry.Overlay(layers)

	type want struct {
		present  bool
		whiteout string
	}
	cases := []struct {
		layer, entry int
		path         string
		want         want
	}{
		{0, 0, "/a", want{false, ""}},      // replaced by layer 1
		{0, 1, "/b", want{true, ""}},       // survives
		{0, 2, "/dir/", want{true, ""}},    // dir survives
		{0, 3, "/dir/x", want{false, ""}},  // whiteout-deleted
		{0, 4, "/op/", want{true, ""}},     // opaque keeps the dir itself
		{0, 5, "/op/low", want{false, ""}}, // opaque clears lower contents
		{1, 0, "/a", want{true, ""}},       // winning copy of /a
		{1, 1, "/dir/.wh.x", want{false, "file"}},
		{2, 0, "/op/.wh..wh..opq", want{false, "opaque"}},
		{2, 1, "/op/new", want{true, ""}}, // added above the opaque marker
	}
	for _, c := range cases {
		got := info[c.layer][c.entry]
		if got.Present != c.want.present || got.Whiteout != c.want.whiteout {
			t.Errorf("%s (layer %d): present=%v whiteout=%q, want present=%v whiteout=%q",
				c.path, c.layer, got.Present, got.Whiteout, c.want.present, c.want.whiteout)
		}
	}
}

func TestNewRequiresDir(t *testing.T) {
	if _, err := registry.New(registry.Options{}); err == nil {
		t.Fatal("expected error when Dir is empty")
	}
}

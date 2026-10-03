// Package imagetest serves registries and makes base images for tests.
package imagetest

import (
	"archive/tar"
	"bytes"
	"io"
	"log"
	"net/http/httptest"
	"strings"
	"testing"

	"github.com/google/go-containerregistry/pkg/name"
	"github.com/google/go-containerregistry/pkg/registry"
	v1 "github.com/google/go-containerregistry/pkg/v1"
	"github.com/google/go-containerregistry/pkg/v1/empty"
	"github.com/google/go-containerregistry/pkg/v1/mutate"
	"github.com/google/go-containerregistry/pkg/v1/remote"
	"github.com/google/go-containerregistry/pkg/v1/tarball"
	"github.com/google/go-containerregistry/pkg/v1/types"
)

// Registry starts an in-memory registry that stops when the test ends, and
// returns its host, such as "127.0.0.1:43210".
func Registry(t testing.TB) string {
	t.Helper()
	srv := httptest.NewServer(registry.New(registry.Logger(log.New(io.Discard, "", 0))))
	t.Cleanup(srv.Close)
	return strings.TrimPrefix(srv.URL, "http://")
}

// Image makes an image like one of Chainguard's static images: one layer,
// and a config for a platform such as "linux/amd64" that runs as user
// 65532. mt is types.OCIManifestSchema1 or types.DockerManifestSchema2.
func Image(t testing.TB, platform string, mt types.MediaType) v1.Image {
	t.Helper()
	p, err := v1.ParsePlatform(platform)
	if err != nil {
		t.Fatal(err)
	}
	var buf bytes.Buffer
	tw := tar.NewWriter(&buf)
	body := "ID=base\nPLATFORM=" + platform + "\n"
	if err := tw.WriteHeader(&tar.Header{Name: "etc/os-release", Mode: 0o644, Size: int64(len(body))}); err != nil {
		t.Fatal(err)
	}
	_, _ = tw.Write([]byte(body))
	_ = tw.Close()
	layerType, configType := types.OCILayer, types.OCIConfigJSON
	if mt == types.DockerManifestSchema2 {
		layerType, configType = types.DockerLayer, types.DockerConfigJSON
	}
	layer, err := tarball.LayerFromOpener(func() (io.ReadCloser, error) {
		return io.NopCloser(bytes.NewReader(buf.Bytes())), nil
	}, tarball.WithMediaType(layerType))
	if err != nil {
		t.Fatal(err)
	}
	img, err := mutate.Append(mutate.MediaType(mutate.ConfigMediaType(empty.Image, configType), mt), mutate.Addendum{Layer: layer, MediaType: layerType})
	if err != nil {
		t.Fatal(err)
	}
	cf, err := img.ConfigFile()
	if err != nil {
		t.Fatal(err)
	}
	cf = cf.DeepCopy()
	cf.OS, cf.Architecture, cf.Variant = p.OS, p.Architecture, p.Variant
	cf.Config.User = "65532"
	cf.Config.Env = []string{"PATH=/usr/bin", "SSL_CERT_FILE=/etc/ssl/certs/ca-certificates.crt"}
	if img, err = mutate.ConfigFile(img, cf); err != nil {
		t.Fatal(err)
	}
	if mt == types.OCIManifestSchema1 {
		img = mutate.Annotations(img, map[string]string{
			"org.opencontainers.image.title":  "static",
			"org.opencontainers.image.source": "https://github.com/chainguard-images/images",
		}).(v1.Image)
	}
	return img
}

// Base pushes an OCI index to ref with one image from Image for each
// platform.
func Base(t testing.TB, ref string, platforms ...string) {
	t.Helper()
	idx := mutate.IndexMediaType(empty.Index, types.OCIImageIndex)
	for _, platform := range platforms {
		p, _ := v1.ParsePlatform(platform)
		idx = mutate.AppendManifests(idx, mutate.IndexAddendum{Add: Image(t, platform, types.OCIManifestSchema1), Descriptor: v1.Descriptor{Platform: p}})
	}
	r, err := name.ParseReference(ref)
	if err != nil {
		t.Fatal(err)
	}
	if err := remote.WriteIndex(r, idx); err != nil {
		t.Fatal(err)
	}
}

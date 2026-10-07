package image

import (
	"io"
	"log"
	"net/http"
	"net/http/httptest"
	"strings"
	"testing"

	"github.com/google/go-containerregistry/pkg/registry"

	"github.com/imjasonh/playground/kube/internal/image/imagetest"
)

func TestDigest(t *testing.T) {
	reg := imagetest.Registry(t)
	want := imagetest.Base(t, reg+"/chainguard/static:latest", "linux/amd64", "linux/arm64")
	const pinned = "sha256:0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"
	for ref, want := range map[string]string{
		reg + "/chainguard/static:latest":   want,
		reg + "/chainguard/static":          want,
		"registry.invalid/app@" + pinned:    pinned,
		"registry.invalid/app:v1@" + pinned: pinned,
	} {
		got, err := Digest(t.Context(), ref)
		if err != nil {
			t.Errorf("Digest(%q): %v", ref, err)
			continue
		}
		if got != want {
			t.Errorf("Digest(%q) = %q, want %q", ref, got, want)
		}
	}
	if _, err := Digest(t.Context(), reg+"/chainguard/static:nope"); err == nil || !strings.Contains(err.Error(), "MANIFEST_UNKNOWN") {
		t.Errorf("Digest() of a missing tag: %v, want the registry's error", err)
	}
}

func TestDigestWithoutHead(t *testing.T) {
	images := registry.New(registry.Logger(log.New(io.Discard, "", 0)))
	plain := httptest.NewServer(images)
	t.Cleanup(plain.Close)
	noHead := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		if r.Method == http.MethodHead {
			w.WriteHeader(http.StatusMethodNotAllowed)
			return
		}
		images.ServeHTTP(w, r)
	}))
	t.Cleanup(noHead.Close)
	want := imagetest.Base(t, strings.TrimPrefix(plain.URL, "http://")+"/chainguard/static:latest", "linux/amd64")
	got, err := Digest(t.Context(), strings.TrimPrefix(noHead.URL, "http://")+"/chainguard/static:latest")
	if err != nil {
		t.Fatal(err)
	}
	if got != want {
		t.Errorf("Digest() = %q, want %q", got, want)
	}
}

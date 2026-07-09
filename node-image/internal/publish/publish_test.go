package publish_test

import (
	"testing"

	"github.com/imjasonh/playground/node-image/internal/layer"
	"github.com/imjasonh/playground/node-image/internal/publish"
	v1 "github.com/google/go-containerregistry/pkg/v1"
)

func TestEmptyImageDeterministic(t *testing.T) {
	files := []layer.File{{Rel: "app/index.js", Mode: 0o644, Body: []byte("console.log(1)")}}
	opts := publish.Options{
		Workdir:    "/app",
		Entrypoint: []string{"/nodejs/bin/node"},
		Cmd:        []string{"/app/index.js"},
		Platform:   v1.Platform{OS: "linux", Architecture: "amd64"},
	}
	img1, err := publish.EmptyImage(opts, []publish.LayerFiles{{Files: files}})
	if err != nil {
		t.Fatal(err)
	}
	img2, err := publish.EmptyImage(opts, []publish.LayerFiles{{Files: files}})
	if err != nil {
		t.Fatal(err)
	}
	d1, _ := img1.Digest()
	d2, _ := img2.Digest()
	if d1 != d2 {
		t.Fatalf("%s vs %s", d1, d2)
	}
}

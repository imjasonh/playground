package image

import (
	"archive/tar"
	"io"
	"os"
	"path/filepath"
	"reflect"
	"strings"
	"testing"

	"github.com/google/go-containerregistry/pkg/name"
	v1 "github.com/google/go-containerregistry/pkg/v1"
	"github.com/google/go-containerregistry/pkg/v1/remote"
	"github.com/google/go-containerregistry/pkg/v1/types"

	"github.com/imjasonh/playground/kube/internal/image/imagetest"
)

func mustRef(t *testing.T, s string) name.Reference {
	t.Helper()
	r, err := name.ParseReference(s)
	if err != nil {
		t.Fatal(err)
	}
	return r
}

func executables(t *testing.T, platforms ...string) []Executable {
	t.Helper()
	dir := t.TempDir()
	var exes []Executable
	for _, s := range platforms {
		p, err := v1.ParsePlatform(s)
		if err != nil {
			t.Fatal(err)
		}
		f := filepath.Join(dir, strings.ReplaceAll(s, "/", "-"))
		if err := os.WriteFile(f, []byte("#!binary for "+s), 0o600); err != nil {
			t.Fatal(err)
		}
		exes = append(exes, Executable{Platform: *p, File: f})
	}
	return exes
}

func TestPush(t *testing.T) {
	reg := imagetest.Registry(t)
	baseRef := reg + "/chainguard/static:latest"
	imagetest.Base(t, baseRef, "linux/amd64", "linux/arm64", "linux/s390x")
	baseDesc, err := remote.Get(mustRef(t, baseRef))
	if err != nil {
		t.Fatal(err)
	}
	im := Image{
		Base:        baseRef,
		Repository:  reg + "/you/app",
		Tag:         "latest",
		Path:        "/app/website",
		Executables: executables(t, "linux/arm64", "linux/amd64"),
	}
	ref, err := Push(t.Context(), im)
	if err != nil {
		t.Fatal(err)
	}
	if !strings.HasPrefix(ref, reg+"/you/app@sha256:") {
		t.Fatalf("ref = %s", ref)
	}
	idx, err := remote.Index(mustRef(t, ref))
	if err != nil {
		t.Fatal(err)
	}
	man, err := idx.IndexManifest()
	if err != nil {
		t.Fatal(err)
	}
	if man.MediaType != types.OCIImageIndex || len(man.Manifests) != 2 ||
		man.Manifests[0].Platform.Architecture != "amd64" || man.Manifests[1].Platform.Architecture != "arm64" {
		t.Fatalf("index = %+v", man)
	}
	tagged, err := remote.Get(mustRef(t, reg+"/you/app:latest"))
	if err != nil || tagged.Digest.String() != strings.TrimPrefix(ref, reg+"/you/app@") {
		t.Errorf("the tag names %v, %v, not the index", tagged, err)
	}
	for _, d := range man.Manifests {
		img, err := idx.Image(d.Digest)
		if err != nil {
			t.Fatal(err)
		}
		m, _ := img.Manifest()
		if m.Annotations["org.opencontainers.image.base.name"] != baseRef || m.Annotations["org.opencontainers.image.base.digest"] != baseDesc.Digest.String() {
			t.Errorf("annotations = %v", m.Annotations)
		}
		cf, _ := img.ConfigFile()
		if cf.Architecture != d.Platform.Architecture || !cf.Created.Time.Equal(epoch.Time) || cf.Config.User != "65532" ||
			!reflect.DeepEqual(cf.Config.Entrypoint, []string{"/app/website"}) || len(cf.Config.Env) != 2 ||
			len(cf.RootFS.DiffIDs) != 2 || len(cf.History) != 2 || cf.History[1].CreatedBy != "kube generate" {
			t.Errorf("config = %+v", cf)
		}
		layers, _ := img.Layers()
		if len(layers) != 2 {
			t.Fatalf("%d layers", len(layers))
		}
		if mt, _ := layers[1].MediaType(); mt != types.OCILayer {
			t.Errorf("layer media type %s", mt)
		}
		rc, err := layers[1].Uncompressed()
		if err != nil {
			t.Fatal(err)
		}
		tr := tar.NewReader(rc)
		var names []string
		for {
			h, err := tr.Next()
			if err == io.EOF {
				break
			}
			if err != nil {
				t.Fatal(err)
			}
			names = append(names, h.Name)
			if h.Mode != 0o755 || h.Uid != 0 || !h.ModTime.Equal(epoch.Time) {
				t.Errorf("%s: mode %o, uid %d, mtime %v", h.Name, h.Mode, h.Uid, h.ModTime)
			}
			if h.Typeflag == tar.TypeReg {
				body, _ := io.ReadAll(tr)
				if want := "#!binary for linux/" + d.Platform.Architecture; string(body) != want {
					t.Errorf("%s holds %q, want %q", h.Name, body, want)
				}
			}
		}
		rc.Close()
		if !reflect.DeepEqual(names, []string{"app/", "app/website"}) {
			t.Errorf("layer entries = %v", names)
		}
	}

	again, err := Push(t.Context(), im)
	if err != nil || again != ref {
		t.Errorf("pushing again = %s, %v, want the same digest %s", again, err, ref)
	}
}

func TestPushOnePlatformBase(t *testing.T) {
	reg := imagetest.Registry(t)
	for _, mt := range []types.MediaType{types.OCIManifestSchema1, types.DockerManifestSchema2} {
		base := reg + "/single:" + map[types.MediaType]string{types.OCIManifestSchema1: "oci", types.DockerManifestSchema2: "docker"}[mt]
		if err := remote.Write(mustRef(t, base), imagetest.Image(t, "linux/amd64", mt)); err != nil {
			t.Fatal(err)
		}
		im := Image{Base: base, Repository: reg + "/app", Path: "/app", Executables: executables(t, "linux/amd64")}
		ref, err := Push(t.Context(), im)
		if err != nil {
			t.Fatal(err)
		}
		idx, err := remote.Index(mustRef(t, ref))
		if err != nil {
			t.Fatal(err)
		}
		wantIndex := map[types.MediaType]types.MediaType{types.OCIManifestSchema1: types.OCIImageIndex, types.DockerManifestSchema2: types.DockerManifestList}[mt]
		if got, _ := idx.MediaType(); got != wantIndex {
			t.Errorf("%s base: index media type %s, want %s", mt, got, wantIndex)
		}
		im.Executables = executables(t, "linux/amd64", "linux/arm64")
		if _, err := Push(t.Context(), im); err == nil || !strings.Contains(err.Error(), "one platform") {
			t.Errorf("two platforms on a one-platform base: %v", err)
		}
		im.Executables = executables(t, "linux/arm64")
		if _, err := Push(t.Context(), im); err == nil || !strings.Contains(err.Error(), "isn't for linux/arm64") {
			t.Errorf("another platform: %v", err)
		}
	}
	imagetest.Base(t, reg+"/multi:latest", "linux/amd64")
	im := Image{Base: reg + "/multi:latest", Repository: reg + "/app", Path: "/app", Executables: executables(t, "linux/arm64")}
	if _, err := Push(t.Context(), im); err == nil || !strings.Contains(err.Error(), "no image for linux/arm64") {
		t.Errorf("a platform the base lacks: %v", err)
	}
	im.Path = "app"
	if _, err := Push(t.Context(), im); err == nil || !strings.Contains(err.Error(), "must be absolute") {
		t.Errorf("a relative path: %v", err)
	}
}

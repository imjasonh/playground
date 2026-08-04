package ocirootfs

import (
	"archive/tar"
	"bytes"
	"io"
	"os"
	"path/filepath"
	"strings"
	"testing"

	v1 "github.com/google/go-containerregistry/pkg/v1"
	"github.com/google/go-containerregistry/pkg/v1/empty"
	"github.com/google/go-containerregistry/pkg/v1/mutate"
	"github.com/google/go-containerregistry/pkg/v1/tarball"
	"github.com/google/go-containerregistry/pkg/v1/types"
)

type tarEnt struct {
	name string
	body string
	typ  byte
	mode int64
	link string
}

func layerFromEntries(t *testing.T, ents []tarEnt, opts ...tarball.LayerOption) v1.Layer {
	t.Helper()
	var buf bytes.Buffer
	tw := tar.NewWriter(&buf)
	for _, e := range ents {
		typ := e.typ
		if typ == 0 {
			typ = tar.TypeReg
		}
		mode := e.mode
		if mode == 0 {
			if typ == tar.TypeDir {
				mode = 0o755
			} else {
				mode = 0o644
			}
		}
		hdr := &tar.Header{
			Name:     e.name,
			Mode:     mode,
			Size:     int64(len(e.body)),
			Typeflag: typ,
			Linkname: e.link,
		}
		if err := tw.WriteHeader(hdr); err != nil {
			t.Fatal(err)
		}
		if len(e.body) > 0 {
			if _, err := tw.Write([]byte(e.body)); err != nil {
				t.Fatal(err)
			}
		}
	}
	if err := tw.Close(); err != nil {
		t.Fatal(err)
	}
	b := buf.Bytes()
	layer, err := tarball.LayerFromOpener(func() (io.ReadCloser, error) {
		return io.NopCloser(bytes.NewReader(b)), nil
	}, opts...)
	if err != nil {
		t.Fatal(err)
	}
	return layer
}

func imageFromLayers(t *testing.T, layers ...v1.Layer) v1.Image {
	t.Helper()
	img, err := mutate.AppendLayers(empty.Image, layers...)
	if err != nil {
		t.Fatal(err)
	}
	return img
}

func withConfig(t *testing.T, img v1.Image, entrypoint, cmd, env []string, wd string) v1.Image {
	t.Helper()
	cfg, err := img.ConfigFile()
	if err != nil {
		t.Fatal(err)
	}
	cfg.Config.Entrypoint = entrypoint
	cfg.Config.Cmd = cmd
	cfg.Config.Env = env
	cfg.Config.WorkingDir = wd
	out, err := mutate.ConfigFile(img, cfg)
	if err != nil {
		t.Fatal(err)
	}
	return out
}

func TestUnpackWhiteouts(t *testing.T) {
	t.Parallel()
	base := layerFromEntries(t, []tarEnt{
		{name: "a.txt", body: "A"},
		{name: "b.txt", body: "B"},
		{name: "sub/", typ: tar.TypeDir, mode: 0o755},
		{name: "sub/c.txt", body: "C"},
		{name: "sub/keep.txt", body: "old"},
	})
	upper := layerFromEntries(t, []tarEnt{
		{name: "sub/.wh..wh..opq"},
		{name: ".wh.b.txt"},
		{name: "sub/d.txt", body: "D"},
		{name: "e.txt", body: "E"},
	})
	img := imageFromLayers(t, base, upper)

	dir := t.TempDir()
	if err := Unpack(img, dir, 1<<20); err != nil {
		t.Fatal(err)
	}

	mustRead := func(rel, want string) {
		t.Helper()
		b, err := os.ReadFile(filepath.Join(dir, rel))
		if err != nil {
			t.Fatalf("read %s: %v", rel, err)
		}
		if string(b) != want {
			t.Fatalf("%s: got %q want %q", rel, b, want)
		}
	}
	mustRead("a.txt", "A")
	mustRead("e.txt", "E")
	mustRead("sub/d.txt", "D")
	if _, err := os.Stat(filepath.Join(dir, "b.txt")); !os.IsNotExist(err) {
		t.Fatalf("b.txt should be whiteout-removed, err=%v", err)
	}
	if _, err := os.Stat(filepath.Join(dir, "sub/c.txt")); !os.IsNotExist(err) {
		t.Fatalf("sub/c.txt should be opaque-removed, err=%v", err)
	}
	if _, err := os.Stat(filepath.Join(dir, "sub/keep.txt")); !os.IsNotExist(err) {
		t.Fatalf("sub/keep.txt should be opaque-removed, err=%v", err)
	}
	if _, err := os.Stat(filepath.Join(dir, ".wh.b.txt")); !os.IsNotExist(err) {
		t.Fatal("whiteout marker should not remain on disk")
	}
	if _, err := os.Stat(filepath.Join(dir, "sub/.wh..wh..opq")); !os.IsNotExist(err) {
		t.Fatal("opaque marker should not remain on disk")
	}
}

func TestUnpackRejectsWindowsImage(t *testing.T) {
	t.Parallel()
	layer := layerFromEntries(t, []tarEnt{{name: "Windows/System32/a", body: "x"}})
	img := imageFromLayers(t, layer)
	cfg, err := img.ConfigFile()
	if err != nil {
		t.Fatal(err)
	}
	cfg.OS = "windows"
	img, err = mutate.ConfigFile(img, cfg)
	if err != nil {
		t.Fatal(err)
	}
	err = Unpack(img, t.TempDir(), 1<<20)
	if err == nil || !strings.Contains(err.Error(), "windows") {
		t.Fatalf("expected windows error, got %v", err)
	}
}

func TestUnpackSkipsForeignLayers(t *testing.T) {
	t.Parallel()
	foreign := layerFromEntries(t, []tarEnt{{name: "secret.txt", body: "nope"}}, tarball.WithMediaType(types.DockerForeignLayer))
	linux := layerFromEntries(t, []tarEnt{{name: "ok.txt", body: "yes"}})
	img := imageFromLayers(t, foreign, linux)
	dir := t.TempDir()
	if err := Unpack(img, dir, 1<<20); err != nil {
		t.Fatal(err)
	}
	if _, err := os.Stat(filepath.Join(dir, "secret.txt")); !os.IsNotExist(err) {
		t.Fatal("foreign layer file should be skipped")
	}
	b, err := os.ReadFile(filepath.Join(dir, "ok.txt"))
	if err != nil || string(b) != "yes" {
		t.Fatalf("ok.txt: %q %v", b, err)
	}
}

func TestUnpackEnforcesSizeCap(t *testing.T) {
	t.Parallel()
	layer := layerFromEntries(t, []tarEnt{{name: "big.bin", body: strings.Repeat("x", 200)}})
	img := imageFromLayers(t, layer)
	err := Unpack(img, t.TempDir(), 50)
	if err == nil || !strings.Contains(err.Error(), "byte limit") {
		t.Fatalf("expected size cap error, got %v", err)
	}
}

func TestUnpackRejectsPathEscape(t *testing.T) {
	t.Parallel()
	layer := layerFromEntries(t, []tarEnt{{name: "../escape.txt", body: "x"}})
	img := imageFromLayers(t, layer)
	err := Unpack(img, t.TempDir(), 1<<20)
	if err == nil || !strings.Contains(err.Error(), "unsafe") {
		t.Fatalf("expected unsafe path error, got %v", err)
	}
}

func TestUnpackSymlink(t *testing.T) {
	t.Parallel()
	layer := layerFromEntries(t, []tarEnt{
		{name: "target.txt", body: "data"},
		{name: "link.txt", typ: tar.TypeSymlink, link: "target.txt"},
	})
	img := imageFromLayers(t, layer)
	dir := t.TempDir()
	if err := Unpack(img, dir, 1<<20); err != nil {
		t.Fatal(err)
	}
	b, err := os.ReadFile(filepath.Join(dir, "link.txt"))
	if err != nil || string(b) != "data" {
		t.Fatalf("symlink: %q %v", b, err)
	}
}

func TestUnpackRejectsWriteThroughEscapingSymlink(t *testing.T) {
	t.Parallel()
	parent := t.TempDir()
	dest := filepath.Join(parent, "root")
	outside := filepath.Join(parent, "outside")
	if err := os.MkdirAll(outside, 0o755); err != nil {
		t.Fatal(err)
	}

	base := layerFromEntries(t, []tarEnt{
		{name: "escape", typ: tar.TypeSymlink, link: outside},
	})
	upper := layerFromEntries(t, []tarEnt{
		{name: "escape/owned", body: "host write"},
	})
	err := Unpack(imageFromLayers(t, base, upper), dest, 1<<20)
	if err == nil {
		t.Fatal("expected write through absolute symlink to fail")
	}
	if _, statErr := os.Stat(filepath.Join(outside, "owned")); !os.IsNotExist(statErr) {
		t.Fatalf("unpack escaped root: %v", statErr)
	}
}

func TestUnpackRejectsHardLinkEscape(t *testing.T) {
	t.Parallel()
	layer := layerFromEntries(t, []tarEnt{
		{name: "link", typ: tar.TypeLink, link: "../outside"},
	})
	err := Unpack(imageFromLayers(t, layer), t.TempDir(), 1<<20)
	if err == nil || !strings.Contains(err.Error(), "unsafe") {
		t.Fatalf("expected unsafe hard-link error, got %v", err)
	}
}

func TestUnpackWhiteoutCannotTraverseSymlink(t *testing.T) {
	t.Parallel()
	parent := t.TempDir()
	dest := filepath.Join(parent, "root")
	outside := filepath.Join(parent, "outside")
	if err := os.MkdirAll(outside, 0o755); err != nil {
		t.Fatal(err)
	}
	sentinel := filepath.Join(outside, "keep")
	if err := os.WriteFile(sentinel, []byte("safe"), 0o644); err != nil {
		t.Fatal(err)
	}

	base := layerFromEntries(t, []tarEnt{
		{name: "escape", typ: tar.TypeSymlink, link: outside},
	})
	upper := layerFromEntries(t, []tarEnt{
		{name: "escape/.wh.keep"},
	})
	err := Unpack(imageFromLayers(t, base, upper), dest, 1<<20)
	if err == nil {
		t.Fatal("expected whiteout through absolute symlink to fail")
	}
	got, readErr := os.ReadFile(sentinel)
	if readErr != nil || string(got) != "safe" {
		t.Fatalf("outside file changed: %q, %v", got, readErr)
	}
}

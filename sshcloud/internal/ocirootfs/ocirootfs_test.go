package ocirootfs

import (
	"archive/tar"
	"context"
	"fmt"
	"io"
	"log"
	"net/http/httptest"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"

	"github.com/google/go-containerregistry/pkg/name"
	"github.com/google/go-containerregistry/pkg/registry"
	"github.com/google/go-containerregistry/pkg/v1/remote"
)

func TestMaterializeRejectsUnpinned(t *testing.T) {
	t.Parallel()
	dir := t.TempDir()
	_, err := Materialize(context.Background(), "ghcr.io/me/app:latest", Options{CacheDir: dir})
	if err == nil || !strings.Contains(err.Error(), "digest-pinned") {
		t.Fatalf("got %v", err)
	}
}

func TestMaterializeCacheHitSkipsPull(t *testing.T) {
	t.Parallel()
	dir := t.TempDir()
	hex := "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"
	cached := filepath.Join(dir, hex+".ext4")
	if err := os.WriteFile(cached, []byte("cached-ext4"), 0o644); err != nil {
		t.Fatal(err)
	}
	ref := "example.invalid/me/app@sha256:" + hex
	path, err := Materialize(context.Background(), ref, Options{CacheDir: dir})
	if err != nil {
		t.Fatal(err)
	}
	if path != cached {
		t.Fatalf("path %s want %s", path, cached)
	}
	b, err := os.ReadFile(path)
	if err != nil || string(b) != "cached-ext4" {
		t.Fatalf("cache contents: %q %v", b, err)
	}
}

func TestMaterializeFromLocalRegistry(t *testing.T) {
	if _, err := exec.LookPath("mkfs.ext4"); err != nil {
		t.Skip("mkfs.ext4 not available")
	}
	if _, err := exec.LookPath("debugfs"); err != nil {
		t.Skip("debugfs not available")
	}

	img := imageFromLayers(t,
		layerFromEntries(t, []tarEnt{
			{name: "app/", typ: tar.TypeDir, mode: 0o755},
			{name: "app/bin", body: "#!/bin/sh\necho hi\n", mode: 0o755},
			{name: "gone.txt", body: "bye"},
		}),
		layerFromEntries(t, []tarEnt{
			{name: ".wh.gone.txt"},
			{name: "hello.txt", body: "world\n"},
		}),
	)

	srv := httptest.NewServer(registry.New(registry.Logger(log.New(io.Discard, "", 0))))
	t.Cleanup(srv.Close)
	host := strings.TrimPrefix(srv.URL, "http://")
	tag, err := name.NewTag(host+"/sshcloud/demo:test", name.WeakValidation)
	if err != nil {
		t.Fatal(err)
	}
	if err := remote.Write(tag, img); err != nil {
		t.Fatal(err)
	}
	digest, err := img.Digest()
	if err != nil {
		t.Fatal(err)
	}
	ref := fmt.Sprintf("%s/sshcloud/demo@%s", host, digest.String())

	cache := t.TempDir()
	path, err := Materialize(context.Background(), ref, Options{CacheDir: cache, SizeMB: 8})
	if err != nil {
		t.Fatal(err)
	}
	if _, err := os.Stat(path); err != nil {
		t.Fatal(err)
	}

	out, err := exec.Command("debugfs", "-R", "ls -l", path).CombinedOutput()
	if err != nil {
		t.Fatal(err, string(out))
	}
	listing := string(out)
	if !strings.Contains(listing, "hello.txt") || !strings.Contains(listing, "app") {
		t.Fatalf("listing missing files:\n%s", listing)
	}
	if strings.Contains(listing, "gone.txt") {
		t.Fatalf("whiteout file still present:\n%s", listing)
	}

	again, err := Materialize(context.Background(), ref, Options{CacheDir: cache, SizeMB: 8})
	if err != nil {
		t.Fatal(err)
	}
	if again != path {
		t.Fatalf("cache miss: %s vs %s", again, path)
	}
}

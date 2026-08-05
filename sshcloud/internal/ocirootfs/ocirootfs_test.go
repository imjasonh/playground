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
	v1 "github.com/google/go-containerregistry/pkg/v1"
	"github.com/google/go-containerregistry/pkg/v1/mutate"
	"github.com/google/go-containerregistry/pkg/v1/remote"

	"github.com/imjasonh/playground/sshcloud/internal/guestinit"
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
	spec := guestinit.Spec{Entrypoint: []string{"/app"}, Cmd: []string{"--ssh"}, WorkingDir: "/app", Env: []string{"FOO=1"}}
	if err := guestinit.WriteFile(filepath.Join(dir, hex+".boot.json"), spec); err != nil {
		t.Fatal(err)
	}
	ref := "example.invalid/me/app@sha256:" + hex
	res, err := Materialize(context.Background(), ref, Options{CacheDir: dir})
	if err != nil {
		t.Fatal(err)
	}
	if res.Rootfs != cached {
		t.Fatalf("path %s want %s", res.Rootfs, cached)
	}
	if strings.Join(guestinit.Argv(res.Spec), " ") != "/app --ssh" || res.Spec.WorkingDir != "/app" {
		t.Fatalf("spec %+v", res.Spec)
	}
	b, err := os.ReadFile(res.Rootfs)
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
	img = withConfig(t, img, []string{"/app/bin"}, []string{"--ssh"}, []string{"PATH=/bin", "FOO=bar"}, "/app")

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
	res, err := Materialize(context.Background(), ref, Options{CacheDir: cache, SizeMB: 64})
	if err != nil {
		t.Fatal(err)
	}
	if _, err := os.Stat(res.Rootfs); err != nil {
		t.Fatal(err)
	}
	if strings.Join(guestinit.Argv(res.Spec), " ") != "/app/bin --ssh" {
		t.Fatalf("spec argv %+v", res.Spec)
	}
	if res.Spec.WorkingDir != "/app" || strings.Join(res.Spec.Env, ",") != "PATH=/bin,FOO=bar" {
		t.Fatalf("spec %+v", res.Spec)
	}

	out, err := exec.Command("debugfs", "-R", "ls -l", res.Rootfs).CombinedOutput()
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

	again, err := Materialize(context.Background(), ref, Options{CacheDir: cache, SizeMB: 64})
	if err != nil {
		t.Fatal(err)
	}
	if again.Rootfs != res.Rootfs {
		t.Fatalf("cache miss: %s vs %s", again.Rootfs, res.Rootfs)
	}
	if strings.Join(guestinit.Argv(again.Spec), " ") != "/app/bin --ssh" {
		t.Fatalf("cached spec %+v", again.Spec)
	}
}

func TestSpecRejectsUnsupportedRuntimeContract(t *testing.T) {
	t.Parallel()
	base := withConfig(t, imageFromLayers(t, layerFromEntries(t, []tarEnt{{name: "app", body: "x"}})), []string{"/app"}, nil, nil, "/")
	tests := []struct {
		name   string
		mutate func(*v1.ConfigFile)
		want   string
	}{
		{name: "user", mutate: func(cfg *v1.ConfigFile) { cfg.Config.User = "65532" }, want: "User"},
		{name: "volumes", mutate: func(cfg *v1.ConfigFile) {
			cfg.Config.Volumes = map[string]struct{}{"/data": {}}
		}, want: "volumes"},
		{name: "architecture", mutate: func(cfg *v1.ConfigFile) { cfg.Architecture = "arm64" }, want: "architecture"},
	}
	for _, tc := range tests {
		t.Run(tc.name, func(t *testing.T) {
			cfg, err := base.ConfigFile()
			if err != nil {
				t.Fatal(err)
			}
			tc.mutate(cfg)
			image, err := mutate.ConfigFile(base, cfg)
			if err != nil {
				t.Fatal(err)
			}
			if _, err := specFromImage(image); err == nil || !strings.Contains(err.Error(), tc.want) {
				t.Fatalf("error %v, want %q", err, tc.want)
			}
		})
	}
}

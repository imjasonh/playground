// Package apppack builds minimal OCI images from a linux binary for tests and demos.
package apppack

import (
	"archive/tar"
	"bytes"
	"fmt"
	"io"
	"os"
	"path"
	"strings"

	"github.com/google/go-containerregistry/pkg/name"
	v1 "github.com/google/go-containerregistry/pkg/v1"
	"github.com/google/go-containerregistry/pkg/v1/empty"
	"github.com/google/go-containerregistry/pkg/v1/mutate"
	"github.com/google/go-containerregistry/pkg/v1/remote"
	"github.com/google/go-containerregistry/pkg/v1/tarball"
)

// Spec describes a single-binary OCI image.
type Spec struct {
	// Binary is a host path to a linux/amd64 executable.
	Binary string
	// GuestPath is where the binary lands in the image (default /app).
	GuestPath string
	// Entrypoint defaults to []string{GuestPath}.
	Entrypoint []string
	// Cmd is appended after Entrypoint (OCI semantics).
	Cmd []string
	// Env defaults to a minimal PATH.
	Env []string
	// WorkingDir defaults to "/".
	WorkingDir string
}

// Build creates a linux/amd64 image containing Binary.
func Build(s Spec) (v1.Image, error) {
	if strings.TrimSpace(s.Binary) == "" {
		return nil, fmt.Errorf("Binary required")
	}
	body, err := os.ReadFile(s.Binary)
	if err != nil {
		return nil, err
	}
	guest := s.GuestPath
	if guest == "" {
		guest = "/app"
	}
	guest = path.Clean("/" + strings.TrimPrefix(guest, "/"))
	entrypoint := s.Entrypoint
	if len(entrypoint) == 0 {
		entrypoint = []string{guest}
	}
	env := s.Env
	if len(env) == 0 {
		env = []string{"PATH=/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin"}
	}
	wd := s.WorkingDir
	if wd == "" {
		wd = "/"
	}

	layer, err := layerWithFile(guest, body, 0o755)
	if err != nil {
		return nil, err
	}
	img, err := mutate.AppendLayers(empty.Image, layer)
	if err != nil {
		return nil, err
	}
	cfg, err := img.ConfigFile()
	if err != nil {
		return nil, err
	}
	cfg.Architecture = "amd64"
	cfg.OS = "linux"
	cfg.Config.Entrypoint = entrypoint
	cfg.Config.Cmd = s.Cmd
	cfg.Config.Env = env
	cfg.Config.WorkingDir = wd
	return mutate.ConfigFile(img, cfg)
}

// Push writes img to repo (tag or registry host/path) and returns a digest-pinned ref.
func Push(img v1.Image, repo string) (string, error) {
	tag, err := name.NewTag(repo, name.WeakValidation)
	if err != nil {
		return "", err
	}
	if err := remote.Write(tag, img); err != nil {
		return "", err
	}
	digest, err := img.Digest()
	if err != nil {
		return "", err
	}
	return fmt.Sprintf("%s@%s", tag.Context().Name(), digest.String()), nil
}

func layerWithFile(guestPath string, body []byte, mode int64) (v1.Layer, error) {
	var buf bytes.Buffer
	tw := tar.NewWriter(&buf)
	var dirs []string
	dir := path.Dir(guestPath)
	for dir != "/" && dir != "." {
		dirs = append(dirs, dir)
		dir = path.Dir(dir)
	}
	for i := len(dirs) - 1; i >= 0; i-- {
		hdr := &tar.Header{Name: strings.TrimPrefix(dirs[i], "/") + "/", Mode: 0o755, Typeflag: tar.TypeDir}
		if err := tw.WriteHeader(hdr); err != nil {
			return nil, err
		}
	}
	name := strings.TrimPrefix(guestPath, "/")
	hdr := &tar.Header{
		Name:     name,
		Mode:     mode,
		Size:     int64(len(body)),
		Typeflag: tar.TypeReg,
	}
	if err := tw.WriteHeader(hdr); err != nil {
		return nil, err
	}
	if _, err := tw.Write(body); err != nil {
		return nil, err
	}
	if err := tw.Close(); err != nil {
		return nil, err
	}
	b := buf.Bytes()
	return tarball.LayerFromOpener(func() (io.ReadCloser, error) {
		return io.NopCloser(bytes.NewReader(b)), nil
	})
}

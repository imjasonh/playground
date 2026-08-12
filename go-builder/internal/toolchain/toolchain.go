// Package toolchain downloads and caches a Go SDK for the buildpack build image.
package toolchain

import (
	"archive/tar"
	"compress/gzip"
	"fmt"
	"io"
	"net/http"
	"os"
	"path/filepath"
	"runtime"
	"strings"
)

const defaultVersion = "1.25.0"

// GoModHints are version fields parsed from go.mod.
type GoModHints struct {
	Go        string // e.g. "1.25.0" or "1.25"
	Toolchain string // e.g. "go1.25.0"
}

// ParseGoMod reads go and toolchain lines from go.mod (best-effort, no go command).
func ParseGoMod(appDir string) (GoModHints, error) {
	b, err := os.ReadFile(filepath.Join(appDir, "go.mod"))
	if err != nil {
		return GoModHints{}, err
	}
	var h GoModHints
	for _, line := range strings.Split(string(b), "\n") {
		line = strings.TrimSpace(line)
		if strings.HasPrefix(line, "go ") {
			h.Go = strings.TrimSpace(strings.TrimPrefix(line, "go "))
		}
		if strings.HasPrefix(line, "toolchain ") {
			h.Toolchain = strings.TrimSpace(strings.TrimPrefix(line, "toolchain "))
		}
	}
	return h, nil
}

// ResolveVersion picks the SDK version to install.
func ResolveVersion(h GoModHints, defaultVer string) string {
	if defaultVer == "" {
		defaultVer = defaultVersion
	}
	if h.Toolchain != "" {
		v := strings.TrimPrefix(h.Toolchain, "go")
		if v != "" && !strings.Contains(v, "local") {
			return normalizeVersion(v)
		}
	}
	if h.Go != "" {
		return normalizeVersion(h.Go)
	}
	return normalizeVersion(defaultVer)
}

func normalizeVersion(v string) string {
	v = strings.TrimPrefix(v, "go")
	// "1.25" → "1.25.0" for the release tarball name when patch is missing.
	parts := strings.Split(v, ".")
	if len(parts) == 2 {
		return v + ".0"
	}
	return v
}

// Ensure installs Go into layerPath when needed and returns the path to the go binary.
// layerPath should be the CNB layer directory for "go".
func Ensure(layerPath, version, goos, goarch string, metadataPrev map[string]string) (goBin string, rebuilt bool, err error) {
	if goos == "" {
		goos = runtime.GOOS
	}
	if goarch == "" {
		goarch = runtime.GOARCH
	}
	goBin = filepath.Join(layerPath, "go", "bin", "go")
	wantURL := downloadURL(version, goos, goarch)

	if metadataPrev["version"] == version && metadataPrev["url"] == wantURL {
		if _, err := os.Stat(goBin); err == nil {
			return goBin, false, nil
		}
	}

	if err := os.RemoveAll(layerPath); err != nil {
		return "", false, err
	}
	if err := os.MkdirAll(layerPath, 0o755); err != nil {
		return "", false, err
	}
	if err := downloadAndExtract(wantURL, layerPath); err != nil {
		return "", false, fmt.Errorf("install go %s: %w", version, err)
	}
	if _, err := os.Stat(goBin); err != nil {
		return "", false, fmt.Errorf("go binary missing after install: %w", err)
	}
	return goBin, true, nil
}

func downloadURL(version, goos, goarch string) string {
	return fmt.Sprintf("https://go.dev/dl/go%s.%s-%s.tar.gz", version, goos, goarch)
}

func downloadAndExtract(url, dest string) error {
	resp, err := http.Get(url) //nolint:gosec // URL is constructed from version/os/arch only
	if err != nil {
		return err
	}
	defer resp.Body.Close()
	if resp.StatusCode != http.StatusOK {
		return fmt.Errorf("GET %s: %s", url, resp.Status)
	}
	gz, err := gzip.NewReader(resp.Body)
	if err != nil {
		return err
	}
	defer gz.Close()
	tr := tar.NewReader(gz)
	for {
		hdr, err := tr.Next()
		if err == io.EOF {
			break
		}
		if err != nil {
			return err
		}
		// tarball roots at "go/..."
		target := filepath.Join(dest, hdr.Name)
		if !strings.HasPrefix(filepath.Clean(target), filepath.Clean(dest)+string(os.PathSeparator)) &&
			filepath.Clean(target) != filepath.Clean(dest) {
			return fmt.Errorf("tar path escapes dest: %s", hdr.Name)
		}
		switch hdr.Typeflag {
		case tar.TypeDir:
			if err := os.MkdirAll(target, 0o755); err != nil {
				return err
			}
		case tar.TypeReg:
			if err := os.MkdirAll(filepath.Dir(target), 0o755); err != nil {
				return err
			}
			f, err := os.OpenFile(target, os.O_CREATE|os.O_TRUNC|os.O_WRONLY, os.FileMode(hdr.Mode))
			if err != nil {
				return err
			}
			if _, err := io.Copy(f, tr); err != nil {
				f.Close()
				return err
			}
			if err := f.Close(); err != nil {
				return err
			}
		}
	}
	return nil
}

// Metadata for the go layer.toml.
func Metadata(version, goos, goarch string) map[string]string {
	return map[string]string{
		"version": version,
		"url":     downloadURL(version, goos, goarch),
	}
}

package honk

import (
	"archive/tar"
	"bytes"
	"compress/gzip"
	"context"
	"crypto/sha256"
	"encoding/hex"
	"errors"
	"fmt"
	"io"
	"net/http"
	"os"
	"path/filepath"
	"runtime"
	"sync"
	"time"
)

// extensionRelease is the Honker SQLite extension build this server loads.
// The sums are the release's SHA256SUMS. A changed file must not load.
const extensionRelease = "ext-v0.5.0"

type extensionAsset struct {
	name string
	sum  string
	file string
}

func extensionForHost() (extensionAsset, error) {
	switch runtime.GOOS + "/" + runtime.GOARCH {
	case "linux/amd64":
		return extensionAsset{"honker-ext-linux-x64.tar.gz", "4275604003e6c450277d9036b854af198462dfb0212ec6f0a0e72aeaf02e5507", "libhonker_ext.so"}, nil
	case "linux/arm64":
		return extensionAsset{"honker-ext-linux-arm64.tar.gz", "36c73bb4e720b967a2711e28feb2bfeff34f97c2b992ec620dd29e0b61eed990", "libhonker_ext.so"}, nil
	case "darwin/amd64":
		return extensionAsset{"honker-ext-macos-x64.tar.gz", "8df907f211bf4d011a5ce9f094ad196e44fb70a761c9bf49d5bf622442a3a435", "libhonker_ext.dylib"}, nil
	case "darwin/arm64":
		return extensionAsset{"honker-ext-macos-arm64.tar.gz", "aa19b5287e016d031f48b611261b47118c7b4e88f2d8bcd12db1d1a5481285da", "libhonker_ext.dylib"}, nil
	case "windows/amd64":
		return extensionAsset{"honker-ext-windows-x64.tar.gz", "4d4cd6918325ee9db79471e46dffefd2d054e4de7a3222b25fd3662cb346327c", "honker_ext.dll"}, nil
	default:
		return extensionAsset{}, fmt.Errorf("no Honker extension build for %s/%s", runtime.GOOS, runtime.GOARCH)
	}
}

var extensionOnce sync.Mutex

// Extension returns the path of the Honker SQLite extension. explicit is
// used as-is when it is set. Otherwise Extension downloads the pinned
// release, checks its SHA-256, and caches the library. fallbackDir is used
// when the user cache directory is not writable.
func Extension(ctx context.Context, explicit, fallbackDir string) (string, error) {
	if explicit != "" {
		st, err := os.Stat(explicit)
		if err != nil {
			return "", err
		}
		if st.IsDir() {
			return "", fmt.Errorf("%s is a directory", explicit)
		}
		return explicit, nil
	}
	asset, err := extensionForHost()
	if err != nil {
		return "", err
	}
	dir, err := extensionCacheDir(fallbackDir)
	if err != nil {
		return "", err
	}
	dest := filepath.Join(dir, asset.file)

	extensionOnce.Lock()
	defer extensionOnce.Unlock()
	if st, err := os.Stat(dest); err == nil && st.Size() > 100_000 && st.Mode().IsRegular() {
		return dest, nil
	}
	if err := downloadExtension(ctx, asset, dest); err != nil {
		return "", err
	}
	return dest, nil
}

func extensionCacheDir(fallback string) (string, error) {
	var dirs []string
	if base, err := os.UserCacheDir(); err == nil {
		dirs = append(dirs, filepath.Join(base, "cloudrun-sqlite", "honker-"+extensionRelease))
	}
	if fallback != "" {
		dirs = append(dirs, filepath.Join(fallback, "honker-ext"))
	}
	var last error
	for _, dir := range dirs {
		if err := os.MkdirAll(dir, 0o755); err != nil {
			last = err
			continue
		}
		f, err := os.CreateTemp(dir, ".write-*")
		if err != nil {
			last = err
			continue
		}
		name := f.Name()
		f.Close()
		os.Remove(name)
		return dir, nil
	}
	if last == nil {
		last = errors.New("no writable directory for the Honker extension")
	}
	return "", last
}

func downloadExtension(ctx context.Context, asset extensionAsset, dest string) error {
	ctx, cancel := context.WithTimeout(ctx, time.Minute)
	defer cancel()
	url := "https://github.com/russellromney/honker/releases/download/" + extensionRelease + "/" + asset.name
	req, err := http.NewRequestWithContext(ctx, http.MethodGet, url, nil)
	if err != nil {
		return err
	}
	req.Header.Set("User-Agent", "cloudrun-sqlite")
	res, err := http.DefaultClient.Do(req)
	if err != nil {
		return fmt.Errorf("download %s: %w", url, err)
	}
	defer res.Body.Close()
	if res.StatusCode != http.StatusOK {
		return fmt.Errorf("download %s: %s", url, res.Status)
	}
	body, err := io.ReadAll(io.LimitReader(res.Body, 8<<20))
	if err != nil {
		return fmt.Errorf("download %s: %w", url, err)
	}
	sum := sha256.Sum256(body)
	got := hex.EncodeToString(sum[:])
	if got != asset.sum {
		return fmt.Errorf("download %s: sha256 %s, want %s", asset.name, got, asset.sum)
	}
	zr, err := gzip.NewReader(bytes.NewReader(body))
	if err != nil {
		return err
	}
	defer zr.Close()
	return extractLibrary(tar.NewReader(zr), asset.file, dest)
}

func extractLibrary(tr *tar.Reader, name, dest string) error {
	for {
		hdr, err := tr.Next()
		if errors.Is(err, io.EOF) {
			return fmt.Errorf("archive has no %s", name)
		}
		if err != nil {
			return err
		}
		if filepath.Base(hdr.Name) != name || hdr.Typeflag != tar.TypeReg {
			continue
		}
		tmp, err := os.CreateTemp(filepath.Dir(dest), ".partial-*")
		if err != nil {
			return err
		}
		tmpName := tmp.Name()
		if err := tmp.Chmod(0o755); err != nil {
			tmp.Close()
			os.Remove(tmpName)
			return err
		}
		_, copyErr := io.Copy(tmp, io.LimitReader(tr, 8<<20))
		closeErr := tmp.Close()
		if copyErr != nil {
			os.Remove(tmpName)
			return copyErr
		}
		if closeErr != nil {
			os.Remove(tmpName)
			return closeErr
		}
		if err := os.Rename(tmpName, dest); err != nil {
			os.Remove(tmpName)
			return err
		}
		return nil
	}
}

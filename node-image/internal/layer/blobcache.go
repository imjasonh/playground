package layer

import (
	"crypto/sha256"
	"encoding/hex"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"strings"
	"sync"
)

// BlobCache stores compressed OCI layer blobs under Dir (typically
// ~/.cache/node-image/layers), keyed by uncompressed DiffID so rebuilds can
// skip recompression when the layer file set is unchanged.
type BlobCache struct {
	Dir string
}

// DefaultBlobCacheDir returns ~/.cache/node-image/layers.
func DefaultBlobCacheDir() (string, error) {
	home, err := os.UserHomeDir()
	if err != nil {
		return "", err
	}
	return filepath.Join(home, ".cache", "node-image", "layers"), nil
}

// EnsureCompressed returns a path to the gzip-compressed tar for files.
// On cache miss it streams WriteCompressed once, teeing into the cache file
// (keyed by DiffID). On hit it returns the existing blob without recompressing.
func (c *BlobCache) EnsureCompressed(files []File) (digest string, size int64, path string, err error) {
	if c == nil || c.Dir == "" {
		return "", 0, "", fmt.Errorf("BlobCache: Dir required")
	}
	if err := os.MkdirAll(c.Dir, 0o700); err != nil {
		return "", 0, "", err
	}
	diffID, err := DiffID(files)
	if err != nil {
		return "", 0, "", err
	}
	key := strings.TrimPrefix(diffID, "sha256:")
	final := filepath.Join(c.Dir, key+".tar.gz")
	meta := filepath.Join(c.Dir, key+".sha256")
	if st, statErr := os.Stat(final); statErr == nil && st.Size() > 0 {
		// Always re-hash the cached blob; do not trust the sidecar alone.
		sum, sz, herr := hashFile(final)
		if herr == nil && sz == st.Size() {
			_ = os.WriteFile(meta, []byte(sum+"\n"), 0o600)
			return sum, sz, final, nil
		}
		// Corrupt cache entry — fall through and rebuild.
		_ = os.Remove(final)
		_ = os.Remove(meta)
	}

	tmp, err := os.CreateTemp(c.Dir, "layer-*.tmp")
	if err != nil {
		return "", 0, "", err
	}
	tmpPath := tmp.Name()
	h := sha256.New()
	cw := &countingWriter{w: io.MultiWriter(tmp, h)}
	if err = WriteCompressed(cw, files); err != nil {
		_ = tmp.Close()
		_ = os.Remove(tmpPath)
		return "", 0, "", err
	}
	if err = tmp.Close(); err != nil {
		_ = os.Remove(tmpPath)
		return "", 0, "", err
	}
	digest = "sha256:" + hex.EncodeToString(h.Sum(nil))
	size = cw.n
	_ = os.Remove(final)
	if err = os.Rename(tmpPath, final); err != nil {
		_ = os.Remove(tmpPath)
		return "", 0, "", err
	}
	_ = os.WriteFile(meta, []byte(digest+"\n"), 0o600)
	return digest, size, final, nil
}

func hashFile(path string) (digest string, size int64, err error) {
	f, err := os.Open(path)
	if err != nil {
		return "", 0, err
	}
	defer f.Close()
	h := sha256.New()
	n, err := io.Copy(h, f)
	if err != nil {
		return "", 0, err
	}
	return "sha256:" + hex.EncodeToString(h.Sum(nil)), n, nil
}

// CachedOpener returns an opener that compresses files at most once (teeing
// into the blob cache) and reopens the cached blob on every call. Safe for
// go-containerregistry's LayerFromOpener, which may invoke the opener many times.
func (c *BlobCache) CachedOpener(files []File) func() (io.ReadCloser, error) {
	var (
		once sync.Once
		path string
		err  error
	)
	return func() (io.ReadCloser, error) {
		once.Do(func() {
			_, _, path, err = c.EnsureCompressed(files)
		})
		if err != nil {
			return nil, err
		}
		return os.Open(path)
	}
}

package layer

import (
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"strings"
	"sync"
)

// BlobCache stores compressed OCI layer blobs under Dir (typically
// ~/.cache/node-image/layers). Entries are keyed by a cheap content
// Fingerprint (metadata only) so warm rebuilds avoid DiffID and recompression.
type BlobCache struct {
	Dir string
}

// CachedBlob is a compressed layer blob with known digests (no rehash needed).
type CachedBlob struct {
	// DiffID is the sha256 of the uncompressed tar (OCI diff_id).
	DiffID string
	// Digest is the sha256 of the compressed blob.
	Digest string
	// Size is the compressed byte length.
	Size int64
	// Path is the absolute path to the .tar.gz on disk.
	Path string
}

type blobMeta struct {
	Fingerprint string `json:"fingerprint"`
	DiffID      string `json:"diffID"`
	Digest      string `json:"digest"`
	Size        int64  `json:"size"`
}

// DefaultBlobCacheDir returns ~/.cache/node-image/layers.
func DefaultBlobCacheDir() (string, error) {
	home, err := os.UserHomeDir()
	if err != nil {
		return "", err
	}
	return filepath.Join(home, ".cache", "node-image", "layers"), nil
}

// Fingerprint returns a cheap content identity for a file list without reading
// file bodies. Used as the blob-cache lookup key so warm hits skip DiffID.
func Fingerprint(files []File) (string, error) {
	sorted := append([]File(nil), files...)
	sortFiles(sorted)
	h := sha256.New()
	for _, f := range sorted {
		_, _ = fmt.Fprintf(h, "%s\n%x\n%s\n", f.Rel, f.Mode, f.Link)
		switch {
		case f.Mode&os.ModeSymlink != 0 || f.Mode.IsDir():
			// metadata only
		case f.DiskPath != "":
			st, err := os.Stat(f.DiskPath)
			if err != nil {
				return "", err
			}
			_, _ = fmt.Fprintf(h, "disk:%d:%d\n", st.Size(), st.ModTime().UnixNano())
		case f.Opener != nil:
			_, _ = fmt.Fprintf(h, "opener:%d\n", f.Size)
		default:
			sum := sha256.Sum256(f.Body)
			_, _ = fmt.Fprintf(h, "body:%x\n", sum)
		}
	}
	return hex.EncodeToString(h.Sum(nil)), nil
}

// EnsureCompressed returns a CachedBlob for files.
// On cache hit (fingerprint match + size + sidecar digests), returns immediately
// without DiffID or rehashing the .tar.gz.
// On miss: computes DiffID, compresses once, writes sidecars.
func (c *BlobCache) EnsureCompressed(files []File) (digest string, size int64, path string, err error) {
	blob, err := c.Ensure(files)
	if err != nil {
		return "", 0, "", err
	}
	return blob.Digest, blob.Size, blob.Path, nil
}

// Ensure is like EnsureCompressed but returns full CachedBlob metadata
// (DiffID + Digest + Size + Path) for constructing a v1.Layer without rehash.
func (c *BlobCache) Ensure(files []File) (*CachedBlob, error) {
	if c == nil || c.Dir == "" {
		return nil, fmt.Errorf("BlobCache: Dir required")
	}
	if err := os.MkdirAll(c.Dir, 0o700); err != nil {
		return nil, err
	}
	fp, err := Fingerprint(files)
	if err != nil {
		return nil, err
	}
	final := filepath.Join(c.Dir, fp+".tar.gz")
	metaPath := filepath.Join(c.Dir, fp+".json")

	if blob, ok := c.hit(final, metaPath, fp); ok {
		return blob, nil
	}

	diffID, err := DiffID(files)
	if err != nil {
		return nil, err
	}
	tmp, err := os.CreateTemp(c.Dir, "layer-*.tmp")
	if err != nil {
		return nil, err
	}
	tmpPath := tmp.Name()
	h := sha256.New()
	cw := &countingWriter{w: io.MultiWriter(tmp, h)}
	if err = WriteCompressed(cw, files); err != nil {
		_ = tmp.Close()
		_ = os.Remove(tmpPath)
		return nil, err
	}
	if err = tmp.Close(); err != nil {
		_ = os.Remove(tmpPath)
		return nil, err
	}
	digest := "sha256:" + hex.EncodeToString(h.Sum(nil))
	size := cw.n
	_ = os.Remove(final)
	if err = os.Rename(tmpPath, final); err != nil {
		_ = os.Remove(tmpPath)
		return nil, err
	}
	meta := blobMeta{
		Fingerprint: fp,
		DiffID:      diffID,
		Digest:      digest,
		Size:        size,
	}
	if err := writeBlobMeta(metaPath, meta); err != nil {
		return nil, err
	}
	// Legacy DiffID-keyed symlink for older caches (best-effort).
	_ = os.Symlink(filepath.Base(final), filepath.Join(c.Dir, strings.TrimPrefix(diffID, "sha256:")+".tar.gz"))
	return &CachedBlob{DiffID: diffID, Digest: digest, Size: size, Path: final}, nil
}

func (c *BlobCache) hit(final, metaPath, fp string) (*CachedBlob, bool) {
	st, err := os.Stat(final)
	if err != nil || st.Size() == 0 {
		return nil, false
	}
	meta, err := readBlobMeta(metaPath)
	if err != nil {
		return nil, false
	}
	if meta.Fingerprint != fp || meta.DiffID == "" || meta.Digest == "" {
		return nil, false
	}
	if meta.Size != 0 && meta.Size != st.Size() {
		return nil, false
	}
	if meta.Size == 0 {
		meta.Size = st.Size()
	}
	return &CachedBlob{
		DiffID: meta.DiffID,
		Digest: meta.Digest,
		Size:   meta.Size,
		Path:   final,
	}, true
}

func writeBlobMeta(path string, m blobMeta) error {
	b, err := json.Marshal(m)
	if err != nil {
		return err
	}
	return os.WriteFile(path, append(b, '\n'), 0o600)
}

func readBlobMeta(path string) (blobMeta, error) {
	b, err := os.ReadFile(path)
	if err != nil {
		return blobMeta{}, err
	}
	// Support legacy single-line "sha256:…" digest sidecar.
	line := strings.TrimSpace(string(b))
	if strings.HasPrefix(line, "sha256:") && !strings.HasPrefix(line, "{") {
		return blobMeta{}, fmt.Errorf("legacy sidecar")
	}
	var m blobMeta
	if err := json.Unmarshal(b, &m); err != nil {
		return blobMeta{}, err
	}
	return m, nil
}

// CachedOpener returns an opener that compresses files at most once.
// Prefer LayerFromCachedBlob / Ensure for warm builds that skip DiffID rehash.
func (c *BlobCache) CachedOpener(files []File) func() (io.ReadCloser, error) {
	var (
		once sync.Once
		path string
		err  error
	)
	return func() (io.ReadCloser, error) {
		once.Do(func() {
			var blob *CachedBlob
			blob, err = c.Ensure(files)
			if blob != nil {
				path = blob.Path
			}
		})
		if err != nil {
			return nil, err
		}
		return os.Open(path)
	}
}

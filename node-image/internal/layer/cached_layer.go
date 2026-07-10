package layer

import (
	"io"
	"os"

	v1 "github.com/google/go-containerregistry/pkg/v1"
	"github.com/google/go-containerregistry/pkg/v1/types"
)

// cachedLayer is a v1.Layer backed by a precomputed CachedBlob.
// Digest/DiffID/Size are returned from sidecars — no gunzip or rehash on warm hits.
type cachedLayer struct {
	blob      *CachedBlob
	mediaType types.MediaType
}

// LayerFromCachedBlob returns a v1.Layer that opens the compressed blob and
// returns known DiffID/Digest/Size without recomputing them.
func LayerFromCachedBlob(blob *CachedBlob) (v1.Layer, error) {
	if blob == nil || blob.Path == "" || blob.Digest == "" || blob.DiffID == "" {
		return nil, io.ErrUnexpectedEOF
	}
	return &cachedLayer{blob: blob, mediaType: types.OCILayer}, nil
}

func (l *cachedLayer) Digest() (v1.Hash, error) {
	return v1.NewHash(l.blob.Digest)
}

func (l *cachedLayer) DiffID() (v1.Hash, error) {
	return v1.NewHash(l.blob.DiffID)
}

func (l *cachedLayer) Compressed() (io.ReadCloser, error) {
	return os.Open(l.blob.Path)
}

func (l *cachedLayer) Uncompressed() (io.ReadCloser, error) {
	rc, err := os.Open(l.blob.Path)
	if err != nil {
		return nil, err
	}
	return newGzipReader(rc), nil
}

func (l *cachedLayer) Size() (int64, error) {
	return l.blob.Size, nil
}

func (l *cachedLayer) MediaType() (types.MediaType, error) {
	return l.mediaType, nil
}

// gzipReader wraps a ReadCloser that is gzip-compressed; Uncompressed is rarely
// used on the push path (Digest/DiffID already known). Implemented lazily via
// compress/gzip in gzip_open.go to keep this file focused.

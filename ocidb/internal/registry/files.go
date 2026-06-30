package registry

// Layer filesystem access.
//
// This adapts the technique described in dagdotdev's registry explorer
// (https://github.com/jonjohnsonjr/dagdotdev/blob/main/pkg/explore/README.md):
// walk each layer's tar exactly once to build a *table of contents* (one entry
// per tar member), and lean on content-addressability to cache aggressively.
//
// A layer's bytes are immutable (it is named by digest), so both the raw blob
// and the derived TOC are cached forever. Listing files for an already-seen
// layer therefore costs zero network and zero decompression. The explorer goes
// one step further and serves individual files with HTTP Range requests over a
// gzip seek index; here we keep it simple for a local CLI by caching the whole
// layer blob on disk and reading file bodies out of that cache, which achieves
// the same "never re-fetch from the registry" goal.

import (
	"archive/tar"
	"bytes"
	"compress/gzip"
	"encoding/json"
	"fmt"
	"io"
	"os"
	"strings"
	"time"

	"github.com/google/go-containerregistry/pkg/name"
	"github.com/klauspost/compress/zstd"
)

// DefaultMaxFileSize bounds how many bytes of a single file are read into a
// SQLite value. Larger files report their size but yield NULL content.
const DefaultMaxFileSize = 1 << 20 // 1 MiB

// TarEntry is one member of a layer's tar stream (a file, directory, symlink,
// and so on). It is the unit stored in a layer's table of contents.
type TarEntry struct {
	Path     string    `json:"path"`
	Type     string    `json:"type"`
	Size     int64     `json:"size"`
	Mode     int64     `json:"mode"`
	Linkname string    `json:"linkname,omitempty"`
	UID      int       `json:"uid"`
	GID      int       `json:"gid"`
	ModTime  time.Time `json:"modTime"`
}

type tocEnvelope struct {
	Digest  string     `json:"digest"`
	Entries []TarEntry `json:"entries"`
}

// LayerTOC returns the table of contents for a layer blob, building it on first
// use and caching it permanently by digest. ref supplies the repository to pull
// the blob from; the layer is addressed by its (immutable) digest.
func (c *Client) LayerTOC(ref, layerDigest string) ([]TarEntry, error) {
	path := c.cachePath("toc", digestFile(layerDigest)+".json")
	if b, err := os.ReadFile(path); err == nil {
		var env tocEnvelope
		if json.Unmarshal(b, &env) == nil {
			c.hit()
			return env.Entries, nil
		}
	}

	repo, err := repoFromRef(ref)
	if err != nil {
		return nil, err
	}
	blob, err := c.Blob(repo, layerDigest)
	if err != nil {
		return nil, err
	}
	entries, err := walkTOC(blob)
	if err != nil {
		return nil, fmt.Errorf("read layer %s: %w", layerDigest, err)
	}
	_ = c.writeJSON(path, tocEnvelope{Digest: layerDigest, Entries: entries})
	return entries, nil
}

// ReadLayerFiles extracts regular-file contents from a layer. When want is nil
// every regular file is read; otherwise only files whose normalized path is a
// key in want are read. Files larger than maxSize (<=0 means DefaultMaxFileSize)
// are skipped and simply absent from the result. The layer blob is served from
// the on-disk cache, so repeated reads never hit the registry.
func (c *Client) ReadLayerFiles(ref, layerDigest string, want map[string]bool, maxSize int64) (map[string][]byte, error) {
	if maxSize <= 0 {
		maxSize = DefaultMaxFileSize
	}
	repo, err := repoFromRef(ref)
	if err != nil {
		return nil, err
	}
	blob, err := c.Blob(repo, layerDigest)
	if err != nil {
		return nil, err
	}
	r, err := decompress(blob)
	if err != nil {
		return nil, err
	}
	defer r.Close()

	out := make(map[string][]byte)
	tr := tar.NewReader(r)
	for {
		hdr, err := tr.Next()
		if err == io.EOF {
			break
		}
		if err != nil {
			return nil, fmt.Errorf("read layer %s: %w", layerDigest, err)
		}
		if hdr.Typeflag != tar.TypeReg && hdr.Typeflag != tar.TypeRegA {
			continue
		}
		p := normalizeTarPath(hdr.Name)
		if want != nil && !want[p] {
			continue
		}
		if hdr.Size > maxSize {
			continue
		}
		body, err := io.ReadAll(tr)
		if err != nil {
			return nil, fmt.Errorf("read %s from layer %s: %w", p, layerDigest, err)
		}
		out[p] = body
	}
	return out, nil
}

func walkTOC(blob []byte) ([]TarEntry, error) {
	r, err := decompress(blob)
	if err != nil {
		return nil, err
	}
	defer r.Close()

	var out []TarEntry
	tr := tar.NewReader(r)
	for {
		hdr, err := tr.Next()
		if err == io.EOF {
			break
		}
		if err != nil {
			return nil, err
		}
		out = append(out, TarEntry{
			Path:     normalizeTarPath(hdr.Name),
			Type:     tarType(hdr.Typeflag),
			Size:     hdr.Size,
			Mode:     hdr.Mode,
			Linkname: hdr.Linkname,
			UID:      hdr.Uid,
			GID:      hdr.Gid,
			ModTime:  hdr.ModTime,
		})
	}
	return out, nil
}

// decompress wraps a layer blob in the right reader, detected from its magic
// bytes: gzip and zstd are the common OCI layer compressions; anything else is
// assumed to be an uncompressed tar.
func decompress(blob []byte) (io.ReadCloser, error) {
	switch {
	case len(blob) >= 2 && blob[0] == 0x1f && blob[1] == 0x8b:
		return gzip.NewReader(bytes.NewReader(blob))
	case len(blob) >= 4 && blob[0] == 0x28 && blob[1] == 0xb5 && blob[2] == 0x2f && blob[3] == 0xfd:
		zr, err := zstd.NewReader(bytes.NewReader(blob))
		if err != nil {
			return nil, err
		}
		return zr.IOReadCloser(), nil
	default:
		return io.NopCloser(bytes.NewReader(blob)), nil
	}
}

func repoFromRef(ref string) (string, error) {
	r, err := name.ParseReference(ref)
	if err != nil {
		return "", fmt.Errorf("parse reference %q: %w", ref, err)
	}
	return r.Context().Name(), nil
}

// normalizeTarPath renders a tar member name as an absolute, slash-rooted path
// (e.g. "./etc/os-release" and "etc/os-release" both become "/etc/os-release").
func normalizeTarPath(n string) string {
	n = strings.TrimPrefix(n, "./")
	n = strings.TrimPrefix(n, "/")
	return "/" + n
}

func tarType(flag byte) string {
	switch flag {
	case tar.TypeReg, tar.TypeRegA:
		return "file"
	case tar.TypeDir:
		return "dir"
	case tar.TypeSymlink:
		return "symlink"
	case tar.TypeLink:
		return "hardlink"
	case tar.TypeChar:
		return "char"
	case tar.TypeBlock:
		return "block"
	case tar.TypeFifo:
		return "fifo"
	default:
		return "other"
	}
}

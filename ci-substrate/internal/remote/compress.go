package remote

import (
	"bytes"
	"compress/flate"
	"fmt"
	"io"

	repb "github.com/bazelbuild/remote-apis/build/bazel/remote/execution/v2"
	"github.com/klauspost/compress/zstd"
)

func selectCompressor(acceptable []repb.Compressor_Value) repb.Compressor_Value {
	hasDeflate := false
	for _, c := range acceptable {
		switch c {
		case repb.Compressor_ZSTD:
			return repb.Compressor_ZSTD
		case repb.Compressor_DEFLATE:
			hasDeflate = true
		}
	}
	if hasDeflate {
		return repb.Compressor_DEFLATE
	}
	return repb.Compressor_IDENTITY
}

func compressBytes(comp repb.Compressor_Value, data []byte) ([]byte, error) {
	switch comp {
	case repb.Compressor_IDENTITY:
		return data, nil
	case repb.Compressor_ZSTD:
		var buf bytes.Buffer
		w, err := zstd.NewWriter(&buf)
		if err != nil {
			return nil, err
		}
		if _, err := w.Write(data); err != nil {
			w.Close()
			return nil, err
		}
		if err := w.Close(); err != nil {
			return nil, err
		}
		return buf.Bytes(), nil
	case repb.Compressor_DEFLATE:
		var buf bytes.Buffer
		w, err := flate.NewWriter(&buf, flate.DefaultCompression)
		if err != nil {
			return nil, err
		}
		if _, err := w.Write(data); err != nil {
			w.Close()
			return nil, err
		}
		if err := w.Close(); err != nil {
			return nil, err
		}
		return buf.Bytes(), nil
	default:
		return nil, fmt.Errorf("unsupported compressor %v", comp)
	}
}

func decompressBytes(comp repb.Compressor_Value, data []byte, maxSize int64) ([]byte, error) {
	if comp == repb.Compressor_IDENTITY {
		return data, nil
	}
	r, err := newDecompressReader(comp, bytes.NewReader(data))
	if err != nil {
		return nil, err
	}
	defer r.Close()
	if maxSize >= 0 {
		out, err := io.ReadAll(io.LimitReader(r, maxSize+1))
		if err != nil {
			return nil, err
		}
		if int64(len(out)) > maxSize {
			return nil, fmt.Errorf("decompressed payload exceeds declared size %d", maxSize)
		}
		return out, nil
	}
	return io.ReadAll(r)
}

func newDecompressReader(comp repb.Compressor_Value, r io.Reader) (io.ReadCloser, error) {
	switch comp {
	case repb.Compressor_IDENTITY:
		return io.NopCloser(r), nil
	case repb.Compressor_ZSTD:
		dec, err := zstd.NewReader(r)
		if err != nil {
			return nil, err
		}
		return dec.IOReadCloser(), nil
	case repb.Compressor_DEFLATE:
		return flate.NewReader(r), nil
	default:
		return nil, fmt.Errorf("unsupported compressor %v", comp)
	}
}

func newCompressWriter(comp repb.Compressor_Value, w io.Writer) (io.WriteCloser, error) {
	switch comp {
	case repb.Compressor_ZSTD:
		return zstd.NewWriter(w)
	case repb.Compressor_DEFLATE:
		return flate.NewWriter(w, flate.DefaultCompression)
	default:
		return nil, fmt.Errorf("unsupported compressor %v", comp)
	}
}

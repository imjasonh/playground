package layer

import (
	"compress/gzip"
	"io"
)

type gzipReadCloser struct {
	gr  *gzip.Reader
	raw io.ReadCloser
}

func newGzipReader(raw io.ReadCloser) io.ReadCloser {
	gr, err := gzip.NewReader(raw)
	if err != nil {
		_ = raw.Close()
		return errReadCloser{err: err}
	}
	return &gzipReadCloser{gr: gr, raw: raw}
}

func (g *gzipReadCloser) Read(p []byte) (int, error) { return g.gr.Read(p) }
func (g *gzipReadCloser) Close() error {
	err1 := g.gr.Close()
	err2 := g.raw.Close()
	if err1 != nil {
		return err1
	}
	return err2
}

type errReadCloser struct{ err error }

func (e errReadCloser) Read([]byte) (int, error) { return 0, e.err }
func (e errReadCloser) Close() error             { return nil }

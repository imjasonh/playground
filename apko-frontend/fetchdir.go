package main

import (
	"crypto/sha256"
	"encoding/hex"
	"errors"
	"fmt"
	"io"
	"io/fs"
	"net/http"
	"net/url"
	"os"
	"path/filepath"
	"strings"
)

// fetchKey names the file that holds a URL's content in the fetch
// directory. The frontend and the helper both call it, so the URL apko
// requests in the helper finds the file BuildKit downloaded for the frontend.
func fetchKey(rawURL string) (string, error) {
	u, err := url.Parse(rawURL)
	if err != nil {
		return "", fmt.Errorf("parsing %q: %w", rawURL, err)
	}
	sum := sha256.Sum256([]byte(u.String()))
	return hex.EncodeToString(sum[:]), nil
}

// dirTransport serves GET and HEAD requests from files that the frontend
// placed in dir, named by fetchKey. It never touches the network.
//
// A URL with no file gets a 404. The frontend only places URLs it fetched
// successfully, so a URL that was missing while the frontend resolved
// packages is missing here too.
type dirTransport struct {
	dir string
}

func (t dirTransport) RoundTrip(req *http.Request) (*http.Response, error) {
	if req.Body != nil {
		req.Body.Close()
	}
	if req.Method != http.MethodGet && req.Method != http.MethodHead {
		return textResponse(req, http.StatusMethodNotAllowed, req.Method+" is not supported"), nil
	}
	key, err := fetchKey(req.URL.String())
	if err != nil {
		return nil, err
	}
	f, err := os.Open(filepath.Join(t.dir, key))
	if errors.Is(err, fs.ErrNotExist) {
		return textResponse(req, http.StatusNotFound, req.URL.Redacted()+" was not fetched by the frontend"), nil
	} else if err != nil {
		return nil, err
	}
	info, err := f.Stat()
	if err != nil {
		f.Close()
		return nil, err
	}
	var body io.ReadCloser = f
	if req.Method == http.MethodHead {
		f.Close()
		body = http.NoBody
	}
	return &http.Response{
		Status:        "200 OK",
		StatusCode:    http.StatusOK,
		Proto:         "HTTP/1.1",
		ProtoMajor:    1,
		ProtoMinor:    1,
		Header:        http.Header{"Content-Type": {"application/octet-stream"}},
		ContentLength: info.Size(),
		Body:          body,
		Request:       req,
	}, nil
}

func textResponse(req *http.Request, code int, msg string) *http.Response {
	return &http.Response{
		Status:        fmt.Sprintf("%d %s", code, http.StatusText(code)),
		StatusCode:    code,
		Proto:         "HTTP/1.1",
		ProtoMajor:    1,
		ProtoMinor:    1,
		Header:        http.Header{"Content-Type": {"text/plain"}},
		ContentLength: int64(len(msg)),
		Body:          io.NopCloser(strings.NewReader(msg)),
		Request:       req,
	}
}

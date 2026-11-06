package main

import (
	"archive/tar"
	"bytes"
	"compress/gzip"
	"context"
	"crypto/sha1"
	"crypto/sha256"
	"encoding/base64"
	"encoding/hex"
	"errors"
	"flag"
	"fmt"
	"io"
	"io/fs"
	"net/http"
	"net/url"
	"os"
	"strings"
	"time"

	"chainguard.dev/apko/pkg/apk/expandapk"
	apktypes "chainguard.dev/apko/pkg/apk/types"
)

// fetchCommand is the argument that runs the binary as a build step that
// downloads one package and checks it against its checksum.
//
// The step's cache key is its definition: the frontend image, the URL, and
// the checksum from a signed index. So BuildKit knows whether a package is
// cached without downloading it, which an HTTP source can't do without a
// checksum of the whole file. A builder that imports a remote cache can then
// reuse the apko step without downloading any package.
const fetchCommand = "fetch-apk"

// fetchAttempts bounds the downloads of one package.
const fetchAttempts = 4

func runFetch(ctx context.Context, args []string) error {
	fs := flag.NewFlagSet(fetchCommand, flag.ContinueOnError)
	pkgURL := fs.String("url", "", "package URL")
	checksum := fs.String("checksum", "", "checksum of the package's control section, as Q1<base64 SHA-1>")
	out := fs.String("out", "", "file to write the package to")
	headerFile := fs.String("auth-header-file", "", "file holding an Authorization header value, if it exists")
	tokenFile := fs.String("auth-token-file", "", "file holding a bearer token, if it exists")
	if err := fs.Parse(args); err != nil {
		return err
	}
	if *pkgURL == "" || *checksum == "" || *out == "" {
		return errors.New("-url, -checksum, and -out are required")
	}
	auth, err := authorization(*headerFile, *tokenFile)
	if err != nil {
		return err
	}
	c := http.DefaultClient
	if auth != "" {
		c, err = authClient(*pkgURL, auth)
		if err != nil {
			return err
		}
	}
	return fetchAPK(ctx, c, *pkgURL, *checksum, *out)
}

// authorization returns the Authorization header value from the first of
// headerFile and tokenFile that exists and isn't empty, or "" when neither
// does. A token becomes "Bearer <token>".
func authorization(headerFile, tokenFile string) (string, error) {
	for _, f := range []struct {
		path   string
		prefix string
	}{{headerFile, ""}, {tokenFile, "Bearer "}} {
		if f.path == "" {
			continue
		}
		data, err := os.ReadFile(f.path)
		if errors.Is(err, fs.ErrNotExist) {
			continue
		} else if err != nil {
			return "", err
		}
		if v := strings.TrimSpace(string(data)); v != "" {
			return f.prefix + v, nil
		}
	}
	return "", nil
}

// authClient returns a client that sends auth as the Authorization header
// to rawURL's host, and to no other host a redirect leads to.
func authClient(rawURL, auth string) (*http.Client, error) {
	u, err := url.Parse(rawURL)
	if err != nil {
		return nil, err
	}
	return &http.Client{Transport: authTransport{auth: auth, host: u.Host, next: http.DefaultTransport}}, nil
}

// authTransport sets the Authorization header on requests to host.
type authTransport struct {
	auth string
	host string
	next http.RoundTripper
}

func (t authTransport) RoundTrip(req *http.Request) (*http.Response, error) {
	if req.URL.Host == t.host {
		req = req.Clone(req.Context())
		req.Header.Set("Authorization", t.auth)
	}
	return t.next.RoundTrip(req)
}

// fetchAPK downloads the package at url to out and checks it against
// checksum. It retries transient failures. It writes out only when the
// package verifies, so BuildKit never caches a bad download.
func fetchAPK(ctx context.Context, c *http.Client, url, checksum, out string) error {
	tmp := out + ".partial"
	var err error
	for attempt := range fetchAttempts {
		if attempt > 0 {
			select {
			case <-ctx.Done():
				return ctx.Err()
			case <-time.After(time.Duration(1<<attempt) * time.Second):
			}
		}
		var retry bool
		retry, err = download(ctx, c, url, tmp)
		if err == nil || !retry {
			break
		}
	}
	if err != nil {
		os.Remove(tmp)
		return fmt.Errorf("downloading %s: %w", url, err)
	}
	if err := verifyAPK(tmp, checksum); err != nil {
		os.Remove(tmp)
		return fmt.Errorf("verifying %s: %w", url, err)
	}
	return os.Rename(tmp, out)
}

// download writes the body of url to path, and reports whether a failure
// might succeed on retry.
func download(ctx context.Context, c *http.Client, url, path string) (bool, error) {
	req, err := http.NewRequestWithContext(ctx, http.MethodGet, url, nil)
	if err != nil {
		return false, err
	}
	resp, err := c.Do(req)
	if err != nil {
		return true, err
	}
	defer resp.Body.Close()
	if resp.StatusCode != http.StatusOK {
		retry := resp.StatusCode == http.StatusTooManyRequests || resp.StatusCode >= 500
		return retry, fmt.Errorf("unexpected status %s", resp.Status)
	}
	f, err := os.Create(path)
	if err != nil {
		return false, err
	}
	if _, err := io.Copy(f, resp.Body); err != nil {
		f.Close()
		return true, err
	}
	return false, f.Close()
}

// verifyAPK checks the package at path against checksum, the SHA-1 of its
// control section that the signed index lists, and checks its data section
// against the SHA-256 that the control section records.
func verifyAPK(path, checksum string) error {
	f, err := os.Open(path)
	if err != nil {
		return err
	}
	defer f.Close()
	parts, err := expandapk.Split(f)
	if err != nil {
		return err
	}
	if len(parts) < 2 {
		return fmt.Errorf("found %d sections, want a control and a data section", len(parts))
	}
	control, err := io.ReadAll(parts[len(parts)-2])
	if err != nil {
		return err
	}
	sum := sha1.Sum(control)
	if got := "Q1" + base64.StdEncoding.EncodeToString(sum[:]); got != checksum {
		return fmt.Errorf("control section checksum is %s, want %s", got, checksum)
	}
	info, err := pkgInfo(control)
	if err != nil {
		return err
	}
	h := sha256.New()
	if _, err := io.Copy(h, parts[len(parts)-1]); err != nil {
		return err
	}
	if got := hex.EncodeToString(h.Sum(nil)); got != info.DataHash {
		return fmt.Errorf("data section SHA-256 is %s, want %s", got, info.DataHash)
	}
	return nil
}

// pkgInfo parses the .PKGINFO file in a gzipped control section.
func pkgInfo(control []byte) (*apktypes.PackageInfo, error) {
	zr, err := gzip.NewReader(bytes.NewReader(control))
	if err != nil {
		return nil, err
	}
	tr := tar.NewReader(zr)
	for {
		hdr, err := tr.Next()
		if err != nil {
			return nil, fmt.Errorf("finding .PKGINFO: %w", err)
		}
		if hdr.Name == ".PKGINFO" {
			return apktypes.ParsePackageInfo(tr)
		}
	}
}

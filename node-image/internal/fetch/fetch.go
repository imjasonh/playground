package fetch

import (
	"crypto/sha512"
	"encoding/base64"
	"encoding/hex"
	"fmt"
	"io"
	"net/http"
	"os"
	"path/filepath"
	"strings"
	"time"
)

// DefaultHTTPTimeout bounds each tarball download.
const DefaultHTTPTimeout = 2 * time.Minute

// Cache stores tarballs by integrity.
type Cache struct {
	Dir        string
	HTTPClient *http.Client
}

func (c *Cache) client() *http.Client {
	if c.HTTPClient != nil {
		return c.HTTPClient
	}
	return &http.Client{Timeout: DefaultHTTPTimeout}
}

// DefaultDir returns ~/.cache/node-image/packages.
func DefaultDir() (string, error) {
	home, err := os.UserHomeDir()
	if err != nil {
		return "", err
	}
	return filepath.Join(home, ".cache", "node-image", "packages"), nil
}

// Ensure downloads tarballURL if missing, verifies integrity (SRI), returns path to tarball.
func (c *Cache) Ensure(tarballURL, integrity string) (string, error) {
	if integrity == "" {
		return "", fmt.Errorf("missing integrity for %s", tarballURL)
	}
	if err := os.MkdirAll(c.Dir, 0o700); err != nil {
		return "", err
	}
	key, err := integrityKey(integrity)
	if err != nil {
		return "", err
	}
	path := filepath.Join(c.Dir, key+".tgz")
	if st, err := os.Stat(path); err == nil && st.Size() > 0 {
		if err := verifyFile(path, integrity); err == nil {
			return path, nil
		}
		_ = os.Remove(path)
	}
	resp, err := c.client().Get(tarballURL)
	if err != nil {
		return "", fmt.Errorf("fetch %s: %w", tarballURL, err)
	}
	defer resp.Body.Close()
	if resp.StatusCode != http.StatusOK {
		return "", fmt.Errorf("fetch %s: %s", tarballURL, resp.Status)
	}
	// Unique temp file so concurrent Ensure calls for the same integrity cannot
	// clobber each other's downloads.
	f, err := os.CreateTemp(c.Dir, key+".*.tmp")
	if err != nil {
		return "", err
	}
	tmp := f.Name()
	h := sha512.New()
	w := io.MultiWriter(f, h)
	_, copyErr := io.Copy(w, resp.Body)
	closeErr := f.Close()
	if copyErr != nil {
		_ = os.Remove(tmp)
		return "", copyErr
	}
	if closeErr != nil {
		_ = os.Remove(tmp)
		return "", closeErr
	}
	sum := h.Sum(nil)
	if err := checkSRI(integrity, sum); err != nil {
		_ = os.Remove(tmp)
		return "", fmt.Errorf("%s: %w", tarballURL, err)
	}
	if err := os.Rename(tmp, path); err != nil {
		_ = os.Remove(tmp)
		// Another concurrent writer may have won the rename race with a good file.
		if st, statErr := os.Stat(path); statErr == nil && st.Size() > 0 {
			if verifyFile(path, integrity) == nil {
				return path, nil
			}
		}
		return "", err
	}
	return path, nil
}

func integrityKey(integrity string) (string, error) {
	return IntegrityKey(integrity)
}

// IntegrityKey turns an SRI string (sha512-<base64>) into the filesystem key
// used under the tarball cache and integrity spool (sha512-<hex>).
func IntegrityKey(integrity string) (string, error) {
	algo, b64, ok := strings.Cut(integrity, "-")
	if !ok {
		return "", fmt.Errorf("bad integrity %q", integrity)
	}
	raw, err := base64.StdEncoding.DecodeString(b64)
	if err != nil {
		return "", fmt.Errorf("bad integrity encoding: %w", err)
	}
	return algo + "-" + hex.EncodeToString(raw), nil
}

func verifyFile(path, integrity string) error {
	f, err := os.Open(path)
	if err != nil {
		return err
	}
	defer f.Close()
	h := sha512.New()
	if _, err := io.Copy(h, f); err != nil {
		return err
	}
	return checkSRI(integrity, h.Sum(nil))
}

func checkSRI(integrity string, sha512sum []byte) error {
	algo, b64, ok := strings.Cut(integrity, "-")
	if !ok {
		return fmt.Errorf("bad integrity %q", integrity)
	}
	want, err := base64.StdEncoding.DecodeString(b64)
	if err != nil {
		return err
	}
	switch algo {
	case "sha512":
		if subtleConstantCompare(want, sha512sum) {
			return nil
		}
		return fmt.Errorf("sha512 mismatch")
	default:
		return fmt.Errorf("unsupported integrity algorithm %q", algo)
	}
}

func subtleConstantCompare(a, b []byte) bool {
	if len(a) != len(b) {
		return false
	}
	var v byte
	for i := range a {
		v |= a[i] ^ b[i]
	}
	return v == 0
}

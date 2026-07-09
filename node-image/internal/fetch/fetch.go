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
)

// Cache stores tarballs by integrity.
type Cache struct {
	Dir string
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
	if err := os.MkdirAll(c.Dir, 0o755); err != nil {
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
	resp, err := http.Get(tarballURL)
	if err != nil {
		return "", fmt.Errorf("fetch %s: %w", tarballURL, err)
	}
	defer resp.Body.Close()
	if resp.StatusCode != http.StatusOK {
		return "", fmt.Errorf("fetch %s: %s", tarballURL, resp.Status)
	}
	tmp := path + ".tmp"
	f, err := os.Create(tmp)
	if err != nil {
		return "", err
	}
	h := sha512.New()
	w := io.MultiWriter(f, h)
	if _, err := io.Copy(w, resp.Body); err != nil {
		f.Close()
		_ = os.Remove(tmp)
		return "", err
	}
	if err := f.Close(); err != nil {
		_ = os.Remove(tmp)
		return "", err
	}
	sum := h.Sum(nil)
	if err := checkSRI(integrity, sum); err != nil {
		_ = os.Remove(tmp)
		return "", fmt.Errorf("%s: %w", tarballURL, err)
	}
	if err := os.Rename(tmp, path); err != nil {
		_ = os.Remove(tmp)
		return "", err
	}
	return path, nil
}

func integrityKey(integrity string) (string, error) {
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

package fetch

import (
	"bufio"
	"crypto/sha512"
	"encoding/base64"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"io"
	"net/http"
	"net/url"
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
	// Auth resolves Authorization / token headers for a tarball URL.
	// When nil, DefaultNPMAuth is used (reads .npmrc + env).
	Auth func(*http.Request) error
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
	metaPath := filepath.Join(c.Dir, key+".ok")
	if st, err := os.Stat(path); err == nil && st.Size() > 0 {
		// Warm hit: trust size+mtime sidecar written after a prior verified download.
		// Integrity is already encoded in the filename key.
		if b, err := os.ReadFile(metaPath); err == nil {
			var meta struct {
				Size    int64 `json:"size"`
				ModNano int64 `json:"modNano"`
			}
			if json.Unmarshal(b, &meta) == nil && meta.Size == st.Size() && meta.ModNano == st.ModTime().UnixNano() {
				return path, nil
			}
		}
		if err := verifyFile(path, integrity); err == nil {
			_ = writeFetchMeta(metaPath, st)
			return path, nil
		}
		_ = os.Remove(path)
		_ = os.Remove(metaPath)
	}
	req, err := http.NewRequest(http.MethodGet, tarballURL, nil)
	if err != nil {
		return "", err
	}
	auth := c.Auth
	if auth == nil {
		auth = DefaultNPMAuth
	}
	if err := auth(req); err != nil {
		return "", err
	}
	resp, err := c.client().Do(req)
	if err != nil {
		return "", fmt.Errorf("fetch %s: %w", tarballURL, err)
	}
	defer resp.Body.Close()
	if resp.StatusCode != http.StatusOK {
		return "", fmt.Errorf("fetch %s: %s", tarballURL, resp.Status)
	}
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
		if st, statErr := os.Stat(path); statErr == nil && st.Size() > 0 {
			if verifyFile(path, integrity) == nil {
				_ = writeFetchMeta(filepath.Join(c.Dir, key+".ok"), st)
				return path, nil
			}
		}
		return "", err
	}
	if st, err := os.Stat(path); err == nil {
		_ = writeFetchMeta(filepath.Join(c.Dir, key+".ok"), st)
	}
	return path, nil
}

func writeFetchMeta(path string, st os.FileInfo) error {
	b, err := json.Marshal(struct {
		Size    int64 `json:"size"`
		ModNano int64 `json:"modNano"`
	}{Size: st.Size(), ModNano: st.ModTime().UnixNano()})
	if err != nil {
		return err
	}
	return os.WriteFile(path, append(b, '\n'), 0o600)
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

// DefaultNPMAuth attaches npm-style auth from env and ~/.npmrc / project .npmrc.
// Never logs token values. Supports:
//   - NPM_TOKEN / NODE_AUTH_TOKEN → Bearer for any host
//   - //host/:_authToken=… in .npmrc
func DefaultNPMAuth(req *http.Request) error {
	if req.URL == nil {
		return nil
	}
	host := req.URL.Host
	if token := firstEnv("NODE_AUTH_TOKEN", "NPM_TOKEN"); token != "" {
		req.Header.Set("Authorization", "Bearer "+token)
		return nil
	}
	token := lookupNPMRCToken(host)
	if token != "" {
		req.Header.Set("Authorization", "Bearer "+token)
	}
	return nil
}

func firstEnv(keys ...string) string {
	for _, k := range keys {
		if v := os.Getenv(k); v != "" {
			return v
		}
	}
	return ""
}

func lookupNPMRCToken(host string) string {
	paths := npmrcPaths()
	for _, p := range paths {
		if tok := readNPMRCToken(p, host); tok != "" {
			return tok
		}
	}
	return ""
}

func npmrcPaths() []string {
	var out []string
	if wd, err := os.Getwd(); err == nil {
		out = append(out, filepath.Join(wd, ".npmrc"))
	}
	if home, err := os.UserHomeDir(); err == nil {
		out = append(out, filepath.Join(home, ".npmrc"))
	}
	return out
}

func readNPMRCToken(path, host string) string {
	f, err := os.Open(path)
	if err != nil {
		return ""
	}
	defer f.Close()
	wantPrefix := "//" + host + "/:_authToken="
	wantPrefixNoSlash := "//" + host + ":_authToken="
	sc := bufio.NewScanner(f)
	for sc.Scan() {
		line := strings.TrimSpace(sc.Text())
		if line == "" || strings.HasPrefix(line, "#") || strings.HasPrefix(line, ";") {
			continue
		}
		for _, prefix := range []string{wantPrefix, wantPrefixNoSlash} {
			if strings.HasPrefix(line, prefix) {
				return strings.TrimSpace(strings.TrimPrefix(line, prefix))
			}
		}
		// Match registry host from URL-shaped keys.
		if strings.Contains(line, ":_authToken=") {
			u := strings.SplitN(line, ":_authToken=", 2)
			if len(u) == 2 && hostMatchesNPMRC(u[0], host) {
				return strings.TrimSpace(u[1])
			}
		}
	}
	return ""
}

func hostMatchesNPMRC(key, host string) bool {
	key = strings.TrimPrefix(key, "//")
	key = strings.TrimSuffix(key, "/")
	if i := strings.Index(key, "/"); i >= 0 {
		key = key[:i]
	}
	if key == host {
		return true
	}
	// Compare URL host if key looks like a URL.
	if u, err := url.Parse("https://" + key); err == nil && u.Host == host {
		return true
	}
	return false
}

// Package registry parses image references, and reads the digests of
// images from container registries with only the standard library, so that
// a program in the cluster can resolve an image's tag without
// go-containerregistry.
package registry

import (
	"context"
	"crypto/sha256"
	"encoding/base64"
	"encoding/hex"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"io/fs"
	"maps"
	"net"
	"net/http"
	"net/url"
	"os"
	"path/filepath"
	"regexp"
	"slices"
	"strings"
	"time"
)

// A Reference is an image reference, which Kubernetes reads as docker does.
type Reference struct {
	// Name is the repository as the reference writes it, without a tag or
	// digest, such as "nginx" or "ghcr.io/you/app".
	Name string
	// Registry is the host, and optionally the port, of the registry that
	// serves the repository, such as "registry-1.docker.io" for Docker Hub.
	Registry string
	// Repository is the repository's path in the registry, such as
	// "library/nginx".
	Repository string
	// Tag is the reference's tag, or empty.
	Tag string
	// Digest is the reference's digest, such as "sha256:...", or empty.
	Digest string
}

// The grammar of references is docker's, from
// github.com/distribution/reference.
var (
	hostRE   = regexp.MustCompile(`^(?:[a-zA-Z0-9](?:[a-zA-Z0-9-]*[a-zA-Z0-9])?(?:\.[a-zA-Z0-9](?:[a-zA-Z0-9-]*[a-zA-Z0-9])?)*|\[[a-fA-F0-9:]+\])(?::[0-9]+)?$`)
	pathRE   = regexp.MustCompile(`^[a-z0-9]+(?:(?:[._]|__|-+)[a-z0-9]+)*(?:/[a-z0-9]+(?:(?:[._]|__|-+)[a-z0-9]+)*)*$`)
	tagRE    = regexp.MustCompile(`^\w[\w.-]{0,127}$`)
	digestRE = regexp.MustCompile(`^[A-Za-z][A-Za-z0-9]*(?:[-_+.][A-Za-z][A-Za-z0-9]*)*:[0-9a-fA-F]{32,}$`)
	sha256RE = regexp.MustCompile(`^sha256:[0-9a-f]{64}$`)
)

// Parse parses s, an image reference such as "nginx:1.27",
// "ghcr.io/you/app@sha256:...", or "localhost:5000/app".
func Parse(s string) (Reference, error) {
	var r Reference
	name := s
	if i := strings.IndexByte(s, '@'); i >= 0 {
		name, r.Digest = s[:i], s[i+1:]
		if !digestRE.MatchString(r.Digest) {
			return Reference{}, errors.New("not an image reference: the digest isn't valid")
		}
	}
	// As in docker, the part before the first slash is the registry's host
	// if it looks like a host rather than a repository's first component.
	host, path := "", name
	if i := strings.IndexByte(name, '/'); i >= 0 {
		if first := name[:i]; strings.ContainsAny(first, ".:") || first == "localhost" || strings.ToLower(first) != first {
			host, path = first, name[i+1:]
		}
	}
	r.Name = name
	if i := strings.LastIndexByte(path, ':'); i >= 0 {
		path, r.Tag = path[:i], path[i+1:]
		r.Name = name[:len(name)-len(r.Tag)-1]
		if !tagRE.MatchString(r.Tag) {
			return Reference{}, errors.New("not an image reference: the tag isn't valid")
		}
	}
	switch {
	case host != "" && !hostRE.MatchString(host):
		return Reference{}, errors.New("not an image reference: the registry isn't a host name")
	case !pathRE.MatchString(path):
		return Reference{}, errors.New("not an image reference: a repository has lowercase letters and digits, separated by slashes, periods, underscores, or dashes")
	case len(r.Name) > 255:
		return Reference{}, errors.New("not an image reference: the name is longer than 255 characters")
	}
	r.Registry, r.Repository = host, path
	switch host {
	case "", "docker.io", "index.docker.io":
		r.Registry = "registry-1.docker.io"
		if !strings.Contains(path, "/") {
			r.Repository = "library/" + path
		}
	}
	return r, nil
}

// WithDigest returns the reference to the image with digest d in r's
// repository, with the repository as r writes it, such as "nginx@sha256:...".
func (r Reference) WithDigest(d string) string { return r.Name + "@" + d }

const (
	// manifestTypes are the media types of the manifests and indexes that
	// Digest accepts. With an index's types first, the digest of a tag
	// that names an index for several platforms is the index's, which is
	// what the kubelet pulls.
	manifestTypes = "application/vnd.oci.image.index.v1+json, application/vnd.docker.distribution.manifest.list.v2+json, application/vnd.oci.image.manifest.v1+json, application/vnd.docker.distribution.manifest.v2+json"
	userAgent     = "kube (github.com/imjasonh/playground/kube)"
	maxManifest   = 4 << 20
	maxBody       = 1 << 20
)

var httpClient = &http.Client{Timeout: 30 * time.Second}

// Digest returns the digest of the manifest or index that ref names by tag,
// or by the tag latest if ref has neither a tag nor a digest. It reads the
// credentials for ref's registry from the docker config file,
// $DOCKER_CONFIG/config.json or ~/.docker/config.json, as docker login
// writes them; it doesn't run credential helpers. It uses HTTPS, and tries
// HTTP after HTTPS only for a registry at localhost or a loopback address.
func Digest(ctx context.Context, ref string) (string, error) {
	r, err := Parse(ref)
	if err != nil {
		return "", err
	}
	if r.Digest != "" {
		return r.Digest, nil
	}
	cred, err := credentials(r.Registry)
	if err != nil {
		return "", err
	}
	tag := r.Tag
	if tag == "" {
		tag = "latest"
	}
	var d string
	for _, scheme := range schemes(r.Registry) {
		s := &session{registry: r.Registry, repository: r.Repository, cred: cred}
		d, err = s.digest(ctx, scheme+"://"+r.Registry+"/v2/"+r.Repository+"/manifests/"+tag)
		// A registry that answers HTTPS requests is an HTTPS registry, and
		// only a request that got no answer tries the next scheme.
		var ue *url.Error
		if err == nil || !errors.As(err, &ue) || ctx.Err() != nil {
			break
		}
	}
	return d, err
}

// schemes returns the URL schemes to try for registry, in order.
func schemes(registry string) []string {
	if loopback(registry) {
		return []string{"https", "http"}
	}
	return []string{"https"}
}

// loopback reports whether host, which may have a port, is localhost or a
// loopback address.
func loopback(host string) bool {
	if h, _, err := net.SplitHostPort(host); err == nil {
		host = h
	}
	host = strings.Trim(host, "[]")
	if strings.EqualFold(host, "localhost") {
		return true
	}
	ip := net.ParseIP(host)
	return ip != nil && ip.IsLoopback()
}

// A session reads the digest of one manifest. It answers the registry's
// challenge for credentials once, and sends the answer with its later
// requests.
type session struct {
	registry, repository string
	cred                 *credential
	// auth is the Authorization header, once the registry asks for one.
	auth string
}

func (s *session) digest(ctx context.Context, u string) (string, error) {
	resp, err := s.do(ctx, http.MethodHead, u)
	if err != nil {
		return "", err
	}
	resp.Body.Close()
	if d := resp.Header.Get("Docker-Content-Digest"); resp.StatusCode == http.StatusOK && sha256RE.MatchString(d) {
		return d, nil
	}
	// Without the header, or for a registry that doesn't answer HEAD, the
	// digest is the hash of the manifest. A GET that fails also has the
	// registry's error in its body.
	resp, err = s.do(ctx, http.MethodGet, u)
	if err != nil {
		return "", err
	}
	defer resp.Body.Close()
	if resp.StatusCode != http.StatusOK {
		return "", statusError(resp)
	}
	h := sha256.New()
	n, err := io.Copy(h, io.LimitReader(resp.Body, maxManifest+1))
	switch {
	case err != nil:
		return "", fmt.Errorf("GET %s: %w", u, err)
	case n > maxManifest:
		return "", fmt.Errorf("GET %s: the manifest is larger than %d bytes", u, maxManifest)
	}
	return "sha256:" + hex.EncodeToString(h.Sum(nil)), nil
}

// do sends a request to the registry. If the registry answers that the
// request needs credentials, do gets a token or uses the credentials from
// the docker config file, and sends the request again.
func (s *session) do(ctx context.Context, method, u string) (*http.Response, error) {
	resp, err := s.send(ctx, method, u)
	if err != nil {
		return nil, err
	}
	if resp.StatusCode != http.StatusUnauthorized || s.auth != "" {
		return resp, nil
	}
	ch := parseChallenge(resp.Header.Values("WWW-Authenticate"))
	resp.Body.Close()
	switch strings.ToLower(ch.scheme) {
	case "bearer":
		tok, err := s.token(ctx, ch.params)
		if err != nil {
			return nil, err
		}
		s.auth = "Bearer " + tok
	case "basic":
		if s.cred == nil {
			return nil, fmt.Errorf("%s %s: %s, and the docker config file has no credentials for %s", method, u, resp.Status, s.registry)
		}
		s.auth = "Basic " + base64.StdEncoding.EncodeToString([]byte(s.cred.username+":"+s.cred.password))
	default:
		return nil, fmt.Errorf("%s %s: %s", method, u, resp.Status)
	}
	return s.send(ctx, method, u)
}

func (s *session) send(ctx context.Context, method, u string) (*http.Response, error) {
	req, err := http.NewRequestWithContext(ctx, method, u, nil)
	if err != nil {
		return nil, err
	}
	req.Header.Set("Accept", manifestTypes)
	req.Header.Set("User-Agent", userAgent)
	if s.auth != "" {
		req.Header.Set("Authorization", s.auth)
	}
	return httpClient.Do(req)
}

// token gets a token to pull from the repository, from the realm that the
// registry's challenge names. It sends the realm the credentials for the
// registry, if any, and only over HTTPS unless the realm is on a loopback
// address.
func (s *session) token(ctx context.Context, params map[string]string) (string, error) {
	realm, err := url.Parse(params["realm"])
	if err != nil || realm.Host == "" || realm.Scheme != "https" && (realm.Scheme != "http" || !loopback(realm.Host)) {
		return "", fmt.Errorf("%s: the token realm %q isn't an https URL", s.registry, params["realm"])
	}
	q := realm.Query()
	if svc := params["service"]; svc != "" {
		q.Set("service", svc)
	}
	q.Set("scope", "repository:"+s.repository+":pull")
	realm.RawQuery = q.Encode()
	req, err := http.NewRequestWithContext(ctx, http.MethodGet, realm.String(), nil)
	if err != nil {
		return "", err
	}
	req.Header.Set("User-Agent", userAgent)
	if s.cred != nil {
		req.SetBasicAuth(s.cred.username, s.cred.password)
	}
	resp, err := httpClient.Do(req)
	if err != nil {
		return "", err
	}
	defer resp.Body.Close()
	if resp.StatusCode != http.StatusOK {
		return "", statusError(resp)
	}
	var body struct {
		Token       string `json:"token"`
		AccessToken string `json:"access_token"`
	}
	if err := json.NewDecoder(io.LimitReader(resp.Body, maxBody)).Decode(&body); err != nil {
		return "", fmt.Errorf("GET %s: %w", realm.Redacted(), err)
	}
	if body.Token == "" {
		body.Token = body.AccessToken
	}
	if body.Token == "" {
		return "", fmt.Errorf("GET %s: the response has no token", realm.Redacted())
	}
	return body.Token, nil
}

// statusError describes a failed response, with the errors that the
// registry reports in its body.
func statusError(resp *http.Response) error {
	msg := fmt.Sprintf("%s %s: %s", resp.Request.Method, resp.Request.URL.Redacted(), resp.Status)
	var body struct {
		Errors []struct {
			Code    string `json:"code"`
			Message string `json:"message"`
		} `json:"errors"`
	}
	if json.NewDecoder(io.LimitReader(resp.Body, maxBody)).Decode(&body) == nil {
		for i, e := range body.Errors {
			sep := ": "
			if i > 0 {
				sep = "; "
			}
			msg += sep + strings.TrimSuffix(e.Code+": "+e.Message, ": ")
		}
	}
	return errors.New(msg)
}

// A challenge is the scheme and parameters of a WWW-Authenticate header,
// such as Bearer realm="https://auth.docker.io/token",service="registry.docker.io".
type challenge struct {
	scheme string
	params map[string]string
}

// parseChallenge parses the first of headers that has a challenge.
func parseChallenge(headers []string) challenge {
	for _, h := range headers {
		scheme, rest, _ := strings.Cut(strings.TrimSpace(h), " ")
		if scheme == "" {
			continue
		}
		ch := challenge{scheme: scheme, params: map[string]string{}}
		for rest = strings.TrimSpace(rest); rest != ""; rest = strings.TrimSpace(strings.TrimPrefix(strings.TrimSpace(rest), ",")) {
			var key, value string
			key, rest, _ = strings.Cut(rest, "=")
			rest = strings.TrimSpace(rest)
			if strings.HasPrefix(rest, `"`) {
				var b strings.Builder
				i := 1
				for ; i < len(rest) && rest[i] != '"'; i++ {
					if rest[i] == '\\' && i+1 < len(rest) {
						i++
					}
					b.WriteByte(rest[i])
				}
				value, rest = b.String(), rest[min(i+1, len(rest)):]
			} else {
				value, rest, _ = strings.Cut(rest, ",")
			}
			ch.params[strings.ToLower(strings.TrimSpace(key))] = strings.TrimSpace(value)
		}
		return ch
	}
	return challenge{}
}

type credential struct{ username, password string }

// credentials returns the credentials for registry in the docker config
// file, or nil if there's no file or it has none for registry.
func credentials(registry string) (*credential, error) {
	dir := os.Getenv("DOCKER_CONFIG")
	if dir == "" {
		home, err := os.UserHomeDir()
		if err != nil {
			return nil, nil
		}
		dir = filepath.Join(home, ".docker")
	}
	file := filepath.Join(dir, "config.json")
	b, err := os.ReadFile(file)
	if errors.Is(err, fs.ErrNotExist) {
		return nil, nil
	}
	if err != nil {
		return nil, fmt.Errorf("reading credentials: %w", err)
	}
	var cfg struct {
		Auths map[string]struct {
			Auth     string `json:"auth"`
			Username string `json:"username"`
			Password string `json:"password"`
		} `json:"auths"`
	}
	if err := json.Unmarshal(b, &cfg); err != nil {
		return nil, fmt.Errorf("reading credentials from %s: %w", file, err)
	}
	want := configHost(registry)
	for _, key := range slices.Sorted(maps.Keys(cfg.Auths)) {
		a := cfg.Auths[key]
		if configHost(key) != want {
			continue
		}
		c := &credential{username: a.Username, password: a.Password}
		if a.Auth != "" {
			b, err := base64.StdEncoding.DecodeString(a.Auth)
			user, pass, ok := strings.Cut(string(b), ":")
			if err != nil || !ok {
				return nil, fmt.Errorf("reading credentials from %s: the auth for %s isn't base64 of user:password", file, key)
			}
			c = &credential{username: user, password: pass}
		}
		// A credential helper's entry has no credentials.
		if c.username != "" || c.password != "" {
			return c, nil
		}
	}
	return nil, nil
}

// configHost returns the registry host of a registry, or of a key in the
// docker config file's auths, such as "https://index.docker.io/v1/" or
// "ghcr.io", with each of Docker Hub's names as docker.io.
func configHost(key string) string {
	h := strings.ToLower(key)
	if _, after, ok := strings.Cut(h, "://"); ok {
		h = after
	}
	h, _, _ = strings.Cut(h, "/")
	switch h {
	case "index.docker.io", "registry-1.docker.io":
		return "docker.io"
	}
	return h
}

package registry

import (
	"encoding/base64"
	"fmt"
	"io"
	"log"
	"net/http"
	"net/http/httptest"
	"os"
	"path/filepath"
	"reflect"
	"slices"
	"strings"
	"sync"
	"testing"

	"github.com/google/go-containerregistry/pkg/name"
	ggcr "github.com/google/go-containerregistry/pkg/registry"
	"github.com/google/go-containerregistry/pkg/v1/remote"
	"github.com/google/go-containerregistry/pkg/v1/types"

	"github.com/imjasonh/playground/kube/internal/image/imagetest"
)

const testDigest = "sha256:0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"

func TestParse(t *testing.T) {
	const hub = "registry-1.docker.io"
	for _, tt := range []struct {
		in   string
		want Reference
	}{
		{"nginx", Reference{Name: "nginx", Registry: hub, Repository: "library/nginx"}},
		{"nginx:1.27", Reference{Name: "nginx", Registry: hub, Repository: "library/nginx", Tag: "1.27"}},
		{"docker.io/library/nginx:1.27", Reference{Name: "docker.io/library/nginx", Registry: hub, Repository: "library/nginx", Tag: "1.27"}},
		{"index.docker.io/nginx", Reference{Name: "index.docker.io/nginx", Registry: hub, Repository: "library/nginx"}},
		{"chainguard/static:latest", Reference{Name: "chainguard/static", Registry: hub, Repository: "chainguard/static", Tag: "latest"}},
		{"ghcr.io/you/app@" + testDigest, Reference{Name: "ghcr.io/you/app", Registry: "ghcr.io", Repository: "you/app", Digest: testDigest}},
		{"ghcr.io/you/app:v1@" + testDigest, Reference{Name: "ghcr.io/you/app", Registry: "ghcr.io", Repository: "you/app", Tag: "v1", Digest: testDigest}},
		{"localhost:5000/app", Reference{Name: "localhost:5000/app", Registry: "localhost:5000", Repository: "app"}},
		{"localhost/app:v1", Reference{Name: "localhost/app", Registry: "localhost", Repository: "app", Tag: "v1"}},
		{"[::1]:5000/app:v1", Reference{Name: "[::1]:5000/app", Registry: "[::1]:5000", Repository: "app", Tag: "v1"}},
		{"Registry/app", Reference{Name: "Registry/app", Registry: "Registry", Repository: "app"}},
		{"registry.example.com:443/team/my_app:1.0-rc.1", Reference{Name: "registry.example.com:443/team/my_app", Registry: "registry.example.com:443", Repository: "team/my_app", Tag: "1.0-rc.1"}},
	} {
		got, err := Parse(tt.in)
		if err != nil {
			t.Errorf("Parse(%q): %v", tt.in, err)
			continue
		}
		if got != tt.want {
			t.Errorf("Parse(%q) = %+v, want %+v", tt.in, got, tt.want)
		}
	}
}

func TestParseRejects(t *testing.T) {
	for _, in := range []string{
		"",
		"Nginx",
		"nginx:",
		"nginx:-1",
		"nginx:1.27:2",
		"nginx@sha256:abc",
		"nginx@" + testDigest + "x",
		"a/../b",
		"example.com:http/app",
		"ghcr.io/",
		"ghcr.io//app",
		strings.Repeat("a", 256),
	} {
		if r, err := Parse(in); err == nil {
			t.Errorf("Parse(%q) = %+v, want an error", in, r)
		}
	}
}

func TestWithDigest(t *testing.T) {
	for in, want := range map[string]string{
		"nginx:1.27":              "nginx@" + testDigest,
		"docker.io/library/nginx": "docker.io/library/nginx@" + testDigest,
		"localhost:5000/app:v1":   "localhost:5000/app@" + testDigest,
		"ghcr.io/you/app:v1@sha256:" + strings.Repeat("f", 64): "ghcr.io/you/app@" + testDigest,
	} {
		r, err := Parse(in)
		if err != nil {
			t.Fatal(err)
		}
		if got := r.WithDigest(testDigest); got != want {
			t.Errorf("Parse(%q).WithDigest() = %q, want %q", in, got, want)
		}
	}
}

func mustRef(t *testing.T, s string) name.Reference {
	t.Helper()
	r, err := name.ParseReference(s)
	if err != nil {
		t.Fatal(err)
	}
	return r
}

// noConfig points Digest at an empty docker config directory, so that the
// developer's credentials don't change what a test sees.
func noConfig(t *testing.T) {
	t.Helper()
	t.Setenv("DOCKER_CONFIG", t.TempDir())
}

// writeConfig points Digest at a docker config file with the given auths.
func writeConfig(t *testing.T, auths string) {
	t.Helper()
	dir := t.TempDir()
	if err := os.WriteFile(filepath.Join(dir, "config.json"), []byte(`{"auths":`+auths+`}`), 0o600); err != nil {
		t.Fatal(err)
	}
	t.Setenv("DOCKER_CONFIG", dir)
}

// serve serves h until the test ends, and returns its host.
func serve(t *testing.T, h http.Handler) string {
	t.Helper()
	srv := httptest.NewServer(h)
	t.Cleanup(srv.Close)
	return strings.TrimPrefix(srv.URL, "http://")
}

func newRegistry() http.Handler { return ggcr.New(ggcr.Logger(log.New(io.Discard, "", 0))) }

// requests records the method and path of each request that h serves.
type requests struct {
	mu  sync.Mutex
	got []string
}

func (rs *requests) record(h http.Handler) http.Handler {
	return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		rs.mu.Lock()
		rs.got = append(rs.got, r.Method+" "+r.URL.Path)
		rs.mu.Unlock()
		h.ServeHTTP(w, r)
	})
}

func TestDigest(t *testing.T) {
	noConfig(t)
	images := newRegistry()
	reg := serve(t, images)
	index := imagetest.Base(t, reg+"/chainguard/static:latest", "linux/amd64", "linux/arm64")
	img := imagetest.Image(t, "linux/amd64", types.DockerManifestSchema2)
	if err := remote.Write(mustRef(t, reg+"/team/app:v1"), img, remote.WithContext(t.Context())); err != nil {
		t.Fatal(err)
	}
	manifest, err := img.Digest()
	if err != nil {
		t.Fatal(err)
	}
	var rs requests
	recorded := serve(t, rs.record(images))
	for _, tt := range []struct{ ref, want string }{
		{reg + "/chainguard/static:latest", index},
		{reg + "/chainguard/static", index},
		{"localhost:" + strings.Split(reg, ":")[1] + "/team/app:v1", manifest.String()},
		{"registry.invalid/app:v1@" + testDigest, testDigest},
		{recorded + "/chainguard/static:latest", index},
	} {
		got, err := Digest(t.Context(), tt.ref)
		if err != nil {
			t.Errorf("Digest(%q): %v", tt.ref, err)
			continue
		}
		if got != tt.want {
			t.Errorf("Digest(%q) = %q, want %q", tt.ref, got, tt.want)
		}
	}
	// The digest is in the response to HEAD, which Docker Hub doesn't count
	// against its pull limit, so Digest doesn't GET the manifest.
	if want := []string{"HEAD /v2/chainguard/static/manifests/latest"}; !slices.Equal(rs.got, want) {
		t.Errorf("Digest sent %q, want %q", rs.got, want)
	}
}

// noDigest serves a response without the Docker-Content-Digest header.
type noDigest struct{ http.ResponseWriter }

func (w noDigest) WriteHeader(code int) {
	w.Header().Del("Docker-Content-Digest")
	w.ResponseWriter.WriteHeader(code)
}

func (w noDigest) Write(b []byte) (int, error) {
	w.Header().Del("Docker-Content-Digest")
	return w.ResponseWriter.Write(b)
}

func TestDigestHashesManifest(t *testing.T) {
	noConfig(t)
	images := newRegistry()
	want := imagetest.Base(t, serve(t, images)+"/chainguard/static:latest", "linux/amd64")
	for _, tt := range []struct {
		name string
		h    http.Handler
	}{
		{"without the digest header", http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
			images.ServeHTTP(noDigest{w}, r)
		})},
		{"without HEAD", http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
			if r.Method == http.MethodHead {
				w.WriteHeader(http.StatusMethodNotAllowed)
				return
			}
			images.ServeHTTP(noDigest{w}, r)
		})},
	} {
		t.Run(tt.name, func(t *testing.T) {
			got, err := Digest(t.Context(), serve(t, tt.h)+"/chainguard/static:latest")
			if err != nil {
				t.Fatal(err)
			}
			if got != want {
				t.Errorf("Digest() = %q, want %q", got, want)
			}
		})
	}
}

func TestDigestFails(t *testing.T) {
	noConfig(t)
	reg := serve(t, newRegistry())
	imagetest.Base(t, reg+"/chainguard/static:latest", "linux/amd64")
	for _, tt := range []struct{ ref, want string }{
		{reg + "/chainguard/static:nope", "/v2/chainguard/static/manifests/nope: 404 Not Found: MANIFEST_UNKNOWN: Unknown manifest"},
		{reg + "/chainguard/nope:latest", "404 Not Found: NAME_UNKNOWN"},
		{"Nginx:1.27", "not an image reference"},
		{"127.0.0.1:1/app:v1", "http://127.0.0.1:1/v2/app/manifests/v1"},
	} {
		if d, err := Digest(t.Context(), tt.ref); err == nil || !strings.Contains(err.Error(), tt.want) {
			t.Errorf("Digest(%q) = %q, %v; want an error with %q", tt.ref, d, err, tt.want)
		}
	}
}

func basic(user, password string) string {
	return base64.StdEncoding.EncodeToString([]byte(user + ":" + password))
}

func TestDigestToken(t *testing.T) {
	images := newRegistry()
	want := imagetest.Base(t, serve(t, images)+"/team/app:v1", "linux/amd64")
	var host string
	mux := http.NewServeMux()
	mux.HandleFunc("/token", func(w http.ResponseWriter, r *http.Request) {
		user, password, ok := r.BasicAuth()
		q := r.URL.Query()
		if !ok || user != "user" || password != "secret" || q.Get("service") != "test" || q.Get("scope") != "repository:team/app:pull" {
			w.WriteHeader(http.StatusUnauthorized)
			return
		}
		_, _ = io.WriteString(w, `{"token":"t0k3n"}`)
	})
	mux.HandleFunc("/v2/", func(w http.ResponseWriter, r *http.Request) {
		if r.Header.Get("Authorization") != "Bearer t0k3n" {
			w.Header().Set("WWW-Authenticate", `Bearer realm="http://`+host+`/token",service="test"`)
			w.WriteHeader(http.StatusUnauthorized)
			return
		}
		images.ServeHTTP(w, r)
	})
	host = serve(t, mux)

	writeConfig(t, `{"`+host+`":{"auth":"`+basic("user", "secret")+`"}}`)
	got, err := Digest(t.Context(), host+"/team/app:v1")
	if err != nil {
		t.Fatal(err)
	}
	if got != want {
		t.Errorf("Digest() = %q, want %q", got, want)
	}

	noConfig(t)
	if _, err := Digest(t.Context(), host+"/team/app:v1"); err == nil || !strings.Contains(err.Error(), "/token?scope=repository%3Ateam%2Fapp%3Apull&service=test: 401 Unauthorized") {
		t.Errorf("Digest() without credentials: %v, want the token's 401", err)
	}
}

func TestDigestTokenRealm(t *testing.T) {
	noConfig(t)
	host := serve(t, http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		w.Header().Set("WWW-Authenticate", `Bearer realm="http://auth.example.com/token"`)
		w.WriteHeader(http.StatusUnauthorized)
	}))
	if _, err := Digest(t.Context(), host+"/team/app:v1"); err == nil || !strings.Contains(err.Error(), `the token realm "http://auth.example.com/token" isn't an https URL`) {
		t.Errorf("Digest(): %v, want an error about the realm", err)
	}
}

func TestDigestBasic(t *testing.T) {
	images := newRegistry()
	want := imagetest.Base(t, serve(t, images)+"/team/app:v1", "linux/amd64")
	host := serve(t, http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		if user, password, ok := r.BasicAuth(); !ok || user != "user" || password != "secret" {
			w.Header().Set("WWW-Authenticate", `Basic realm="test"`)
			w.WriteHeader(http.StatusUnauthorized)
			return
		}
		images.ServeHTTP(w, r)
	}))

	writeConfig(t, `{"http://`+host+`":{"username":"user","password":"secret"}}`)
	got, err := Digest(t.Context(), host+"/team/app:v1")
	if err != nil {
		t.Fatal(err)
	}
	if got != want {
		t.Errorf("Digest() = %q, want %q", got, want)
	}

	noConfig(t)
	if _, err := Digest(t.Context(), host+"/team/app:v1"); err == nil || !strings.Contains(err.Error(), "401 Unauthorized, and the docker config file has no credentials for "+host) {
		t.Errorf("Digest() without credentials: %v, want an error that names the registry", err)
	}
}

func TestCredentials(t *testing.T) {
	auth := basic("user", "pa:ss")
	for _, tt := range []struct {
		name, auths, registry string
		want                  *credential
		wantErr               string
	}{
		{name: "no file", registry: "ghcr.io"},
		{name: "auth", auths: `{"ghcr.io":{"auth":"` + auth + `"}}`, registry: "ghcr.io", want: &credential{"user", "pa:ss"}},
		{name: "username and password", auths: `{"https://ghcr.io":{"username":"u","password":"p"}}`, registry: "ghcr.io", want: &credential{"u", "p"}},
		{name: "docker hub", auths: `{"https://index.docker.io/v1/":{"auth":"` + auth + `"}}`, registry: "registry-1.docker.io", want: &credential{"user", "pa:ss"}},
		{name: "port", auths: `{"localhost:5000":{"auth":"` + auth + `"}}`, registry: "localhost:5000", want: &credential{"user", "pa:ss"}},
		{name: "other registry", auths: `{"gcr.io":{"auth":"` + auth + `"}}`, registry: "ghcr.io"},
		{name: "credential helper", auths: `{"ghcr.io":{}}`, registry: "ghcr.io"},
		{name: "auth isn't base64", auths: `{"ghcr.io":{"auth":"user:pass"}}`, registry: "ghcr.io", wantErr: "the auth for ghcr.io isn't base64 of user:password"},
		{name: "not JSON", auths: `[`, registry: "ghcr.io", wantErr: "reading credentials from "},
	} {
		t.Run(tt.name, func(t *testing.T) {
			if tt.auths == "" {
				noConfig(t)
			} else {
				writeConfig(t, tt.auths)
			}
			got, err := credentials(tt.registry)
			if tt.wantErr != "" {
				if err == nil || !strings.Contains(err.Error(), tt.wantErr) {
					t.Fatalf("credentials() = %v, %v; want an error with %q", got, err, tt.wantErr)
				}
				return
			}
			if err != nil {
				t.Fatal(err)
			}
			if !reflect.DeepEqual(got, tt.want) {
				t.Errorf("credentials() = %v, want %v", got, tt.want)
			}
		})
	}

	t.Run("home", func(t *testing.T) {
		home := t.TempDir()
		if err := os.MkdirAll(filepath.Join(home, ".docker"), 0o700); err != nil {
			t.Fatal(err)
		}
		if err := os.WriteFile(filepath.Join(home, ".docker", "config.json"), []byte(`{"auths":{"ghcr.io":{"auth":"`+auth+`"}}}`), 0o600); err != nil {
			t.Fatal(err)
		}
		t.Setenv("DOCKER_CONFIG", "")
		t.Setenv("HOME", home)
		got, err := credentials("ghcr.io")
		if err != nil || !reflect.DeepEqual(got, &credential{"user", "pa:ss"}) {
			t.Errorf("credentials() = %v, %v; want the credentials in ~/.docker/config.json", got, err)
		}
	})
}

func TestParseChallenge(t *testing.T) {
	for _, tt := range []struct {
		headers []string
		want    challenge
	}{
		{nil, challenge{}},
		{[]string{`Bearer realm="https://auth.docker.io/token",service="registry.docker.io"`}, challenge{"Bearer", map[string]string{"realm": "https://auth.docker.io/token", "service": "registry.docker.io"}}},
		{[]string{`Basic realm="Registry Realm"`}, challenge{"Basic", map[string]string{"realm": "Registry Realm"}}},
		{[]string{"", `bearer Realm=https://example.com/token, Service=svc`}, challenge{"bearer", map[string]string{"realm": "https://example.com/token", "service": "svc"}}},
		{[]string{`Bearer realm="a\"b,c", scope="x"`}, challenge{"Bearer", map[string]string{"realm": `a"b,c`, "scope": "x"}}},
	} {
		if got := parseChallenge(tt.headers); !reflect.DeepEqual(got, tt.want) {
			t.Errorf("parseChallenge(%q) = %+v, want %+v", tt.headers, got, tt.want)
		}
	}
}

func TestSchemes(t *testing.T) {
	for host, want := range map[string]string{
		"localhost":             "https http",
		"LOCALHOST:5000":        "https http",
		"127.0.0.1:5000":        "https http",
		"127.1.2.3":             "https http",
		"[::1]:5000":            "https http",
		"::1":                   "https http",
		"example.com":           "https",
		"10.0.0.1:5000":         "https",
		"localhost.example.com": "https",
		"registry-1.docker.io":  "https",
	} {
		if got := strings.Join(schemes(host), " "); got != want {
			t.Errorf("schemes(%q) = %q, want %q", host, got, want)
		}
	}
}

func TestConfigHost(t *testing.T) {
	for key, want := range map[string]string{
		"https://index.docker.io/v1/": "docker.io",
		"registry-1.docker.io":        "docker.io",
		"docker.io":                   "docker.io",
		"GHCR.io":                     "ghcr.io",
		"http://localhost:5000":       "localhost:5000",
		"https://gcr.io/v2/":          "gcr.io",
	} {
		if got := configHost(key); got != want {
			t.Errorf("configHost(%q) = %q, want %q", key, got, want)
		}
	}
}

func ExampleParse() {
	r, err := Parse("nginx:1.27")
	if err != nil {
		panic(err)
	}
	fmt.Println(r.Registry, r.Repository, r.Tag)
	fmt.Println(r.WithDigest(testDigest))
	// Output:
	// registry-1.docker.io library/nginx 1.27
	// nginx@sha256:0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef
}

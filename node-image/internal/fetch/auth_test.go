package fetch_test

import (
	"net/http"
	"net/http/httptest"
	"os"
	"path/filepath"
	"testing"

	"github.com/imjasonh/playground/node-image/internal/fetch"
)

func TestEnsureSendsAuthHeader(t *testing.T) {
	var gotAuth string
	srv := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		gotAuth = r.Header.Get("Authorization")
		// minimal gzip tar would fail SRI — we only check the request was authorized
		// before body validation by returning 401 without token.
		if gotAuth == "" {
			w.WriteHeader(http.StatusUnauthorized)
			return
		}
		w.WriteHeader(http.StatusUnauthorized)
	}))
	defer srv.Close()

	t.Setenv("NODE_AUTH_TOKEN", "secret-token")
	c := &fetch.Cache{Dir: t.TempDir()}
	_, err := c.Ensure(srv.URL+"/pkg.tgz", "sha512-AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA==")
	if err == nil {
		t.Fatal("expected integrity/status error")
	}
	if gotAuth != "Bearer secret-token" {
		t.Fatalf("auth=%q", gotAuth)
	}
}

func TestNPMRCTokenLookup(t *testing.T) {
	dir := t.TempDir()
	npmrc := filepath.Join(dir, ".npmrc")
	if err := os.WriteFile(npmrc, []byte("//registry.example.com/:_authToken=from-npmrc\n"), 0o600); err != nil {
		t.Fatal(err)
	}
	wd, _ := os.Getwd()
	if err := os.Chdir(dir); err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { _ = os.Chdir(wd) })

	req, _ := http.NewRequest(http.MethodGet, "https://registry.example.com/foo/-/foo-1.0.0.tgz", nil)
	t.Setenv("NODE_AUTH_TOKEN", "")
	t.Setenv("NPM_TOKEN", "")
	if err := fetch.DefaultNPMAuth(req); err != nil {
		t.Fatal(err)
	}
	if got := req.Header.Get("Authorization"); got != "Bearer from-npmrc" {
		t.Fatalf("got %q", got)
	}
}

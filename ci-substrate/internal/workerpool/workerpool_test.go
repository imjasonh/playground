package workerpool_test

import (
	"encoding/json"
	"encoding/pem"
	"io"
	"net"
	"net/http"
	"net/http/httptest"
	"os"
	"path/filepath"
	"strings"
	"sync"
	"testing"

	"github.com/imjasonh/playground/ci-substrate/internal/workerpool"
)

const scalePath = "/apis/ate.dev/v1/namespaces/ci-substrate-workers/workerpools/ci-runner/scale"

type fakeAPIServer struct {
	mu       sync.Mutex
	token    string
	replicas int
}

func (f *fakeAPIServer) ServeHTTP(w http.ResponseWriter, r *http.Request) {
	f.mu.Lock()
	defer f.mu.Unlock()
	if r.Header.Get("Authorization") != "Bearer "+f.token {
		http.Error(w, `{"reason":"Unauthorized"}`, http.StatusUnauthorized)
		return
	}
	if r.URL.Path != scalePath {
		http.NotFound(w, r)
		return
	}
	switch r.Method {
	case http.MethodGet:
	case http.MethodPatch:
		if ct := r.Header.Get("Content-Type"); ct != "application/merge-patch+json" {
			http.Error(w, "content type "+ct, http.StatusUnsupportedMediaType)
			return
		}
		var patch map[string]map[string]int
		b, _ := io.ReadAll(r.Body)
		if err := json.Unmarshal(b, &patch); err != nil || len(patch) != 1 || len(patch["spec"]) != 1 {
			http.Error(w, "patch "+string(b), http.StatusBadRequest)
			return
		}
		f.replicas = patch["spec"]["replicas"]
	default:
		http.Error(w, r.Method, http.StatusMethodNotAllowed)
		return
	}
	json.NewEncoder(w).Encode(map[string]any{
		"kind":   "Scale",
		"spec":   map[string]int{"replicas": f.replicas},
		"status": map[string]any{"replicas": f.replicas, "selector": "ate.dev/workerpool=ci-runner"},
	})
}

func newScaler(t *testing.T, api *fakeAPIServer) (*workerpool.Scaler, string) {
	t.Helper()
	srv := httptest.NewTLSServer(api)
	t.Cleanup(srv.Close)
	dir := t.TempDir()
	caFile := filepath.Join(dir, "ca.crt")
	if err := os.WriteFile(caFile, pem.EncodeToMemory(&pem.Block{Type: "CERTIFICATE", Bytes: srv.Certificate().Raw}), 0o600); err != nil {
		t.Fatal(err)
	}
	tokenFile := filepath.Join(dir, "token")
	if err := os.WriteFile(tokenFile, []byte(api.token+"\n"), 0o600); err != nil {
		t.Fatal(err)
	}
	host, port, err := net.SplitHostPort(strings.TrimPrefix(srv.URL, "https://"))
	if err != nil {
		t.Fatal(err)
	}
	s, err := workerpool.New(host, port, caFile, tokenFile, "ci-substrate-workers/ci-runner")
	if err != nil {
		t.Fatal(err)
	}
	return s, tokenFile
}

func TestReadsAndSetsReplicas(t *testing.T) {
	api := &fakeAPIServer{token: "first", replicas: 1}
	s, tokenFile := newScaler(t, api)
	if got, err := s.Replicas(t.Context()); err != nil || got != 1 {
		t.Fatalf("Replicas() = %d, %v; want 1", got, err)
	}
	if err := s.Scale(t.Context(), 0); err != nil {
		t.Fatal(err)
	}
	if got, err := s.Replicas(t.Context()); err != nil || got != 0 {
		t.Fatalf("Replicas() after Scale(0) = %d, %v; want 0", got, err)
	}
	// The kubelet rotates the projected token in place.
	api.mu.Lock()
	api.token = "second"
	api.mu.Unlock()
	if _, err := s.Replicas(t.Context()); err == nil || !strings.Contains(err.Error(), "401") {
		t.Fatalf("Replicas() with a stale token = %v, want 401", err)
	}
	if err := os.WriteFile(tokenFile, []byte("second"), 0o600); err != nil {
		t.Fatal(err)
	}
	if err := s.Scale(t.Context(), 3); err != nil {
		t.Fatal(err)
	}
	if api.replicas != 3 {
		t.Fatalf("replicas %d, want 3", api.replicas)
	}
}

func TestRejectsBadConfig(t *testing.T) {
	ca := filepath.Join(t.TempDir(), "ca.crt")
	if err := os.WriteFile(ca, []byte("not a certificate"), 0o600); err != nil {
		t.Fatal(err)
	}
	for _, tc := range []struct{ host, port, ca, pool string }{
		{"10.0.0.1", "443", ca, "ci-runner"},
		{"10.0.0.1", "443", ca, "ns/"},
		{"10.0.0.1", "443", ca, "a/b/c"},
		{"", "443", ca, "ns/ci-runner"},
		{"10.0.0.1", "443", ca, "ns/ci-runner"},
		{"10.0.0.1", "443", filepath.Join(t.TempDir(), "missing"), "ns/ci-runner"},
	} {
		if _, err := workerpool.New(tc.host, tc.port, tc.ca, "token", tc.pool); err == nil {
			t.Errorf("New(%q, %q, %q, %q) succeeded", tc.host, tc.port, tc.ca, tc.pool)
		}
	}
}

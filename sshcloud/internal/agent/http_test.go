package agent

import (
	"bytes"
	"encoding/json"
	"net/http"
	"net/http/httptest"
	"testing"

	"github.com/imjasonh/playground/sshcloud/internal/snapshot"
)

func TestHTTPSleepNotFound(t *testing.T) {
	dir := t.TempDir()
	store, err := snapshot.NewLocalStore(dir + "/snaps")
	if err != nil {
		t.Fatal(err)
	}
	mgr, err := NewManager(Config{
		WorkDir:     dir,
		KernelPath:  dir + "/vmlinux",
		BaseRootfs:  dir + "/rootfs.ext4",
		SnapStore:   store,
		IdleTimeout: 0,
	})
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { _ = mgr.Close() })

	mux := http.NewServeMux()
	(&Handler{Manager: mgr}).Mount(mux)

	body, _ := json.Marshal(map[string]string{"user": "alice", "app": "fortune"})
	req := httptest.NewRequest(http.MethodPost, "/v1/instances/sleep", bytes.NewReader(body))
	rec := httptest.NewRecorder()
	mux.ServeHTTP(rec, req)
	if rec.Code != http.StatusConflict {
		t.Fatalf("status %d body %s", rec.Code, rec.Body.String())
	}
}

func TestHTTPStatusNotFound(t *testing.T) {
	dir := t.TempDir()
	mgr, err := NewManager(Config{
		WorkDir:     dir,
		KernelPath:  dir + "/vmlinux",
		BaseRootfs:  dir + "/rootfs.ext4",
		IdleTimeout: 0,
	})
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { _ = mgr.Close() })

	mux := http.NewServeMux()
	(&Handler{Manager: mgr}).Mount(mux)

	req := httptest.NewRequest(http.MethodGet, "/v1/instances/status?user=alice&app=fortune", nil)
	rec := httptest.NewRecorder()
	mux.ServeHTTP(rec, req)
	if rec.Code != http.StatusNotFound {
		t.Fatalf("status %d", rec.Code)
	}
}

func TestHTTPEvictAdoptRoutes(t *testing.T) {
	dir := t.TempDir()
	store, err := snapshot.NewLocalStore(dir + "/snaps")
	if err != nil {
		t.Fatal(err)
	}
	mgr, err := NewManager(Config{
		WorkDir:     dir,
		KernelPath:  dir + "/vmlinux",
		BaseRootfs:  dir + "/rootfs.ext4",
		SnapStore:   store,
		IdleTimeout: 0,
	})
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { _ = mgr.Close() })

	mux := http.NewServeMux()
	(&Handler{Manager: mgr}).Mount(mux)

	body, _ := json.Marshal(map[string]string{"user": "alice", "app": "fortune"})
	req := httptest.NewRequest(http.MethodPost, "/v1/instances/evict", bytes.NewReader(body))
	rec := httptest.NewRecorder()
	mux.ServeHTTP(rec, req)
	if rec.Code != http.StatusNoContent {
		t.Fatalf("evict empty: %d %s", rec.Code, rec.Body.String())
	}

	req = httptest.NewRequest(http.MethodPost, "/v1/instances/adopt", bytes.NewReader(body))
	rec = httptest.NewRecorder()
	mux.ServeHTTP(rec, req)
	// No snapshot in store → 500, but route must exist (not 404).
	if rec.Code == http.StatusNotFound {
		t.Fatalf("adopt route missing")
	}
}

func TestHealthz(t *testing.T) {
	mux := http.NewServeMux()
	(&Handler{}).Mount(mux)
	req := httptest.NewRequest(http.MethodGet, "/healthz", nil)
	rec := httptest.NewRecorder()
	mux.ServeHTTP(rec, req)
	if rec.Code != http.StatusOK || rec.Body.String() != "ok" {
		t.Fatalf("%d %q", rec.Code, rec.Body.String())
	}
}

package agent

import (
	"bytes"
	"encoding/json"
	"net/http"
	"net/http/httptest"
	"strings"
	"testing"

	"github.com/imjasonh/playground/sshcloud/internal/firecracker"
	"github.com/imjasonh/playground/sshcloud/internal/snapshot"
)

func TestHTTPEnsureNoKVM(t *testing.T) {
	if firecracker.Available() {
		t.Skip("KVM available")
	}
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
	req := httptest.NewRequest(http.MethodPost, "/v1/instances/ensure", bytes.NewReader(body))
	rec := httptest.NewRecorder()
	mux.ServeHTTP(rec, req)
	if rec.Code != http.StatusInternalServerError {
		t.Fatalf("status %d body %s", rec.Code, rec.Body.String())
	}
	if !strings.Contains(rec.Body.String(), "/dev/kvm") {
		t.Fatalf("body: %s", rec.Body.String())
	}
}

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

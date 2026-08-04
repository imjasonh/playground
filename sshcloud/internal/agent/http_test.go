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

func TestHTTPEnsureRejectsUnpinnedImage(t *testing.T) {
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

	body, _ := json.Marshal(map[string]string{
		"user":  "alice",
		"app":   "myapp",
		"image": "ghcr.io/me/app:latest",
	})
	req := httptest.NewRequest(http.MethodPost, "/v1/instances/ensure", bytes.NewReader(body))
	rec := httptest.NewRecorder()
	mux.ServeHTTP(rec, req)
	if rec.Code != http.StatusBadRequest {
		t.Fatalf("status %d body %s", rec.Code, rec.Body.String())
	}
}

func TestHTTPEnsureImageRequiresResolver(t *testing.T) {
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

	digest := "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"
	body, _ := json.Marshal(map[string]string{
		"user":  "alice",
		"app":   "myapp",
		"image": "ghcr.io/me/app@sha256:" + digest,
	})
	req := httptest.NewRequest(http.MethodPost, "/v1/instances/ensure", bytes.NewReader(body))
	rec := httptest.NewRecorder()
	mux.ServeHTTP(rec, req)
	if rec.Code != http.StatusInternalServerError {
		t.Fatalf("status %d body %s", rec.Code, rec.Body.String())
	}
	if !bytes.Contains(rec.Body.Bytes(), []byte("RootfsResolver")) {
		t.Fatalf("body %s", rec.Body.String())
	}
}

func TestHTTPEnsureAcceptsGenNoIdle(t *testing.T) {
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
	mgr.mu.Lock()
	mgr.inst[InstanceKey{User: "alice", App: "myapp.gabc"}] = &Instance{
		Key:     InstanceKey{User: "alice", App: "myapp.gabc"},
		State:   StateRunning,
		Addr:    "10.0.0.2:22",
		machine: &stubMachine{},
	}
	mgr.mu.Unlock()

	mux := http.NewServeMux()
	(&Handler{Manager: mgr}).Mount(mux)

	body, _ := json.Marshal(map[string]any{
		"user": "alice", "app": "myapp", "gen": "gabc", "no_idle": true,
	})
	req := httptest.NewRequest(http.MethodPost, "/v1/instances/ensure", bytes.NewReader(body))
	rec := httptest.NewRecorder()
	mux.ServeHTTP(rec, req)
	if rec.Code != http.StatusOK {
		t.Fatalf("status %d body %s", rec.Code, rec.Body.String())
	}
	st, ok := mgr.Status("alice", "myapp.gabc")
	if !ok || st.State != StateRunning {
		t.Fatalf("status ok=%v %+v", ok, st)
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

func TestHTTPRejectsUnsafeIdentityAndUnknownFields(t *testing.T) {
	dir := t.TempDir()
	mgr, err := NewManager(Config{
		WorkDir:    dir,
		KernelPath: dir + "/vmlinux",
		BaseRootfs: dir + "/rootfs.ext4",
	})
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { _ = mgr.Close() })

	mux := http.NewServeMux()
	(&Handler{Manager: mgr}).Mount(mux)

	for name, body := range map[string]string{
		"path_traversal:": `{"user":"alice","app":"../bob/fortune"}`,
		"bad_generation":  `{"user":"alice","app":"fortune","gen":"../../g1"}`,
		"unknown_field":   `{"user":"alice","app":"fortune","owner":"bob"}`,
		"multiple_values": `{"user":"alice","app":"fortune"} {}`,
	} {
		t.Run(name, func(t *testing.T) {
			req := httptest.NewRequest(http.MethodPost, "/v1/instances/stop", bytes.NewBufferString(body))
			rec := httptest.NewRecorder()
			mux.ServeHTTP(rec, req)
			if rec.Code != http.StatusBadRequest {
				t.Fatalf("status %d body %s", rec.Code, rec.Body.String())
			}
		})
	}
}

func TestHTTPControlAuthentication(t *testing.T) {
	token := "0123456789abcdef0123456789abcdef"
	mux := http.NewServeMux()
	(&Handler{Token: token}).Mount(mux)

	req := httptest.NewRequest(http.MethodGet, "/v1/instances/status?user=alice&app=fortune", nil)
	rec := httptest.NewRecorder()
	mux.ServeHTTP(rec, req)
	if rec.Code != http.StatusUnauthorized {
		t.Fatalf("unauthenticated status %d", rec.Code)
	}

	req = httptest.NewRequest(http.MethodGet, "/healthz", nil)
	rec = httptest.NewRecorder()
	mux.ServeHTTP(rec, req)
	if rec.Code != http.StatusOK {
		t.Fatalf("health should remain public, got %d", rec.Code)
	}
}

func TestHTTPHostCapacityInventoryAndCordon(t *testing.T) {
	dir := t.TempDir()
	mgr, err := NewManager(Config{
		WorkDir: dir, KernelPath: dir + "/kernel", BaseRootfs: dir + "/rootfs",
		CapacityVCPUs: 4, CapacityMemMiB: 4096,
	})
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { _ = mgr.Close() })
	mgr.inst[InstanceKey{User: "alice", App: "myapp.gabc"}] = &Instance{
		Key: InstanceKey{User: "alice", App: "myapp.gabc"}, State: StateSleeping, Tier: "tiny",
	}
	mux := http.NewServeMux()
	(&Handler{Manager: mgr}).Mount(mux)

	req := httptest.NewRequest(http.MethodGet, "/v1/host/capacity", nil)
	rec := httptest.NewRecorder()
	mux.ServeHTTP(rec, req)
	if rec.Code != http.StatusOK || !bytes.Contains(rec.Body.Bytes(), []byte(`"vcpus":4`)) {
		t.Fatalf("capacity: %d %s", rec.Code, rec.Body.String())
	}
	req = httptest.NewRequest(http.MethodGet, "/v1/host/instances", nil)
	rec = httptest.NewRecorder()
	mux.ServeHTTP(rec, req)
	if rec.Code != http.StatusOK || !bytes.Contains(rec.Body.Bytes(), []byte(`"gen":"gabc"`)) {
		t.Fatalf("inventory: %d %s", rec.Code, rec.Body.String())
	}
	req = httptest.NewRequest(http.MethodPost, "/v1/host/cordon", bytes.NewReader([]byte(`{}`)))
	rec = httptest.NewRecorder()
	mux.ServeHTTP(rec, req)
	if rec.Code != http.StatusOK || !mgr.Capacity().Cordoned ||
		!bytes.Contains(rec.Body.Bytes(), []byte("cordon_epoch")) {
		t.Fatalf("cordon: %d %s %+v", rec.Code, rec.Body.String(), mgr.Capacity())
	}
}

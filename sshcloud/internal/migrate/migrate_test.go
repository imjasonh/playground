package migrate_test

import (
	"context"
	"encoding/json"
	"net/http"
	"net/http/httptest"
	"sync"
	"testing"

	"github.com/imjasonh/playground/sshcloud/internal/backend"
	"github.com/imjasonh/playground/sshcloud/internal/migrate"
	"github.com/imjasonh/playground/sshcloud/internal/placement"
)

// TestMigrateOrchestration drives Migrator against httptest agent stubs.
// This covers Sleep→Evict→Adopt + placement without faking Firecracker/KVM
// (real Firecracker migrate is TestKVMCrossHostMigrate).
func TestMigrateOrchestration(t *testing.T) {
	src := newStubAgent(t, "host-a")
	dst := newStubAgent(t, "host-b")
	src.ensure("alice", "fortune", "10.0.0.2:22")

	place := placement.NewMemory()
	ctx := context.Background()
	if err := place.Set(ctx, "alice", "fortune", "host-a"); err != nil {
		t.Fatal(err)
	}
	mig := &migrate.Migrator{
		Placement: place,
		Hosts: migrate.Hosts{
			"host-a": {BaseURL: src.URL},
			"host-b": {BaseURL: dst.URL},
		},
	}

	res, err := mig.Migrate(ctx, "alice", "fortune", "host-b")
	if err != nil {
		t.Fatal(err)
	}
	if res.FromHost != "host-a" || res.ToHost != "host-b" {
		t.Fatalf("hosts: %+v", res)
	}
	if res.Addr != "10.0.1.2:22" {
		t.Fatalf("addr: %s", res.Addr)
	}
	if !src.slept || !src.evicted {
		t.Fatalf("source actions: slept=%v evicted=%v", src.slept, src.evicted)
	}
	if !dst.adopted {
		t.Fatal("target did not adopt")
	}
	host, ok, err := place.Get(ctx, "alice", "fortune")
	if err != nil || !ok || host != "host-b" {
		t.Fatalf("placement: %q ok=%v err=%v", host, ok, err)
	}

	// Idempotent same-host migrate.
	res2, err := mig.Migrate(ctx, "alice", "fortune", "host-b")
	if err != nil {
		t.Fatal(err)
	}
	if res2.ToHost != "host-b" {
		t.Fatalf("re-migrate: %+v", res2)
	}
}

type stubAgent struct {
	URL      string
	mu       sync.Mutex
	inst     map[string]string // key → addr (running)
	sleeping map[string]bool
	slept    bool
	evicted  bool
	adopted  bool
}

func newStubAgent(t *testing.T, _ string) *stubAgent {
	t.Helper()
	s := &stubAgent{inst: make(map[string]string), sleeping: make(map[string]bool)}
	mux := http.NewServeMux()
	mux.HandleFunc("POST /v1/instances/ensure", s.handleEnsure)
	mux.HandleFunc("POST /v1/instances/sleep", s.handleSleep)
	mux.HandleFunc("POST /v1/instances/evict", s.handleEvict)
	mux.HandleFunc("POST /v1/instances/adopt", s.handleAdopt)
	mux.HandleFunc("GET /v1/instances/status", s.handleStatus)
	srv := httptest.NewServer(mux)
	t.Cleanup(srv.Close)
	s.URL = srv.URL
	return s
}

func (s *stubAgent) ensure(user, app, addr string) {
	s.mu.Lock()
	defer s.mu.Unlock()
	s.inst[user+"/"+app] = addr
}

func (s *stubAgent) key(r *http.Request) (string, bool) {
	var req struct {
		User string `json:"user"`
		App  string `json:"app"`
	}
	if err := json.NewDecoder(r.Body).Decode(&req); err != nil || req.User == "" || req.App == "" {
		return "", false
	}
	return req.User + "/" + req.App, true
}

func (s *stubAgent) handleEnsure(w http.ResponseWriter, r *http.Request) {
	k, ok := s.key(r)
	if !ok {
		http.Error(w, "bad request", http.StatusBadRequest)
		return
	}
	s.mu.Lock()
	defer s.mu.Unlock()
	addr, ok := s.inst[k]
	if !ok {
		http.Error(w, "not found", http.StatusInternalServerError)
		return
	}
	_ = json.NewEncoder(w).Encode(backend.InstanceView{Addr: addr, State: "running"})
}

func (s *stubAgent) handleSleep(w http.ResponseWriter, r *http.Request) {
	k, ok := s.key(r)
	if !ok {
		http.Error(w, "bad request", http.StatusBadRequest)
		return
	}
	s.mu.Lock()
	defer s.mu.Unlock()
	if _, ok := s.inst[k]; !ok {
		http.Error(w, "not found", http.StatusConflict)
		return
	}
	delete(s.inst, k)
	s.sleeping[k] = true
	s.slept = true
	_ = json.NewEncoder(w).Encode(map[string]string{"state": "sleeping"})
}

func (s *stubAgent) handleEvict(w http.ResponseWriter, r *http.Request) {
	k, ok := s.key(r)
	if !ok {
		http.Error(w, "bad request", http.StatusBadRequest)
		return
	}
	s.mu.Lock()
	defer s.mu.Unlock()
	delete(s.sleeping, k)
	delete(s.inst, k)
	s.evicted = true
	w.WriteHeader(http.StatusNoContent)
}

func (s *stubAgent) handleAdopt(w http.ResponseWriter, r *http.Request) {
	k, ok := s.key(r)
	if !ok {
		http.Error(w, "bad request", http.StatusBadRequest)
		return
	}
	s.mu.Lock()
	defer s.mu.Unlock()
	addr := "10.0.1.2:22"
	s.inst[k] = addr
	delete(s.sleeping, k)
	s.adopted = true
	_ = json.NewEncoder(w).Encode(backend.InstanceView{Addr: addr, State: "running"})
}

func (s *stubAgent) handleStatus(w http.ResponseWriter, r *http.Request) {
	user := r.URL.Query().Get("user")
	app := r.URL.Query().Get("app")
	k := user + "/" + app
	s.mu.Lock()
	defer s.mu.Unlock()
	if addr, ok := s.inst[k]; ok {
		_ = json.NewEncoder(w).Encode(backend.InstanceView{Addr: addr, State: "running"})
		return
	}
	if s.sleeping[k] {
		_ = json.NewEncoder(w).Encode(backend.InstanceView{State: "sleeping"})
		return
	}
	http.Error(w, "not found", http.StatusNotFound)
}

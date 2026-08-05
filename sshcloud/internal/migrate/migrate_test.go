package migrate_test

import (
	"context"
	"encoding/json"
	"net/http"
	"net/http/httptest"
	"strings"
	"sync"
	"testing"

	"github.com/imjasonh/playground/sshcloud/internal/agent"
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
		Hosts: backend.NewHostSet(map[string]*backend.AgentClient{
			"host-a": {BaseURL: src.URL, InsecureLoopback: true},
			"host-b": {BaseURL: dst.URL, InsecureLoopback: true},
		}, "host-a"),
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

func TestMigrateReconcilesAdoptAppliedBeforeCanceledResponse(t *testing.T) {
	t.Parallel()
	src := newStubAgent(t, "host-a")
	dst := newStubAgent(t, "host-b")
	src.ensure("alice", "fortune", "10.0.0.2:22")
	ctx, cancel := context.WithCancel(context.Background())
	dst.mu.Lock()
	dst.adoptResponseErr = true
	dst.cancelOnAdopt = cancel
	dst.mu.Unlock()

	place := placement.NewMemory()
	if err := place.Set(ctx, "alice", "fortune", "host-a"); err != nil {
		t.Fatal(err)
	}
	mig := &migrate.Migrator{
		Placement: place,
		Hosts: backend.NewHostSet(map[string]*backend.AgentClient{
			"host-a": {BaseURL: src.URL, InsecureLoopback: true},
			"host-b": {BaseURL: dst.URL, InsecureLoopback: true},
		}, "host-a"),
	}
	res, err := mig.Migrate(ctx, "alice", "fortune", "host-b")
	if err != nil {
		t.Fatalf("ambiguous adopt was not reconciled: %v", err)
	}
	if res.ToHost != "host-b" || res.Addr != "10.0.1.2:22" {
		t.Fatalf("result %+v", res)
	}
	host, ok, err := place.Get(context.Background(), "alice", "fortune")
	if err != nil || !ok || host != "host-b" {
		t.Fatalf("placement host=%q ok=%v err=%v", host, ok, err)
	}
	src.mu.Lock()
	_, sourceRunning := src.inst["alice/fortune"]
	src.mu.Unlock()
	if sourceRunning {
		t.Fatal("ambiguous target success created a second source copy")
	}
}

type stubAgent struct {
	URL              string
	mu               sync.Mutex
	inst             map[string]string // key → addr (running)
	sleeping         map[string]bool
	slept            bool
	evicted          bool
	adopted          bool
	adoptResponseErr bool
	cancelOnAdopt    context.CancelFunc
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
	mux.HandleFunc("GET /v1/host/instances", s.handleInstances)
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
	_ = json.NewEncoder(w).Encode(backend.InstanceView{Addr: addr, State: "running", SSHHostPublicKey: "test-host-key"})
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
	if s.cancelOnAdopt != nil {
		s.cancelOnAdopt()
	}
	if s.adoptResponseErr {
		http.Error(w, "injected response loss", http.StatusInternalServerError)
		return
	}
	_ = json.NewEncoder(w).Encode(backend.InstanceView{Addr: addr, State: "running", SSHHostPublicKey: "test-host-key"})
}

func (s *stubAgent) handleStatus(w http.ResponseWriter, r *http.Request) {
	user := r.URL.Query().Get("user")
	app := r.URL.Query().Get("app")
	k := user + "/" + app
	s.mu.Lock()
	defer s.mu.Unlock()
	if addr, ok := s.inst[k]; ok {
		_ = json.NewEncoder(w).Encode(backend.InstanceView{Addr: addr, State: "running", SSHHostPublicKey: "test-host-key"})
		return
	}
	if s.sleeping[k] {
		_ = json.NewEncoder(w).Encode(backend.InstanceView{State: "sleeping"})
		return
	}
	http.Error(w, "not found", http.StatusNotFound)
}

func (s *stubAgent) handleInstances(w http.ResponseWriter, _ *http.Request) {
	s.mu.Lock()
	defer s.mu.Unlock()
	var inventory []agent.InstanceInfo
	for key := range s.inst {
		parts := strings.SplitN(key, "/", 2)
		user, app := parts[0], parts[1]
		inventory = append(inventory, agent.InstanceInfo{
			User: user, App: app, State: agent.StateRunning, Tier: "tiny", SSHHostPublicKey: "test-host-key",
		})
	}
	for key := range s.sleeping {
		if _, running := s.inst[key]; running {
			continue
		}
		parts := strings.SplitN(key, "/", 2)
		inventory = append(inventory, agent.InstanceInfo{User: parts[0], App: parts[1], State: agent.StateSleeping, Tier: "tiny"})
	}
	_ = json.NewEncoder(w).Encode(map[string]any{"instances": inventory})
}

package reconcile_test

import (
	"context"
	"encoding/json"
	"net/http"
	"net/http/httptest"
	"sync"
	"testing"
	"time"

	"github.com/imjasonh/playground/sshcloud/internal/backend"
	"github.com/imjasonh/playground/sshcloud/internal/placement"
	"github.com/imjasonh/playground/sshcloud/internal/reconcile"
)

type reconcileHost struct {
	server *httptest.Server
	shared *sync.Map

	mu       sync.Mutex
	running  map[string]bool
	sleeping map[string]bool
	cordoned bool
}

func newReconcileHost(t *testing.T, shared *sync.Map) *reconcileHost {
	t.Helper()
	h := &reconcileHost{shared: shared, running: make(map[string]bool), sleeping: make(map[string]bool)}
	h.server = httptest.NewServer(http.HandlerFunc(h.serveHTTP))
	t.Cleanup(h.server.Close)
	return h
}

func (h *reconcileHost) client() *backend.AgentClient {
	return &backend.AgentClient{BaseURL: h.server.URL}
}

func (h *reconcileHost) serveHTTP(w http.ResponseWriter, r *http.Request) {
	var body struct {
		User string `json:"user"`
		App  string `json:"app"`
		Gen  string `json:"gen"`
	}
	if r.Method == http.MethodPost {
		_ = json.NewDecoder(r.Body).Decode(&body)
	}
	key := body.User + "/" + body.App + "." + body.Gen
	switch r.URL.Path {
	case "/v1/instances/status":
		key = r.URL.Query().Get("user") + "/" + r.URL.Query().Get("app") + "." + r.URL.Query().Get("gen")
		h.mu.Lock()
		running, sleeping := h.running[key], h.sleeping[key]
		h.mu.Unlock()
		switch {
		case running:
			_ = json.NewEncoder(w).Encode(backend.InstanceView{
				Addr: "127.0.0.1:22", State: "running", SSHHostPublicKey: "test-host-key",
			})
		case sleeping:
			_ = json.NewEncoder(w).Encode(backend.InstanceView{State: "sleeping"})
		default:
			http.Error(w, "not found", http.StatusNotFound)
		}
	case "/v1/instances/no-idle":
		w.WriteHeader(http.StatusNoContent)
	case "/v1/instances/sleep":
		h.mu.Lock()
		delete(h.running, key)
		h.sleeping[key] = true
		h.mu.Unlock()
		h.shared.Store(key, true)
		_ = json.NewEncoder(w).Encode(map[string]string{"state": "sleeping"})
	case "/v1/instances/evict":
		h.mu.Lock()
		delete(h.running, key)
		delete(h.sleeping, key)
		h.mu.Unlock()
		w.WriteHeader(http.StatusNoContent)
	case "/v1/instances/adopt":
		if _, ok := h.shared.Load(key); !ok {
			http.Error(w, "snapshot missing", http.StatusInternalServerError)
			return
		}
		h.mu.Lock()
		h.running[key] = true
		h.mu.Unlock()
		_ = json.NewEncoder(w).Encode(backend.InstanceView{Addr: "127.0.0.1:22", State: "running"})
	case "/v1/host/uncordon":
		h.mu.Lock()
		h.cordoned = false
		h.mu.Unlock()
		w.WriteHeader(http.StatusNoContent)
	default:
		http.NotFound(w, r)
	}
}

func TestExpiredOperationRollsTargetBackToAuthoritativeSource(t *testing.T) {
	t.Parallel()
	ctx := context.Background()
	var snapshots sync.Map
	source := newReconcileHost(t, &snapshots)
	target := newReconcileHost(t, &snapshots)
	key := "alice/myapp.gabc"
	target.running[key] = true

	store := placement.NewMemory()
	if err := store.Set(ctx, "alice", "myapp", "host-a"); err != nil {
		t.Fatal(err)
	}
	past := time.Now().Add(-time.Minute)
	lease, err := store.Acquire(ctx, "alice", "myapp", "crashed-drain", time.Second, past)
	if err != nil {
		t.Fatal(err)
	}
	if err := store.Mark(ctx, lease, placement.Operation{
		Kind: "drain", Phase: "unknown-adopt", SourceHost: "host-a",
		TargetHost: "host-b", Generations: []string{"gabc"},
	}); err != nil {
		t.Fatal(err)
	}
	controller := &reconcile.Controller{
		Placement: store,
		Hosts: backend.NewHostSet(map[string]*backend.AgentClient{
			"host-a": source.client(), "host-b": target.client(),
		}, "host-a"),
	}
	if err := controller.RunOnce(ctx); err != nil {
		t.Fatal(err)
	}
	source.mu.Lock()
	sourceRunning := source.running[key]
	source.mu.Unlock()
	target.mu.Lock()
	targetRunning := target.running[key]
	target.mu.Unlock()
	if !sourceRunning || targetRunning {
		t.Fatalf("source running=%v target running=%v", sourceRunning, targetRunning)
	}
	record, ok, err := store.GetRecord(ctx, "alice", "myapp")
	if err != nil || !ok || record.Operation.Kind != "" || record.LeaseOwner != "" || record.HostID != "host-a" {
		t.Fatalf("record %+v ok=%v err=%v", record, ok, err)
	}
}

func TestExpiredInitialEnsureCommitsPreparedTarget(t *testing.T) {
	t.Parallel()
	ctx := context.Background()
	var snapshots sync.Map
	target := newReconcileHost(t, &snapshots)
	key := "alice/myapp.gabc"
	target.running[key] = true
	store := placement.NewMemory()
	past := time.Now().Add(-time.Minute)
	lease, err := store.Acquire(ctx, "alice", "myapp", "crashed-ensure", time.Second, past)
	if err != nil {
		t.Fatal(err)
	}
	if err := store.Mark(ctx, lease, placement.Operation{
		ID: "ensure-op", Kind: "ensure", Phase: "ensuring", TargetHost: "host-b",
		Generations: []string{"gabc"},
		Desired: []placement.Generation{{
			Gen: "gabc", Image: "image", Tier: "tiny", State: "running", SSHHostPublicKey: "test-host-key",
		}},
	}); err != nil {
		t.Fatal(err)
	}
	controller := &reconcile.Controller{
		Placement: store,
		Hosts: backend.NewHostSet(map[string]*backend.AgentClient{
			"host-b": target.client(),
		}, "host-b"),
	}
	if err := controller.RunOnce(ctx); err != nil {
		t.Fatal(err)
	}
	record, ok, err := store.GetRecord(ctx, "alice", "myapp")
	if err != nil || !ok || record.HostID != "host-b" || record.Operation.Kind != "" ||
		len(record.Generations) != 1 {
		t.Fatalf("record %+v ok=%v err=%v", record, ok, err)
	}
}

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

	mu          sync.Mutex
	running     map[string]bool
	sleeping    map[string]bool
	stops       int
	sleeps      int
	registers   int
	cordoned    bool
	noIdleEpoch string
	sleepEpoch  string
}

func newReconcileHost(t *testing.T, shared *sync.Map) *reconcileHost {
	t.Helper()
	h := &reconcileHost{shared: shared, running: make(map[string]bool), sleeping: make(map[string]bool)}
	h.server = httptest.NewServer(http.HandlerFunc(h.serveHTTP))
	t.Cleanup(h.server.Close)
	return h
}

func (h *reconcileHost) client(instanceID ...string) *backend.AgentClient {
	id := ""
	if len(instanceID) != 0 {
		id = instanceID[0]
	}
	return &backend.AgentClient{
		BaseURL: h.server.URL, InstanceID: id, InsecureLoopback: true,
	}
}

func (h *reconcileHost) serveHTTP(w http.ResponseWriter, r *http.Request) {
	var body struct {
		User        string `json:"user"`
		App         string `json:"app"`
		Gen         string `json:"gen"`
		CordonEpoch string `json:"cordon_epoch"`
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
			_ = json.NewEncoder(w).Encode(backend.InstanceView{
				State: "sleeping", SSHHostPublicKey: "test-host-key",
			})
		default:
			http.Error(w, "not found", http.StatusNotFound)
		}
	case "/v1/instances/no-idle":
		h.mu.Lock()
		h.noIdleEpoch = body.CordonEpoch
		h.mu.Unlock()
		w.WriteHeader(http.StatusNoContent)
	case "/v1/instances/sleep":
		h.mu.Lock()
		delete(h.running, key)
		h.sleeping[key] = true
		h.sleeps++
		h.sleepEpoch = body.CordonEpoch
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
		delete(h.sleeping, key)
		h.running[key] = true
		h.mu.Unlock()
		_ = json.NewEncoder(w).Encode(backend.InstanceView{
			Addr: "127.0.0.1:22", State: "running", SSHHostPublicKey: "test-host-key",
		})
	case "/v1/instances/register-sleeping":
		if _, ok := h.shared.Load(key); !ok {
			http.Error(w, "snapshot missing", http.StatusInternalServerError)
			return
		}
		h.mu.Lock()
		h.sleeping[key] = true
		h.registers++
		h.mu.Unlock()
		_ = json.NewEncoder(w).Encode(map[string]any{
			"user": body.User, "app": body.App, "gen": body.Gen,
			"agent_app": body.App + "." + body.Gen, "tier": "tiny",
			"state": "sleeping", "ssh_host_public_key": "test-host-key",
		})
	case "/v1/instances/stop":
		h.mu.Lock()
		delete(h.running, key)
		delete(h.sleeping, key)
		h.stops++
		h.mu.Unlock()
		h.shared.Delete(key)
		w.WriteHeader(http.StatusNoContent)
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
	if err := store.SetIdentity(ctx, "alice", "myapp", "host-a", "local:host-a"); err != nil {
		t.Fatal(err)
	}
	inventoryLease, err := store.Acquire(ctx, "alice", "myapp", "inventory", time.Minute, time.Now())
	if err != nil {
		t.Fatal(err)
	}
	if err := store.CommitStateIdentity(
		ctx, inventoryLease, "host-a", "local:host-a",
		[]placement.Generation{{
			Gen: "gabc", Tier: "tiny", State: "running", SSHHostPublicKey: "test-host-key",
		}},
		time.Now(),
	); err != nil {
		t.Fatal(err)
	}
	past := time.Now().Add(-time.Minute)
	lease, err := store.Acquire(ctx, "alice", "myapp", "crashed-drain", time.Second, past)
	if err != nil {
		t.Fatal(err)
	}
	if err := store.Mark(ctx, lease, placement.Operation{
		Kind: "drain", Phase: "unknown-adopt", SourceHost: "host-a",
		SourceInstanceID: "local:host-a", TargetHost: "host-b",
		TargetInstanceID: "local:host-b", Generations: []string{"gabc"},
	}); err != nil {
		t.Fatal(err)
	}
	controller := &reconcile.Controller{
		Placement: store,
		Hosts: backend.NewHostSet(map[string]*backend.AgentClient{
			"host-a": source.client("local:host-a"), "host-b": target.client("local:host-b"),
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
		TargetInstanceID: "local:host-b", Generations: []string{"gabc"},
		Desired: []placement.Generation{{
			Gen: "gabc", Image: "image", Tier: "tiny", State: "running", SSHHostPublicKey: "test-host-key",
		}},
	}); err != nil {
		t.Fatal(err)
	}
	controller := &reconcile.Controller{
		Placement: store,
		Hosts: backend.NewHostSet(map[string]*backend.AgentClient{
			"host-b": target.client("local:host-b"),
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

func TestExpiredEnsureCommitsVerifiedActualInventory(t *testing.T) {
	t.Parallel()
	ctx := t.Context()
	var snapshots sync.Map
	target := newReconcileHost(t, &snapshots)
	sleepingKey := "alice/myapp.gabc"
	runningKey := "alice/myapp.gabd"
	snapshots.Store(sleepingKey, true)
	target.running[runningKey] = true

	store := placement.NewMemory()
	if err := store.SetIdentity(ctx, "alice", "myapp", "host-b", "202"); err != nil {
		t.Fatal(err)
	}
	inventory, err := store.Acquire(ctx, "alice", "myapp", "inventory", time.Minute, time.Now())
	if err != nil {
		t.Fatal(err)
	}
	existing := placement.Generation{
		Gen: "gabc", Image: "old-image", Tier: "tiny", State: "sleeping",
		SSHHostPublicKey: "test-host-key",
	}
	if err := store.CommitStateIdentity(
		ctx,
		inventory,
		"host-b",
		"202",
		[]placement.Generation{existing},
		time.Now(),
	); err != nil {
		t.Fatal(err)
	}
	desired := []placement.Generation{
		existing,
		{
			Gen: "gabd", Image: "new-image", Tier: "tiny", State: "running",
			SSHHostPublicKey: "test-host-key",
		},
	}
	past := time.Now().Add(-time.Minute)
	lease, err := store.Acquire(ctx, "alice", "myapp", "crashed-ensure", time.Second, past)
	if err != nil {
		t.Fatal(err)
	}
	if err := store.Mark(ctx, lease, placement.Operation{
		ID: "ensure-actual", Kind: "ensure", Phase: "ready",
		TargetHost: "host-b", TargetInstanceID: "202",
		Generations: []string{"gabd"}, Desired: desired,
	}); err != nil {
		t.Fatal(err)
	}
	controller := &reconcile.Controller{
		Placement: store,
		Hosts: backend.NewHostSet(map[string]*backend.AgentClient{
			"host-b": target.client("202"),
		}, "host-b"),
	}
	if err := controller.RunOnce(ctx); err != nil {
		t.Fatal(err)
	}
	target.mu.Lock()
	sleeping, registers := target.sleeping[sleepingKey], target.registers
	target.mu.Unlock()
	if !sleeping || registers != 1 {
		t.Fatalf("sleeping=%v registrations=%d", sleeping, registers)
	}
	record, ok, err := store.GetRecord(ctx, "alice", "myapp")
	if err != nil || !ok || len(record.Generations) != 2 ||
		record.Generations[0].State != "sleeping" ||
		record.Generations[1].State != "running" {
		t.Fatalf("record %+v ok=%v err=%v", record, ok, err)
	}
}

func TestExpiredEnsureRegistersDesiredSleepingWithoutWake(t *testing.T) {
	t.Parallel()
	ctx := t.Context()
	var snapshots sync.Map
	target := newReconcileHost(t, &snapshots)
	key := "alice/myapp.gab"
	snapshots.Store(key, true)
	store := placement.NewMemory()
	past := time.Now().Add(-time.Minute)
	lease, err := store.Acquire(ctx, "alice", "myapp", "crashed-ensure", time.Second, past)
	if err != nil {
		t.Fatal(err)
	}
	desired := []placement.Generation{{
		Gen: "gab", Image: "image", Tier: "tiny", State: "sleeping",
		SSHHostPublicKey: "test-host-key",
	}}
	if err := store.Mark(ctx, lease, placement.Operation{
		ID: "ensure-sleep", Kind: "ensure", Phase: "registering",
		TargetHost: "host-b", TargetInstanceID: "202",
		Generations: []string{"gab"}, Desired: desired,
	}); err != nil {
		t.Fatal(err)
	}
	controller := &reconcile.Controller{
		Placement: store,
		Hosts: backend.NewHostSet(map[string]*backend.AgentClient{
			"host-b": target.client("202"),
		}, "host-b"),
	}
	if err := controller.RunOnce(ctx); err != nil {
		t.Fatal(err)
	}
	target.mu.Lock()
	running, sleeping, registers := target.running[key], target.sleeping[key], target.registers
	target.mu.Unlock()
	if running || !sleeping || registers != 1 {
		t.Fatalf("running=%v sleeping=%v registers=%d", running, sleeping, registers)
	}
	record, ok, err := store.GetRecord(ctx, "alice", "myapp")
	if err != nil || !ok || record.HostInstanceID != "202" ||
		len(record.Generations) != 1 || record.Generations[0].State != "sleeping" {
		t.Fatalf("record %+v ok=%v err=%v", record, ok, err)
	}
}

func TestExpiredMoveSleepsUnexpectedRunningSourceAndCommitsActualState(t *testing.T) {
	t.Parallel()
	ctx := t.Context()
	var snapshots sync.Map
	source := newReconcileHost(t, &snapshots)
	target := newReconcileHost(t, &snapshots)
	key := "alice/myapp.gab"
	source.running[key] = true
	store := placement.NewMemory()
	if err := store.SetIdentity(ctx, "alice", "myapp", "host-a", "101"); err != nil {
		t.Fatal(err)
	}
	inventory, err := store.Acquire(ctx, "alice", "myapp", "inventory", time.Minute, time.Now())
	if err != nil {
		t.Fatal(err)
	}
	desired := []placement.Generation{{
		Gen: "gab", Image: "image", Tier: "tiny", State: "sleeping",
		SSHHostPublicKey: "test-host-key",
	}}
	if err := store.CommitStateIdentity(ctx, inventory, "host-a", "101", desired, time.Now()); err != nil {
		t.Fatal(err)
	}
	past := time.Now().Add(-time.Minute)
	lease, err := store.Acquire(ctx, "alice", "myapp", "crashed-drain", time.Second, past)
	if err != nil {
		t.Fatal(err)
	}
	if err := store.Mark(ctx, lease, placement.Operation{
		ID: "move-sleep", Kind: "drain", Phase: "unknown",
		SourceHost: "host-a", SourceInstanceID: "101", SourceEpoch: "cordon-a",
		TargetHost: "host-b", TargetInstanceID: "202",
		Generations: []string{"gab"}, Desired: desired,
	}); err != nil {
		t.Fatal(err)
	}
	controller := &reconcile.Controller{
		Placement: store,
		Hosts: backend.NewHostSet(map[string]*backend.AgentClient{
			"host-a": source.client("101"), "host-b": target.client("202"),
		}, "host-a"),
	}
	if err := controller.RunOnce(ctx); err != nil {
		t.Fatal(err)
	}
	source.mu.Lock()
	running, sleeping, sleeps := source.running[key], source.sleeping[key], source.sleeps
	noIdleEpoch, sleepEpoch := source.noIdleEpoch, source.sleepEpoch
	source.mu.Unlock()
	if running || !sleeping || sleeps != 1 ||
		noIdleEpoch != "cordon-a" || sleepEpoch != "cordon-a" {
		t.Fatalf(
			"running=%v sleeping=%v sleeps=%d no-idle epoch=%q sleep epoch=%q",
			running, sleeping, sleeps, noIdleEpoch, sleepEpoch,
		)
	}
	record, _, err := store.GetRecord(ctx, "alice", "myapp")
	if err != nil || record.Operation.Kind != "" ||
		len(record.Generations) != 1 || record.Generations[0].State != "sleeping" {
		t.Fatalf("record %+v err=%v", record, err)
	}
}

func TestExpiredStopJournalRetriesExactSourceAndCommits(t *testing.T) {
	t.Parallel()
	ctx := t.Context()
	var snapshots sync.Map
	source := newReconcileHost(t, &snapshots)
	key := "alice/myapp.g0e"
	source.running[key] = true
	snapshots.Store(key, true)
	store := placement.NewMemory()
	if err := store.SetIdentity(ctx, "alice", "myapp", "host-a", "101"); err != nil {
		t.Fatal(err)
	}
	inventory, err := store.Acquire(ctx, "alice", "myapp", "inventory", time.Minute, time.Now())
	if err != nil {
		t.Fatal(err)
	}
	if err := store.CommitStateIdentity(ctx, inventory, "host-a", "101", []placement.Generation{{
		Gen: "g0e", Tier: "tiny", State: "running", SSHHostPublicKey: "test-host-key",
	}}, time.Now()); err != nil {
		t.Fatal(err)
	}
	past := time.Now().Add(-time.Minute)
	lease, err := store.Acquire(ctx, "alice", "myapp", "crashed-stop", time.Second, past)
	if err != nil {
		t.Fatal(err)
	}
	if err := store.Mark(ctx, lease, placement.Operation{
		ID: "stop-1", Kind: "stop", Phase: "unknown-stop",
		SourceHost: "host-a", SourceInstanceID: "101",
		Generations: []string{"g0e"},
	}); err != nil {
		t.Fatal(err)
	}
	controller := &reconcile.Controller{
		Placement: store,
		Hosts: backend.NewHostSet(map[string]*backend.AgentClient{
			"host-a": source.client("101"),
		}, "host-a"),
	}
	if err := controller.RunOnce(ctx); err != nil {
		t.Fatal(err)
	}
	source.mu.Lock()
	stops := source.stops
	source.mu.Unlock()
	record, _, err := store.GetRecord(ctx, "alice", "myapp")
	if err != nil || stops != 1 || record.Operation.Kind != "" || len(record.Generations) != 0 {
		t.Fatalf("stops=%d record=%+v err=%v", stops, record, err)
	}
}

func TestRecoveryRefusesReplacementParticipantIncarnations(t *testing.T) {
	t.Parallel()
	ctx := t.Context()
	var snapshots sync.Map
	source := newReconcileHost(t, &snapshots)
	target := newReconcileHost(t, &snapshots)
	store := placement.NewMemory()
	if err := store.SetIdentity(ctx, "alice", "myapp", "host-a", "old-source"); err != nil {
		t.Fatal(err)
	}
	past := time.Now().Add(-time.Minute)
	lease, err := store.Acquire(ctx, "alice", "myapp", "crashed-drain", time.Second, past)
	if err != nil {
		t.Fatal(err)
	}
	if err := store.Mark(ctx, lease, placement.Operation{
		ID: "move-1", Kind: "drain", SourceHost: "host-a",
		SourceInstanceID: "old-source", TargetHost: "host-b",
		TargetInstanceID: "old-target", Generations: []string{"gabc"},
	}); err != nil {
		t.Fatal(err)
	}
	controller := &reconcile.Controller{
		Placement: store,
		Hosts: backend.NewHostSet(map[string]*backend.AgentClient{
			"host-a": source.client("new-source"), "host-b": target.client("new-target"),
		}, "host-a"),
	}
	if err := controller.RunOnce(ctx); err == nil {
		t.Fatal("replacement incarnations were accepted")
	}
	record, _, err := store.GetRecord(ctx, "alice", "myapp")
	if err != nil || record.Operation.ID != "move-1" {
		t.Fatalf("journal was not retained: %+v err=%v", record, err)
	}
}

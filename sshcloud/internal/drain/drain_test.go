package drain_test

import (
	"context"
	"encoding/json"
	"fmt"
	"net/http"
	"net/http/httptest"
	"sync"
	"testing"
	"time"

	"github.com/imjasonh/playground/sshcloud/internal/agent"
	"github.com/imjasonh/playground/sshcloud/internal/backend"
	"github.com/imjasonh/playground/sshcloud/internal/drain"
	"github.com/imjasonh/playground/sshcloud/internal/genid"
	"github.com/imjasonh/playground/sshcloud/internal/placement"
)

type drainSnapshotSet struct {
	mu    sync.Mutex
	items map[string]agent.InstanceInfo
}

type drainHost struct {
	server    *httptest.Server
	snapshots *drainSnapshotSet

	mu        sync.Mutex
	cordoned  bool
	instances map[string]agent.InstanceInfo
	total     agent.Resources
}

func newDrainHost(t *testing.T, snapshots *drainSnapshotSet, total agent.Resources) *drainHost {
	t.Helper()
	h := &drainHost{snapshots: snapshots, instances: make(map[string]agent.InstanceInfo), total: total}
	h.server = httptest.NewServer(http.HandlerFunc(h.serveHTTP))
	t.Cleanup(h.server.Close)
	return h
}

func (h *drainHost) client() *backend.AgentClient {
	return &backend.AgentClient{BaseURL: h.server.URL, InsecureLoopback: true}
}

func (h *drainHost) add(info agent.InstanceInfo) {
	h.mu.Lock()
	defer h.mu.Unlock()
	info.AgentApp = genid.AgentApp(info.App, info.Gen)
	if info.SSHHostPublicKey == "" {
		info.SSHHostPublicKey = "test-host-key-" + info.Gen
	}
	h.instances[info.User+"/"+info.AgentApp] = info
}

func (h *drainHost) serveHTTP(w http.ResponseWriter, r *http.Request) {
	switch r.URL.Path {
	case "/v1/host/capacity":
		h.mu.Lock()
		used := agent.Resources{}
		for _, info := range h.instances {
			if info.State == agent.StateRunning {
				resources, _ := agent.ResourcesForTier(info.Tier)
				used.VCPUs += resources.VCPUs
				used.MemMiB += resources.MemMiB
			}
		}
		response := agent.Capacity{Total: h.total, Used: used, Cordoned: h.cordoned}
		h.mu.Unlock()
		_ = json.NewEncoder(w).Encode(response)
	case "/v1/host/instances":
		h.mu.Lock()
		var inventory []agent.InstanceInfo
		for _, info := range h.instances {
			inventory = append(inventory, info)
		}
		h.mu.Unlock()
		_ = json.NewEncoder(w).Encode(map[string]any{"instances": inventory})
	case "/v1/host/cordon":
		h.mu.Lock()
		h.cordoned = true
		h.mu.Unlock()
		_ = json.NewEncoder(w).Encode(map[string]string{"cordon_epoch": "gcordon"})
	case "/v1/host/uncordon":
		h.mu.Lock()
		h.cordoned = false
		h.mu.Unlock()
		w.WriteHeader(http.StatusNoContent)
	case "/v1/instances/no-idle":
		req, key, ok := decodeDrainInstance(r)
		if !ok {
			http.Error(w, "bad request", http.StatusBadRequest)
			return
		}
		h.mu.Lock()
		info, exists := h.instances[key]
		if exists {
			info.NoIdle = req.NoIdle
			h.instances[key] = info
		}
		h.mu.Unlock()
		w.WriteHeader(http.StatusNoContent)
	case "/v1/instances/sleep":
		_, key, ok := decodeDrainInstance(r)
		if !ok {
			http.Error(w, "bad request", http.StatusBadRequest)
			return
		}
		h.mu.Lock()
		info, exists := h.instances[key]
		if !exists || info.NoIdle {
			h.mu.Unlock()
			http.Error(w, "not sleepable", http.StatusConflict)
			return
		}
		info.State = agent.StateSleeping
		h.instances[key] = info
		h.mu.Unlock()
		h.snapshots.mu.Lock()
		h.snapshots.items[key] = info
		h.snapshots.mu.Unlock()
		_ = json.NewEncoder(w).Encode(map[string]string{"state": "sleeping"})
	case "/v1/instances/evict":
		_, key, ok := decodeDrainInstance(r)
		if !ok {
			http.Error(w, "bad request", http.StatusBadRequest)
			return
		}
		h.mu.Lock()
		info, exists := h.instances[key]
		if exists && info.State == agent.StateRunning {
			h.mu.Unlock()
			http.Error(w, "still running", http.StatusConflict)
			return
		}
		delete(h.instances, key)
		h.mu.Unlock()
		w.WriteHeader(http.StatusNoContent)
	case "/v1/instances/adopt":
		_, key, ok := decodeDrainInstance(r)
		if !ok {
			http.Error(w, "bad request", http.StatusBadRequest)
			return
		}
		h.snapshots.mu.Lock()
		info, exists := h.snapshots.items[key]
		h.snapshots.mu.Unlock()
		if !exists {
			http.Error(w, "snapshot missing", http.StatusInternalServerError)
			return
		}
		info.State, info.NoIdle = agent.StateRunning, false
		h.mu.Lock()
		h.instances[key] = info
		h.mu.Unlock()
		_ = json.NewEncoder(w).Encode(backend.InstanceView{
			Addr: "127.0.0.1:2222", State: "running", SSHHostPublicKey: info.SSHHostPublicKey,
		})
	case "/v1/instances/preflight":
		_, key, ok := decodeDrainInstance(r)
		if !ok {
			http.Error(w, "bad request", http.StatusBadRequest)
			return
		}
		h.snapshots.mu.Lock()
		info, exists := h.snapshots.items[key]
		h.snapshots.mu.Unlock()
		if !exists {
			http.Error(w, "snapshot missing", http.StatusInternalServerError)
			return
		}
		_ = json.NewEncoder(w).Encode(info)
	case "/v1/instances/register-sleeping":
		_, key, ok := decodeDrainInstance(r)
		if !ok {
			http.Error(w, "bad request", http.StatusBadRequest)
			return
		}
		h.snapshots.mu.Lock()
		info, exists := h.snapshots.items[key]
		h.snapshots.mu.Unlock()
		if !exists {
			http.Error(w, "snapshot missing", http.StatusInternalServerError)
			return
		}
		info.State = agent.StateSleeping
		h.mu.Lock()
		if h.cordoned {
			h.mu.Unlock()
			http.Error(w, "host cordoned", http.StatusServiceUnavailable)
			return
		}
		h.instances[key] = info
		h.mu.Unlock()
		_ = json.NewEncoder(w).Encode(info)
	default:
		http.NotFound(w, r)
	}
}

type drainInstanceRequest struct {
	User   string `json:"user"`
	App    string `json:"app"`
	Gen    string `json:"gen"`
	NoIdle bool   `json:"no_idle"`
}

func decodeDrainInstance(r *http.Request) (drainInstanceRequest, string, bool) {
	var req drainInstanceRequest
	if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
		return req, "", false
	}
	return req, req.User + "/" + genid.AgentApp(req.App, req.Gen), req.User != "" && req.App != ""
}

type drainGateway struct {
	server *httptest.Server
	mu     sync.Mutex
	frozen []string
	thawed []string
}

func newDrainGateway(t *testing.T) *drainGateway {
	t.Helper()
	g := &drainGateway{}
	g.server = httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		var body map[string]any
		_ = json.NewDecoder(r.Body).Decode(&body)
		switch r.URL.Path {
		case "/v1/sessions/freeze":
			gen, _ := body["gen"].(string)
			token := "token-" + gen
			g.mu.Lock()
			g.frozen = append(g.frozen, gen)
			g.mu.Unlock()
			_ = json.NewEncoder(w).Encode(map[string]any{"token": token, "sessions": 1})
		case "/v1/sessions/thaw":
			token, _ := body["token"].(string)
			g.mu.Lock()
			g.thawed = append(g.thawed, token)
			g.mu.Unlock()
			_ = json.NewEncoder(w).Encode(map[string]int{"sessions": 1})
		default:
			http.NotFound(w, r)
		}
	}))
	t.Cleanup(g.server.Close)
	return g
}

func TestDrainHostMovesRunningAndSleepingGenerations(t *testing.T) {
	t.Parallel()
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()
	snapshots := &drainSnapshotSet{items: make(map[string]agent.InstanceInfo)}
	source := newDrainHost(t, snapshots, agent.Resources{VCPUs: 4, MemMiB: 4096})
	target := newDrainHost(t, snapshots, agent.Resources{VCPUs: 4, MemMiB: 4096})
	source.add(agent.InstanceInfo{
		User: "alice", App: "myapp", Gen: "gactive", Image: "image", Tier: "tiny",
		State: agent.StateRunning, NoIdle: true,
	})
	sleeping := agent.InstanceInfo{
		User: "alice", App: "myapp", Gen: "gold", Image: "image", Tier: "tiny",
		State: agent.StateSleeping, SSHHostPublicKey: "test-host-key-gold",
	}
	source.add(sleeping)
	snapshots.items["alice/"+genid.AgentApp("myapp", "gold")] = sleeping

	place := placement.NewMemory()
	if err := place.Set(ctx, "alice", "myapp", "host-a"); err != nil {
		t.Fatal(err)
	}
	gateway := newDrainGateway(t)
	controller := &drain.Controller{
		Placement: place,
		Hosts: backend.NewHostSet(map[string]*backend.AgentClient{
			"host-a": source.client(), "host-b": target.client(),
		}, "host-a"),
		Gateway:      &backend.GatewayClient{BaseURL: gateway.server.URL, InsecureLoopback: true},
		FreezeWindow: time.Second,
	}
	result, err := controller.DrainHost(ctx, "host-a")
	if err != nil {
		t.Fatal(err)
	}
	if len(result.Moved) != 1 || result.Moved[0].Target != "host-b" || len(result.Moved[0].Gens) != 2 {
		t.Fatalf("result %+v", result)
	}
	host, ok, err := place.Get(ctx, "alice", "myapp")
	if err != nil || !ok || host != "host-b" {
		t.Fatalf("placement host=%q ok=%v err=%v", host, ok, err)
	}
	source.mu.Lock()
	sourceCount, cordoned := len(source.instances), source.cordoned
	source.mu.Unlock()
	if sourceCount != 0 || !cordoned {
		t.Fatalf("source instances=%d cordoned=%v", sourceCount, cordoned)
	}
	target.mu.Lock()
	_, activeMoved := target.instances["alice/"+genid.AgentApp("myapp", "gactive")]
	target.mu.Unlock()
	if !activeMoved {
		t.Fatal("running generation was not adopted on target")
	}
	gateway.mu.Lock()
	defer gateway.mu.Unlock()
	if fmt.Sprint(gateway.frozen) != "[gactive]" || fmt.Sprint(gateway.thawed) != "[token-gactive]" {
		t.Fatalf("gateway frozen=%v thawed=%v", gateway.frozen, gateway.thawed)
	}
}

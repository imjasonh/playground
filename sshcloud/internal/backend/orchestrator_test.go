package backend_test

import (
	"encoding/json"
	"net/http"
	"net/http/httptest"
	"testing"

	"github.com/imjasonh/playground/sshcloud/internal/backend"
	"github.com/imjasonh/playground/sshcloud/internal/placement"
)

func TestOrchestratorClientAddr(t *testing.T) {
	place := placement.NewMemory()
	agents := map[string]*backend.AgentClient{}

	agent := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		if r.URL.Path != "/v1/instances/ensure" {
			http.NotFound(w, r)
			return
		}
		_ = json.NewEncoder(w).Encode(map[string]string{
			"addr":     "10.0.0.2:22",
			"guest_ip": "10.0.0.2",
			"state":    "running",
		})
	}))
	t.Cleanup(agent.Close)
	agents["host-a"] = &backend.AgentClient{BaseURL: agent.URL}

	dial := &backend.PlacedDial{
		Placement:   place,
		Agents:      agents,
		DefaultHost: "host-a",
	}
	orch := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		if r.URL.Path != "/v1/ensure" {
			http.NotFound(w, r)
			return
		}
		var req struct {
			User string `json:"user"`
			App  string `json:"app"`
		}
		if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
			http.Error(w, err.Error(), 400)
			return
		}
		addr, err := dial.Addr(req.User, req.App)
		if err != nil {
			http.Error(w, err.Error(), 500)
			return
		}
		_ = json.NewEncoder(w).Encode(map[string]string{"addr": addr})
	}))
	t.Cleanup(orch.Close)

	c := &backend.OrchestratorClient{BaseURL: orch.URL}
	addr, err := c.Addr("alice", "fortune")
	if err != nil {
		t.Fatal(err)
	}
	if addr != "10.0.0.2:22" {
		t.Fatalf("addr = %q", addr)
	}
	host, ok, err := place.Get(t.Context(), "alice", "fortune")
	if err != nil || !ok || host != "host-a" {
		t.Fatalf("placement: host=%q ok=%v err=%v", host, ok, err)
	}
}

func TestPlacedDialUnknownHost(t *testing.T) {
	place := placement.NewMemory()
	_ = place.Set(t.Context(), "alice", "fortune", "missing")
	dial := &backend.PlacedDial{
		Placement: place,
		Agents:    map[string]*backend.AgentClient{},
	}
	if _, err := dial.Addr("alice", "fortune"); err == nil {
		t.Fatal("expected error for unknown host")
	}
}

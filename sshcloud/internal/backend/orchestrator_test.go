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

	var got struct {
		User   string
		App    string
		Gen    string
		Image  string
		NoIdle bool
	}
	agent := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		if r.URL.Path != "/v1/instances/ensure" {
			http.NotFound(w, r)
			return
		}
		var req struct {
			User   string `json:"user"`
			App    string `json:"app"`
			Gen    string `json:"gen"`
			Image  string `json:"image"`
			NoIdle bool   `json:"no_idle"`
		}
		if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
			http.Error(w, err.Error(), 400)
			return
		}
		got.User, got.App, got.Gen, got.Image, got.NoIdle = req.User, req.App, req.Gen, req.Image, req.NoIdle
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
		Agents:      backend.NewHostSet(agents, "host-a"),
		DefaultHost: "host-a",
	}
	orch := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		switch r.URL.Path {
		case "/v1/ensure":
			var req struct {
				User   string `json:"user"`
				App    string `json:"app"`
				Gen    string `json:"gen"`
				Image  string `json:"image"`
				NoIdle bool   `json:"no_idle"`
			}
			if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
				http.Error(w, err.Error(), 400)
				return
			}
			addr, err := dial.EnsureAddr(r.Context(), req.User, req.App, req.Gen, req.Image, req.NoIdle)
			if err != nil {
				http.Error(w, err.Error(), 500)
				return
			}
			_ = json.NewEncoder(w).Encode(map[string]string{"addr": addr})
		case "/v1/stop":
			var req struct {
				User string `json:"user"`
				App  string `json:"app"`
				Gen  string `json:"gen"`
			}
			_ = json.NewDecoder(r.Body).Decode(&req)
			if err := dial.Stop(r.Context(), req.User, req.App, req.Gen); err != nil {
				http.Error(w, err.Error(), 500)
				return
			}
			w.WriteHeader(http.StatusNoContent)
		default:
			http.NotFound(w, r)
		}
	}))
	t.Cleanup(orch.Close)

	c := &backend.OrchestratorClient{BaseURL: orch.URL}
	digest := "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"
	addr, err := c.Addr("alice", "fortune", "gabc", "ghcr.io/me/app@sha256:"+digest)
	if err != nil {
		t.Fatal(err)
	}
	if addr != "10.0.0.2:22" {
		t.Fatalf("addr = %q", addr)
	}
	if got.User != "alice" || got.App != "fortune" || got.Gen != "gabc" {
		t.Fatalf("agent body %+v", got)
	}
	host, ok, err := place.Get(t.Context(), "alice", "fortune")
	if err != nil || !ok || host != "host-a" {
		t.Fatalf("placement: host=%q ok=%v err=%v", host, ok, err)
	}

	if err := c.Ensure(t.Context(), "alice", "fortune", "gdef", "", true); err != nil {
		t.Fatal(err)
	}
	if !got.NoIdle || got.Gen != "gdef" {
		t.Fatalf("no_idle ensure %+v", got)
	}
}

func TestPlacedDialUnknownHost(t *testing.T) {
	place := placement.NewMemory()
	_ = place.Set(t.Context(), "alice", "fortune", "missing")
	dial := &backend.PlacedDial{
		Placement: place,
		Agents:    backend.NewHostSet(map[string]*backend.AgentClient{}, ""),
	}
	if _, err := dial.Addr("alice", "fortune", "", ""); err == nil {
		t.Fatal("expected error for unknown host")
	}
}

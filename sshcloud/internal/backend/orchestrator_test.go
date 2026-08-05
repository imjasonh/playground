package backend_test

import (
	"encoding/json"
	"errors"
	"net/http"
	"net/http/httptest"
	"testing"

	"github.com/imjasonh/playground/sshcloud/internal/agent"
	"github.com/imjasonh/playground/sshcloud/internal/backend"
	"github.com/imjasonh/playground/sshcloud/internal/placement"
	"github.com/imjasonh/playground/sshcloud/internal/quota"
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
		if r.URL.Path == "/v1/host/capacity" {
			_ = json.NewEncoder(w).Encode(map[string]any{
				"total":    map[string]int{"vcpus": 4, "mem_mib": 4096},
				"used":     map[string]int{"vcpus": 0, "mem_mib": 0},
				"reserved": map[string]int{"vcpus": 0, "mem_mib": 0},
			})
			return
		}
		if r.URL.Path == "/v1/host/instances" {
			_ = json.NewEncoder(w).Encode(map[string]any{"instances": []agent.InstanceInfo{}})
			return
		}
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
			"addr": "10.0.0.2:22", "guest_ip": "10.0.0.2", "state": "running",
			"ssh_host_public_key": "test-host-key",
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
			_ = json.NewEncoder(w).Encode(map[string]string{
				"addr": addr, "ssh_host_public_key": "test-host-key",
			})
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

	if err := c.Ensure(t.Context(), "alice", "fortune", "gdef", "", "tiny", true); err != nil {
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

func TestPlacedDialRefusesImplicitCrossHostRecovery(t *testing.T) {
	place := placement.NewMemory()
	_ = place.Set(t.Context(), "alice", "fortune", "removed-host")
	agent := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		if r.URL.Path == "/v1/host/capacity" {
			_ = json.NewEncoder(w).Encode(map[string]any{
				"total":    map[string]int{"vcpus": 4, "mem_mib": 4096},
				"used":     map[string]int{"vcpus": 0, "mem_mib": 0},
				"reserved": map[string]int{"vcpus": 0, "mem_mib": 0},
			})
			return
		}
		if r.URL.Path != "/v1/instances/ensure" {
			http.NotFound(w, r)
			return
		}
		_ = json.NewEncoder(w).Encode(map[string]string{
			"addr": "10.20.0.8:24000", "guest_ip": "172.16.2.2", "state": "running",
			"ssh_host_public_key": "test-host-key",
		})
	}))
	t.Cleanup(agent.Close)
	dial := &backend.PlacedDial{
		Placement: place,
		Agents: backend.NewHostSet(map[string]*backend.AgentClient{
			"host-b": {BaseURL: agent.URL},
		}, "host-b"),
		DefaultHost: "removed-host",
	}
	if _, err := dial.EnsureAddr(t.Context(), "alice", "fortune", "gabc", "", false); err == nil {
		t.Fatal("stale placement implicitly booted on another host")
	}
	host, ok, err := place.Get(t.Context(), "alice", "fortune")
	if err != nil || !ok || host != "removed-host" {
		t.Fatalf("placement host=%q ok=%v err=%v", host, ok, err)
	}
}

func TestPlacedDialEnforcesAwakeUserQuotaBeforeEnsure(t *testing.T) {
	t.Parallel()
	ensureCalls := 0
	host := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		switch r.URL.Path {
		case "/v1/instances/status":
			_ = json.NewEncoder(w).Encode(backend.InstanceView{State: "sleeping"})
		case "/v1/host/instances":
			_ = json.NewEncoder(w).Encode(map[string]any{"instances": []agent.InstanceInfo{
				{User: "alice", App: "one", Gen: "g1", State: agent.StateRunning},
				{User: "alice", App: "two", Gen: "g1", State: agent.StateRunning},
			}})
		case "/v1/instances/ensure":
			ensureCalls++
			_ = json.NewEncoder(w).Encode(backend.InstanceView{
				Addr: "127.0.0.1:22", State: "running", SSHHostPublicKey: "key",
			})
		default:
			http.NotFound(w, r)
		}
	}))
	defer host.Close()
	place := placement.NewMemory()
	if err := place.Set(t.Context(), "alice", "fortune", "host-a"); err != nil {
		t.Fatal(err)
	}
	dial := &backend.PlacedDial{
		Placement: place,
		Agents: backend.NewHostSet(map[string]*backend.AgentClient{
			"host-a": {BaseURL: host.URL},
		}, "host-a"),
		Quotas: quota.NewMemory(), MaxAwakePerUser: 2,
	}
	_, err := dial.EnsureAddr(t.Context(), "alice", "fortune", "gfortune", "", false)
	var exceeded quota.ErrExceeded
	if !errors.As(err, &exceeded) {
		t.Fatalf("error %v, want awake quota", err)
	}
	if ensureCalls != 0 {
		t.Fatalf("ensure called %d times after quota denial", ensureCalls)
	}
}

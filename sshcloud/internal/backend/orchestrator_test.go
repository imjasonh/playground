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
	agents["host-a"] = &backend.AgentClient{BaseURL: agent.URL, InsecureLoopback: true}

	dial := &backend.PlacedDial{
		Placement: place,
		Agents:    backend.NewHostSet(agents),
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
			addr, err := dial.EnsureAddrTierWithOptions(
				r.Context(), req.User, req.App, req.Gen, req.Image, "", req.NoIdle,
				backend.StartOptions{Purpose: "session", RequestID: "test-session"},
			)
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

	c := &backend.OrchestratorClient{BaseURL: orch.URL, InsecureLoopback: true}
	digest := "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"
	target, err := c.TargetTierRequest(
		t.Context(), "alice", "fortune", "gabc", "ghcr.io/me/app@sha256:"+digest,
		"", false, "session", "test-session",
	)
	if err != nil {
		t.Fatal(err)
	}
	if target.Addr != "10.0.0.2:22" {
		t.Fatalf("addr = %q", target.Addr)
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
	_ = place.SetIdentity(t.Context(), "alice", "fortune", "missing", "local:missing")
	dial := &backend.PlacedDial{
		Placement: place,
		Agents:    backend.NewHostSet(map[string]*backend.AgentClient{}),
	}
	if _, err := dial.EnsureAddrTierWithOptions(
		t.Context(), "alice", "fortune", "", "", "", false,
		backend.StartOptions{Purpose: "session", RequestID: "test-session"},
	); err == nil {
		t.Fatal("expected error for unknown host")
	}
}

func TestPlacedDialRefusesImplicitCrossHostRecovery(t *testing.T) {
	place := placement.NewMemory()
	_ = place.SetIdentity(t.Context(), "alice", "fortune", "removed-host", "local:removed-host")
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
			"host-b": {BaseURL: agent.URL, InsecureLoopback: true},
		}),
	}
	if _, err := dial.EnsureAddrTierWithOptions(
		t.Context(), "alice", "fortune", "gabc", "", "", false,
		backend.StartOptions{Purpose: "session", RequestID: "test-session"},
	); err == nil {
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
	if err := place.SetIdentity(t.Context(), "alice", "fortune", "host-a", "local:host-a"); err != nil {
		t.Fatal(err)
	}
	dial := &backend.PlacedDial{
		Placement: place,
		Agents: backend.NewHostSet(map[string]*backend.AgentClient{
			"host-a": {BaseURL: host.URL, InsecureLoopback: true},
		}),
		Quotas: quota.NewMemory(), MaxAwakePerUser: 2,
	}
	_, err := dial.EnsureAddrTierWithOptions(
		t.Context(), "alice", "fortune", "gfortune", "", "", false,
		backend.StartOptions{Purpose: "session", RequestID: "test-session"},
	)
	var exceeded quota.ErrExceeded
	if !errors.As(err, &exceeded) {
		t.Fatalf("error %v, want awake quota", err)
	}
	if ensureCalls != 0 {
		t.Fatalf("ensure called %d times after quota denial", ensureCalls)
	}
}

func TestPlacedDialWakeOperationIdentity(t *testing.T) {
	t.Parallel()
	ensureCalls := 0
	host := quotaAgentServer(t, nil, &ensureCalls)
	place := placement.NewMemory()
	if err := place.SetIdentity(t.Context(), "alice", "fortune", "host-a", "local:host-a"); err != nil {
		t.Fatal(err)
	}
	dial := &backend.PlacedDial{
		Placement: place,
		Agents: backend.NewHostSet(map[string]*backend.AgentClient{
			"host-a": {BaseURL: host.URL, InsecureLoopback: true},
		}),
		Quotas: quota.NewMemory(), MaxAwakePerUser: 10, WakesPerHour: 1,
	}
	options := backend.StartOptions{Purpose: "session", RequestID: "session-stable"}
	for attempt := 0; attempt < 2; attempt++ {
		if _, err := dial.EnsureAddrTierWithOptions(
			t.Context(), "alice", "fortune", "g1", "", "tiny", false, options,
		); err != nil {
			t.Fatalf("retry %d with stable operation ID: %v", attempt, err)
		}
	}
	_, err := dial.EnsureAddrTierWithOptions(
		t.Context(), "alice", "fortune", "g1", "", "tiny", false,
		backend.StartOptions{Purpose: "session", RequestID: "session-separate"},
	)
	var exceeded quota.ErrExceeded
	if !errors.As(err, &exceeded) || exceeded.Kind != "wake" {
		t.Fatalf("separate wake error = %v, want wake quota", err)
	}
	if ensureCalls != 2 {
		t.Fatalf("ensure calls = %d, want two retries before separate wake denial", ensureCalls)
	}
}

func TestPlacedDialDeployBurstRequiresRunningOldGeneration(t *testing.T) {
	t.Parallel()
	tests := []struct {
		name      string
		inventory []agent.InstanceInfo
		wantError bool
	}{
		{
			name: "initial deploy gets no burst",
			inventory: []agent.InstanceInfo{
				{User: "alice", App: "one", Gen: "g1", State: agent.StateRunning},
				{User: "alice", App: "two", Gen: "g1", State: agent.StateRunning},
			},
			wantError: true,
		},
		{
			name: "old plus new cutover gets one burst",
			inventory: []agent.InstanceInfo{
				{User: "alice", App: "fortune", Gen: "gold", State: agent.StateRunning},
				{User: "alice", App: "other", Gen: "g1", State: agent.StateRunning},
			},
		},
	}
	for _, tc := range tests {
		tc := tc
		t.Run(tc.name, func(t *testing.T) {
			t.Parallel()
			ensureCalls := 0
			host := quotaAgentServer(t, tc.inventory, &ensureCalls)
			place := placement.NewMemory()
			if err := place.SetIdentity(t.Context(), "alice", "fortune", "host-a", "local:host-a"); err != nil {
				t.Fatal(err)
			}
			dial := &backend.PlacedDial{
				Placement: place,
				Agents: backend.NewHostSet(map[string]*backend.AgentClient{
					"host-a": {BaseURL: host.URL, InsecureLoopback: true},
				}),
				Quotas: quota.NewMemory(), MaxAwakePerUser: 2, WakesPerHour: 10,
			}
			_, err := dial.EnsureAddrTierWithOptions(
				t.Context(), "alice", "fortune", "gnew", "", "tiny", true,
				backend.StartOptions{Purpose: "deploy", RequestID: "deploy-gnew"},
			)
			if tc.wantError {
				var exceeded quota.ErrExceeded
				if !errors.As(err, &exceeded) || exceeded.Kind != "awake_vms" {
					t.Fatalf("error = %v, want awake_vms quota", err)
				}
				if ensureCalls != 0 {
					t.Fatalf("initial deploy used burst and called ensure %d times", ensureCalls)
				}
				return
			}
			if err != nil {
				t.Fatal(err)
			}
			if ensureCalls != 1 {
				t.Fatalf("cutover ensure calls = %d, want 1", ensureCalls)
			}
		})
	}
}

func quotaAgentServer(t *testing.T, inventory []agent.InstanceInfo, ensureCalls *int) *httptest.Server {
	t.Helper()
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		switch r.URL.Path {
		case "/v1/instances/status":
			_ = json.NewEncoder(w).Encode(backend.InstanceView{State: "sleeping"})
		case "/v1/host/instances":
			_ = json.NewEncoder(w).Encode(map[string]any{"instances": inventory})
		case "/v1/instances/ensure":
			(*ensureCalls)++
			_ = json.NewEncoder(w).Encode(backend.InstanceView{
				Addr: "127.0.0.1:22", State: "running", SSHHostPublicKey: "key",
			})
		default:
			http.NotFound(w, r)
		}
	}))
	t.Cleanup(server.Close)
	return server
}

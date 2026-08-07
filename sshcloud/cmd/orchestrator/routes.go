package main

import (
	"context"
	"encoding/json"
	"fmt"
	"net"
	"net/http"
	"os"
	"path/filepath"
	"strings"
	"syscall"
	"time"

	"github.com/imjasonh/playground/sshcloud/internal/agent"
	"github.com/imjasonh/playground/sshcloud/internal/backend"
	"github.com/imjasonh/playground/sshcloud/internal/controlauth"
	"github.com/imjasonh/playground/sshcloud/internal/drain"
	"github.com/imjasonh/playground/sshcloud/internal/image"
	"github.com/imjasonh/playground/sshcloud/internal/migrate"
	"github.com/imjasonh/playground/sshcloud/internal/placement"
)

func buildAPIRoutes(
	controlTLS *controlauth.TLSFlags,
	hosts *backend.HostSet,
	place placement.Store,
	drainer *drain.Controller,
	mig *migrate.Migrator,
	dial *backend.PlacedDial,
) (*http.ServeMux, http.HandlerFunc) {
	api := http.NewServeMux()
	ready := readyHandler(controlTLS, hosts, place)
	api.HandleFunc("GET /v1/readyz", ready)
	api.HandleFunc("GET /v1/hosts", hostsHandler(hosts))
	api.HandleFunc("POST /v1/hosts/cordon", cordonHostHandler(hosts))
	api.HandleFunc("POST /v1/hosts/drain", drainHostHandler(drainer))
	api.HandleFunc("POST /v1/migrate", migrateHandler(mig))
	api.HandleFunc("POST /v1/ensure", ensureHandler(dial))
	api.HandleFunc("POST /v1/stop", stopHandler(dial))
	api.HandleFunc("POST /v1/no-idle", noIdleHandler(dial))
	api.HandleFunc("GET /v1/placement", placementHandler(place))
	api.HandleFunc("GET /v1/placements", placementsHandler(place))
	api.HandleFunc("GET /v1/diagnostics", diagnosticsHandler(place, hosts))
	return api, ready
}

func readyHandler(
	controlTLS *controlauth.TLSFlags,
	hosts *backend.HostSet,
	place placement.Store,
) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		readyCtx, cancel := context.WithTimeout(r.Context(), 4*time.Second)
		defer cancel()
		if err := controlTLS.Fresh(); err != nil {
			http.Error(w, "unavailable", http.StatusServiceUnavailable)
			return
		}
		if hosts.Len() == 0 {
			http.Error(w, "unavailable", http.StatusServiceUnavailable)
			return
		}
		if _, err := place.ListRecords(readyCtx); err != nil {
			http.Error(w, "unavailable", http.StatusServiceUnavailable)
			return
		}
		if _, err := hosts.Candidates(readyCtx, "tiny", nil); err != nil {
			http.Error(w, "unavailable", http.StatusServiceUnavailable)
			return
		}
		w.WriteHeader(http.StatusOK)
		_, _ = w.Write([]byte("ok"))
	}
}

func hostsHandler(hosts *backend.HostSet) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		type hostView struct {
			ID       string         `json:"id"`
			Capacity agent.Capacity `json:"capacity"`
			Error    string         `json:"error,omitempty"`
		}
		var views []hostView
		for _, id := range hosts.IDs() {
			client, _ := hosts.Get(id)
			capacity, err := client.Capacity(r.Context())
			view := hostView{ID: id, Capacity: capacity}
			if err != nil {
				view.Error = err.Error()
			}
			views = append(views, view)
		}
		w.Header().Set("Content-Type", "application/json")
		_ = json.NewEncoder(w).Encode(map[string]any{"hosts": views})
	}
}

func cordonHostHandler(hosts *backend.HostSet) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		var req struct {
			Host        string `json:"host"`
			Cordoned    *bool  `json:"cordoned"`
			CordonEpoch string `json:"cordon_epoch"`
		}
		if !decodeJSON(w, r, &req) {
			return
		}
		client, ok := hosts.Get(req.Host)
		if !ok {
			http.Error(w, "unknown host", http.StatusNotFound)
			return
		}
		cordoned := true
		if req.Cordoned != nil {
			cordoned = *req.Cordoned
		}
		var err error
		if cordoned {
			var epoch string
			epoch, err = client.Cordon(r.Context())
			if err == nil {
				w.Header().Set("Content-Type", "application/json")
				_ = json.NewEncoder(w).Encode(map[string]string{"cordon_epoch": epoch})
				return
			}
		} else {
			err = client.Uncordon(r.Context(), req.CordonEpoch)
		}
		if err != nil {
			http.Error(w, err.Error(), http.StatusBadGateway)
			return
		}
		w.WriteHeader(http.StatusNoContent)
	}
}

func drainHostHandler(drainer *drain.Controller) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		var req struct {
			Host string `json:"host"`
		}
		if !decodeJSON(w, r, &req) {
			return
		}
		result, err := drainer.DrainHost(r.Context(), req.Host)
		if err != nil {
			http.Error(w, err.Error(), http.StatusConflict)
			return
		}
		w.Header().Set("Content-Type", "application/json")
		_ = json.NewEncoder(w).Encode(result)
	}
}

func migrateHandler(mig *migrate.Migrator) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		var req struct {
			User string `json:"user"`
			App  string `json:"app"`
			Gen  string `json:"gen"`
			To   string `json:"to"`
		}
		if !decodeJSON(w, r, &req) {
			return
		}
		if err := validateIdentity(req.User, req.App, req.Gen); err != nil {
			http.Error(w, err.Error(), http.StatusBadRequest)
			return
		}
		res, err := mig.MigrateGeneration(r.Context(), req.User, req.App, req.Gen, req.To)
		if err != nil {
			http.Error(w, err.Error(), http.StatusConflict)
			return
		}
		w.Header().Set("Content-Type", "application/json")
		_ = json.NewEncoder(w).Encode(res)
	}
}

func ensureHandler(dial *backend.PlacedDial) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		var req struct {
			User      string `json:"user"`
			App       string `json:"app"`
			Gen       string `json:"gen"`
			Image     string `json:"image"`
			Tier      string `json:"tier"`
			NoIdle    bool   `json:"no_idle"`
			Purpose   string `json:"purpose"`
			RequestID string `json:"request_id"`
		}
		if !decodeJSON(w, r, &req) {
			return
		}
		if err := validateIdentity(req.User, req.App, req.Gen); err != nil {
			http.Error(w, err.Error(), http.StatusBadRequest)
			return
		}
		if req.Image = strings.TrimSpace(req.Image); req.Image != "" {
			if err := image.ValidateDigestPinned(req.Image); err != nil {
				http.Error(w, err.Error(), http.StatusBadRequest)
				return
			}
		}
		if req.Tier != "" && req.Tier != "tiny" && req.Tier != "small" {
			http.Error(w, "tier must be tiny or small", http.StatusBadRequest)
			return
		}
		if req.Purpose == "" {
			req.Purpose = "session"
		}
		if req.Purpose != "session" && req.Purpose != "deploy" {
			http.Error(w, "purpose must be session or deploy", http.StatusBadRequest)
			return
		}
		req.RequestID = strings.TrimSpace(req.RequestID)
		if req.RequestID == "" || len(req.RequestID) > 128 ||
			strings.ContainsAny(req.RequestID, "\x00\r\n\t ") {
			http.Error(w, "request_id must be a non-empty opaque operation ID", http.StatusBadRequest)
			return
		}
		addr, err := dial.EnsureAddrTierWithOptions(
			r.Context(), req.User, req.App, req.Gen, req.Image, req.Tier, req.NoIdle,
			backend.StartOptions{Purpose: req.Purpose, RequestID: req.RequestID},
		)
		if err != nil {
			writeControlError(w, err)
			return
		}
		view, found, err := dial.StatusView(r.Context(), req.User, req.App, req.Gen)
		if err != nil || !found || view.SSHHostPublicKey == "" {
			if err == nil {
				err = fmt.Errorf("ensured generation has no SSH host identity")
			}
			writeControlError(w, err)
			return
		}
		w.Header().Set("Content-Type", "application/json")
		_ = json.NewEncoder(w).Encode(map[string]string{
			"addr": addr, "ssh_host_public_key": view.SSHHostPublicKey,
		})
	}
}

func stopHandler(dial *backend.PlacedDial) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		var req struct {
			User string `json:"user"`
			App  string `json:"app"`
			Gen  string `json:"gen"`
		}
		if !decodeJSON(w, r, &req) {
			return
		}
		if err := validateIdentity(req.User, req.App, req.Gen); err != nil {
			http.Error(w, err.Error(), http.StatusBadRequest)
			return
		}
		if err := dial.Stop(r.Context(), req.User, req.App, req.Gen); err != nil {
			writeControlError(w, err)
			return
		}
		w.WriteHeader(http.StatusNoContent)
	}
}

func noIdleHandler(dial *backend.PlacedDial) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		var req struct {
			User   string `json:"user"`
			App    string `json:"app"`
			Gen    string `json:"gen"`
			NoIdle bool   `json:"no_idle"`
		}
		if !decodeJSON(w, r, &req) {
			return
		}
		if err := validateIdentity(req.User, req.App, req.Gen); err != nil {
			http.Error(w, err.Error(), http.StatusBadRequest)
			return
		}
		if err := dial.SetNoIdle(r.Context(), req.User, req.App, req.Gen, req.NoIdle); err != nil {
			writeControlError(w, err)
			return
		}
		w.WriteHeader(http.StatusNoContent)
	}
}

func placementHandler(place placement.Store) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		user := r.URL.Query().Get("user")
		app := r.URL.Query().Get("app")
		if err := validateIdentity(user, app, ""); err != nil {
			http.Error(w, err.Error(), http.StatusBadRequest)
			return
		}
		record, ok, err := place.GetRecord(r.Context(), user, app)
		if err != nil {
			http.Error(w, err.Error(), http.StatusInternalServerError)
			return
		}
		if !ok {
			http.Error(w, "not found", http.StatusNotFound)
			return
		}
		w.Header().Set("Content-Type", "application/json")
		_ = json.NewEncoder(w).Encode(record)
	}
}

func placementsHandler(place placement.Store) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		records, err := place.ListRecords(r.Context())
		if err != nil {
			http.Error(w, err.Error(), http.StatusInternalServerError)
			return
		}
		w.Header().Set("Content-Type", "application/json")
		_ = json.NewEncoder(w).Encode(map[string]any{"placements": records})
	}
}

const (
	maxDiagnosticPlacements       = 200
	maxDiagnosticHosts            = 100
	maxDiagnosticInstancesPerHost = 100
	maxDiagnosticErrorBytes       = 512
)

func diagnosticsHandler(place placement.Store, hosts *backend.HostSet) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		records, err := place.ListRecords(r.Context())
		if err != nil {
			http.Error(w, err.Error(), http.StatusInternalServerError)
			return
		}
		hostDiagnostics := hosts.Diagnostics(r.Context())
		placementTotal := len(records)
		if len(records) > maxDiagnosticPlacements {
			records = records[:maxDiagnosticPlacements]
		}
		hostTotal := len(hostDiagnostics)
		instanceTotal := 0
		for _, diagnostic := range hostDiagnostics {
			instanceTotal += len(diagnostic.Instances)
		}
		if len(hostDiagnostics) > maxDiagnosticHosts {
			hostDiagnostics = hostDiagnostics[:maxDiagnosticHosts]
		}
		instanceReturned := 0
		for index := range hostDiagnostics {
			if len(hostDiagnostics[index].Instances) > maxDiagnosticInstancesPerHost {
				hostDiagnostics[index].Instances = hostDiagnostics[index].Instances[:maxDiagnosticInstancesPerHost]
			}
			instanceReturned += len(hostDiagnostics[index].Instances)
			hostDiagnostics[index].Error = boundedDiagnosticText(hostDiagnostics[index].Error)
		}
		w.Header().Set("Content-Type", "application/json")
		_ = json.NewEncoder(w).Encode(map[string]any{
			"placements": records, "hosts": hostDiagnostics,
			"bounds": map[string]int{
				"placements_total": placementTotal, "placements_returned": len(records),
				"hosts_total": hostTotal, "hosts_returned": len(hostDiagnostics),
				"instances_total": instanceTotal, "instances_returned": instanceReturned,
			},
		})
	}
}

func boundedDiagnosticText(value string) string {
	if len(value) <= maxDiagnosticErrorBytes {
		return value
	}
	return value[:maxDiagnosticErrorBytes]
}

func gatewayServiceRoutes(next http.Handler) http.Handler {
	return exactRoutes(next, map[string]struct{}{
		"GET /v1/readyz":   {},
		"POST /v1/ensure":  {},
		"POST /v1/stop":    {},
		"POST /v1/no-idle": {},
	})
}

func adminRoutes(next http.Handler) http.Handler {
	return exactRoutes(next, map[string]struct{}{
		"GET /v1/hosts":         {},
		"POST /v1/hosts/cordon": {},
		"POST /v1/hosts/drain":  {},
		"POST /v1/migrate":      {},
		"GET /v1/placement":     {},
		"GET /v1/placements":    {},
		"GET /v1/diagnostics":   {},
	})
}

func exactRoutes(next http.Handler, allowed map[string]struct{}) http.Handler {
	return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		if _, ok := allowed[r.Method+" "+r.URL.Path]; !ok {
			http.NotFound(w, r)
			return
		}
		next.ServeHTTP(w, r)
	})
}

func listenAdminSocket(path string, requireRoot bool) (net.Listener, error) {
	if path == "" {
		return nil, fmt.Errorf("admin socket path is required")
	}
	if requireRoot && os.Geteuid() != 0 {
		return nil, fmt.Errorf("production admin socket requires root")
	}
	parent := filepath.Dir(path)
	if err := os.MkdirAll(parent, 0o755); err != nil {
		return nil, err
	}
	parentInfo, err := os.Stat(parent)
	if err != nil {
		return nil, err
	}
	if requireRoot {
		stat, ok := parentInfo.Sys().(*syscall.Stat_t)
		if !ok || stat.Uid != 0 || parentInfo.Mode().Perm()&0o022 != 0 {
			return nil, fmt.Errorf("admin socket directory %s must be root-owned and not group/world-writable", parent)
		}
	}
	if info, err := os.Lstat(path); err == nil {
		if info.Mode()&os.ModeSocket == 0 {
			return nil, fmt.Errorf("refusing to replace non-socket admin path %s", path)
		}
		if requireRoot {
			stat, ok := info.Sys().(*syscall.Stat_t)
			if !ok || stat.Uid != 0 {
				return nil, fmt.Errorf("refusing to replace admin socket not owned by root")
			}
		}
		if err := os.Remove(path); err != nil {
			return nil, err
		}
	} else if !os.IsNotExist(err) {
		return nil, err
	}
	listener, err := net.Listen("unix", path)
	if err != nil {
		return nil, err
	}
	cleanup := func(err error) (net.Listener, error) {
		_ = listener.Close()
		_ = os.Remove(path)
		return nil, err
	}
	if err := os.Chmod(path, 0o600); err != nil {
		return cleanup(err)
	}
	if requireRoot {
		info, err := os.Stat(path)
		if err != nil {
			return cleanup(err)
		}
		stat, ok := info.Sys().(*syscall.Stat_t)
		if !ok || stat.Uid != 0 || stat.Gid != 0 {
			return cleanup(fmt.Errorf("admin socket is not owned by root"))
		}
	}
	return listener, nil
}

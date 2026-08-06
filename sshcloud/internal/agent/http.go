package agent

import (
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"net/http"
	"strings"
	"time"

	"github.com/imjasonh/playground/sshcloud/internal/controlauth"
	"github.com/imjasonh/playground/sshcloud/internal/genid"
	"github.com/imjasonh/playground/sshcloud/internal/image"
	"github.com/imjasonh/playground/sshcloud/internal/names"
)

// Handler serves the host agent HTTP API.
type Handler struct {
	Manager        *Manager
	Readiness      func() error
	IdentityTokens controlauth.TokenSource
	InstanceName   string
	InstanceID     string
}

const (
	TargetInstanceNameHeader = "X-SSHCloud-Target-Instance-Name"
	TargetInstanceIDHeader   = "X-SSHCloud-Target-Instance-ID"
)

// Mount registers control routes on mux (Go 1.22+ method patterns). The
// production command wraps this mux in controlauth.Require before serving it.
func (h *Handler) Mount(mux *http.ServeMux) {
	api := http.NewServeMux()
	api.HandleFunc("POST /v1/instances/ensure", h.ensure)
	api.HandleFunc("POST /v1/instances/stop", h.stop)
	api.HandleFunc("POST /v1/instances/sleep", h.sleep)
	api.HandleFunc("POST /v1/instances/wake", h.wake)
	api.HandleFunc("POST /v1/instances/evict", h.evict)
	api.HandleFunc("POST /v1/instances/adopt", h.adopt)
	api.HandleFunc("POST /v1/instances/preflight", h.preflight)
	api.HandleFunc("POST /v1/instances/register-sleeping", h.registerSleeping)
	api.HandleFunc("POST /v1/instances/no-idle", h.setNoIdle)
	api.HandleFunc("GET /v1/instances/status", h.status)
	api.HandleFunc("GET /v1/host/capacity", h.capacity)
	api.HandleFunc("GET /v1/host/instances", h.instances)
	api.HandleFunc("GET /v1/host/orphans", h.orphans)
	api.HandleFunc("GET /v1/host/identity", h.identity)
	api.HandleFunc("POST /v1/host/cordon", h.cordon)
	api.HandleFunc("POST /v1/host/uncordon", h.uncordon)
	mux.Handle("/v1/", h.bindMutationTarget(api))
}

func (h *Handler) bindMutationTarget(next http.Handler) http.Handler {
	if h.InstanceName == "" && h.InstanceID == "" {
		return next
	}
	return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		if r.Method != http.MethodPost {
			next.ServeHTTP(w, r)
			return
		}
		names := r.Header.Values(TargetInstanceNameHeader)
		ids := r.Header.Values(TargetInstanceIDHeader)
		if h.InstanceName == "" || h.InstanceID == "" ||
			len(names) != 1 || names[0] != h.InstanceName ||
			len(ids) != 1 || ids[0] != h.InstanceID {
			http.Error(w, "request targets a different agent incarnation", http.StatusMisdirectedRequest)
			return
		}
		next.ServeHTTP(w, r)
	})
}

// MountHealth registers only body-free liveness/readiness endpoints. It is
// intentionally separate from the authenticated control listener.
func (h *Handler) MountHealth(mux *http.ServeMux) {
	ready := func(w http.ResponseWriter, _ *http.Request) {
		if h.Readiness != nil {
			if err := h.Readiness(); err != nil {
				http.Error(w, "unavailable", http.StatusServiceUnavailable)
				return
			}
		}
		w.WriteHeader(http.StatusOK)
		_, _ = w.Write([]byte("ok"))
	}
	mux.HandleFunc("GET /healthz", ready)
	mux.HandleFunc("GET /readyz", ready)
	mux.HandleFunc("GET /livez", func(w http.ResponseWriter, _ *http.Request) {
		w.WriteHeader(http.StatusOK)
		_, _ = w.Write([]byte("ok"))
	})
}

type instanceRequest struct {
	User        string `json:"user"`
	App         string `json:"app"`
	Gen         string `json:"gen,omitempty"`
	NoIdle      bool   `json:"no_idle,omitempty"`
	Image       string `json:"image,omitempty"`
	Tier        string `json:"tier,omitempty"`
	CordonEpoch string `json:"cordon_epoch,omitempty"`
}

func agentApp(req instanceRequest) string {
	return genid.AgentApp(req.App, req.Gen)
}

func validateInstanceRequest(req instanceRequest) error {
	if err := names.ValidateIdent(req.User); err != nil {
		return fmt.Errorf("invalid user: %w", err)
	}
	if err := names.ValidateIdent(req.App); err != nil {
		return fmt.Errorf("invalid app: %w", err)
	}
	if req.Gen != "" {
		if err := genid.Validate(req.Gen); err != nil {
			return err
		}
	}
	return nil
}

func decodeInstanceRequest(w http.ResponseWriter, r *http.Request) (instanceRequest, bool) {
	var req instanceRequest
	r.Body = http.MaxBytesReader(w, r.Body, 8<<10)
	dec := json.NewDecoder(r.Body)
	dec.DisallowUnknownFields()
	if err := dec.Decode(&req); err != nil {
		http.Error(w, "invalid JSON: "+err.Error(), http.StatusBadRequest)
		return instanceRequest{}, false
	}
	if err := dec.Decode(&struct{}{}); err != io.EOF {
		http.Error(w, "request body must contain one JSON object", http.StatusBadRequest)
		return instanceRequest{}, false
	}
	if err := validateInstanceRequest(req); err != nil {
		http.Error(w, err.Error(), http.StatusBadRequest)
		return instanceRequest{}, false
	}
	return req, true
}

type ensureResponse struct {
	Addr             string `json:"addr"`
	GuestIP          string `json:"guest_ip"`
	State            string `json:"state"`
	SSHHostPublicKey string `json:"ssh_host_public_key"`
}

type statusResponse struct {
	User             string `json:"user"`
	App              string `json:"app"`
	State            string `json:"state"`
	Addr             string `json:"addr,omitempty"`
	GuestIP          string `json:"guest_ip,omitempty"`
	LastUsed         string `json:"last_used,omitempty"`
	SnapKey          string `json:"snap_key,omitempty"`
	SSHHostPublicKey string `json:"ssh_host_public_key,omitempty"`
}

func (h *Handler) ensure(w http.ResponseWriter, r *http.Request) {
	req, ok := decodeInstanceRequest(w, r)
	if !ok {
		return
	}
	app := agentApp(req)
	if img := strings.TrimSpace(req.Image); img != "" {
		if err := image.ValidateDigestPinned(img); err != nil {
			http.Error(w, err.Error(), http.StatusBadRequest)
			return
		}
		req.Image = img
	}
	in, err := h.Manager.EnsureWith(r.Context(), req.User, app, EnsureOpts{
		Image: req.Image, Tier: req.Tier, NoIdle: req.NoIdle,
	})
	if err != nil {
		writeManagerError(w, err)
		return
	}
	writeJSON(w, ensureResponse{Addr: in.Addr, GuestIP: in.GuestIP, State: string(in.State), SSHHostPublicKey: in.SSHHostPublicKey})
}

func (h *Handler) stop(w http.ResponseWriter, r *http.Request) {
	req, ok := decodeInstanceRequest(w, r)
	if !ok {
		return
	}
	if err := h.Manager.StopContext(r.Context(), req.User, agentApp(req)); err != nil {
		http.Error(w, err.Error(), http.StatusInternalServerError)
		return
	}
	w.WriteHeader(http.StatusNoContent)
}

func (h *Handler) sleep(w http.ResponseWriter, r *http.Request) {
	req, ok := decodeInstanceRequest(w, r)
	if !ok {
		return
	}
	if err := h.Manager.SleepWithEpoch(r.Context(), req.User, agentApp(req), req.CordonEpoch); err != nil {
		http.Error(w, err.Error(), http.StatusConflict)
		return
	}
	writeJSON(w, statusResponse{User: req.User, App: req.App, State: string(StateSleeping)})
}

func (h *Handler) wake(w http.ResponseWriter, r *http.Request) {
	req, ok := decodeInstanceRequest(w, r)
	if !ok {
		return
	}
	in, err := h.Manager.Ensure(r.Context(), req.User, agentApp(req))
	if err != nil {
		writeManagerError(w, err)
		return
	}
	writeJSON(w, ensureResponse{Addr: in.Addr, GuestIP: in.GuestIP, State: string(in.State), SSHHostPublicKey: in.SSHHostPublicKey})
}

func (h *Handler) evict(w http.ResponseWriter, r *http.Request) {
	req, ok := decodeInstanceRequest(w, r)
	if !ok {
		return
	}
	if err := h.Manager.EvictWithEpoch(r.Context(), req.User, agentApp(req), req.CordonEpoch); err != nil {
		http.Error(w, err.Error(), http.StatusConflict)
		return
	}
	w.WriteHeader(http.StatusNoContent)
}

func (h *Handler) adopt(w http.ResponseWriter, r *http.Request) {
	req, ok := decodeInstanceRequest(w, r)
	if !ok {
		return
	}
	var in *Instance
	var err error
	if req.CordonEpoch != "" {
		in, err = h.Manager.AdoptForced(r.Context(), req.User, agentApp(req), req.CordonEpoch)
	} else {
		in, err = h.Manager.Adopt(r.Context(), req.User, agentApp(req))
	}
	if err != nil {
		writeManagerError(w, err)
		return
	}
	writeJSON(w, ensureResponse{Addr: in.Addr, GuestIP: in.GuestIP, State: string(in.State), SSHHostPublicKey: in.SSHHostPublicKey})
}

func (h *Handler) setNoIdle(w http.ResponseWriter, r *http.Request) {
	req, ok := decodeInstanceRequest(w, r)
	if !ok {
		return
	}
	if err := h.Manager.SetNoIdleWithEpoch(r.Context(), req.User, agentApp(req), req.NoIdle, req.CordonEpoch); err != nil {
		http.Error(w, err.Error(), http.StatusNotFound)
		return
	}
	w.WriteHeader(http.StatusNoContent)
}

func (h *Handler) preflight(w http.ResponseWriter, r *http.Request) {
	req, ok := decodeInstanceRequest(w, r)
	if !ok {
		return
	}
	info, err := h.Manager.PreflightSnapshot(r.Context(), req.User, agentApp(req))
	if err != nil {
		writeManagerError(w, err)
		return
	}
	writeJSON(w, info)
}

func (h *Handler) registerSleeping(w http.ResponseWriter, r *http.Request) {
	req, ok := decodeInstanceRequest(w, r)
	if !ok {
		return
	}
	info, err := h.Manager.RegisterSleepingWithEpoch(
		r.Context(), req.User, agentApp(req), req.CordonEpoch,
	)
	if err != nil {
		writeManagerError(w, err)
		return
	}
	writeJSON(w, info)
}

func (h *Handler) status(w http.ResponseWriter, r *http.Request) {
	user := r.URL.Query().Get("user")
	app := r.URL.Query().Get("app")
	gen := r.URL.Query().Get("gen")
	req := instanceRequest{User: user, App: app, Gen: gen}
	if err := validateInstanceRequest(req); err != nil {
		http.Error(w, err.Error(), http.StatusBadRequest)
		return
	}
	if gen != "" {
		app = genid.AgentApp(app, gen)
	}
	st, ok, err := h.Manager.StatusContext(r.Context(), user, app)
	if err != nil {
		http.Error(w, err.Error(), http.StatusRequestTimeout)
		return
	}
	if !ok {
		http.Error(w, "not found", http.StatusNotFound)
		return
	}
	resp := statusResponse{
		User:             user,
		App:              app,
		State:            string(st.State),
		Addr:             st.Addr,
		GuestIP:          st.GuestIP,
		SnapKey:          st.SnapKey,
		SSHHostPublicKey: st.SSHHostPublicKey,
	}
	if !st.LastUsed.IsZero() {
		resp.LastUsed = st.LastUsed.UTC().Format(time.RFC3339)
	}
	writeJSON(w, resp)
}

func (h *Handler) capacity(w http.ResponseWriter, _ *http.Request) {
	writeJSON(w, h.Manager.Capacity())
}

func (h *Handler) instances(w http.ResponseWriter, _ *http.Request) {
	writeJSON(w, map[string]any{"instances": h.Manager.ListInstances()})
}

func (h *Handler) orphans(w http.ResponseWriter, _ *http.Request) {
	orphans, err := h.Manager.Orphans()
	if err != nil {
		http.Error(w, err.Error(), http.StatusInternalServerError)
		return
	}
	writeJSON(w, map[string]any{"orphans": orphans})
}

func (h *Handler) identity(w http.ResponseWriter, r *http.Request) {
	if h.IdentityTokens == nil {
		http.Error(w, "server identity proof unavailable", http.StatusServiceUnavailable)
		return
	}
	ctx, cancel := context.WithTimeout(r.Context(), 5*time.Second)
	defer cancel()
	token, err := h.IdentityTokens.Token(ctx, controlauth.AudienceAgentServer)
	if err != nil {
		http.Error(w, "server identity proof unavailable", http.StatusServiceUnavailable)
		return
	}
	writeJSON(w, map[string]string{"token": token})
}

func (h *Handler) cordon(w http.ResponseWriter, r *http.Request) {
	epoch, err := h.Manager.Cordon(r.Context())
	if err != nil {
		http.Error(w, err.Error(), http.StatusInternalServerError)
		return
	}
	writeJSON(w, map[string]string{"cordon_epoch": epoch})
}

func (h *Handler) uncordon(w http.ResponseWriter, r *http.Request) {
	if err := r.Context().Err(); err != nil {
		http.Error(w, err.Error(), http.StatusRequestTimeout)
		return
	}
	var req struct {
		CordonEpoch string `json:"cordon_epoch"`
	}
	r.Body = http.MaxBytesReader(w, r.Body, 4<<10)
	decoder := json.NewDecoder(r.Body)
	decoder.DisallowUnknownFields()
	if err := decoder.Decode(&req); err != nil {
		http.Error(w, "invalid JSON: "+err.Error(), http.StatusBadRequest)
		return
	}
	if err := h.Manager.Uncordon(req.CordonEpoch); err != nil {
		http.Error(w, err.Error(), http.StatusInternalServerError)
		return
	}
	w.WriteHeader(http.StatusNoContent)
}

func writeManagerError(w http.ResponseWriter, err error) {
	var capacity ErrCapacity
	var cordoned ErrCordoned
	switch {
	case errors.As(err, &capacity):
		http.Error(w, err.Error(), http.StatusConflict)
	case errors.As(err, &cordoned):
		http.Error(w, err.Error(), http.StatusServiceUnavailable)
	default:
		http.Error(w, err.Error(), http.StatusInternalServerError)
	}
}

func writeJSON(w http.ResponseWriter, v any) {
	w.Header().Set("Content-Type", "application/json")
	_ = json.NewEncoder(w).Encode(v)
}

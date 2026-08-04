package agent

import (
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
	Manager   *Manager
	Token     string
	Readiness func() error
}

// Mount registers routes on mux (Go 1.22+ method patterns).
func (h *Handler) Mount(mux *http.ServeMux) {
	api := http.NewServeMux()
	api.HandleFunc("POST /v1/instances/ensure", h.ensure)
	api.HandleFunc("POST /v1/instances/stop", h.stop)
	api.HandleFunc("POST /v1/instances/sleep", h.sleep)
	api.HandleFunc("POST /v1/instances/wake", h.wake)
	api.HandleFunc("POST /v1/instances/evict", h.evict)
	api.HandleFunc("POST /v1/instances/adopt", h.adopt)
	api.HandleFunc("POST /v1/instances/preflight", h.preflight)
	api.HandleFunc("POST /v1/instances/no-idle", h.setNoIdle)
	api.HandleFunc("GET /v1/instances/status", h.status)
	api.HandleFunc("GET /v1/host/capacity", h.capacity)
	api.HandleFunc("GET /v1/host/instances", h.instances)
	api.HandleFunc("POST /v1/host/cordon", h.cordon)
	api.HandleFunc("POST /v1/host/uncordon", h.uncordon)
	mux.Handle("/v1/", controlauth.Require(h.Token, api))
	mux.HandleFunc("GET /healthz", func(w http.ResponseWriter, _ *http.Request) {
		if h.Readiness != nil {
			if err := h.Readiness(); err != nil {
				http.Error(w, "not ready: "+err.Error(), http.StatusServiceUnavailable)
				return
			}
		}
		w.WriteHeader(http.StatusOK)
		_, _ = w.Write([]byte("ok"))
	})
}

type instanceRequest struct {
	User   string `json:"user"`
	App    string `json:"app"`
	Gen    string `json:"gen,omitempty"`
	NoIdle bool   `json:"no_idle,omitempty"`
	Image  string `json:"image,omitempty"`
	Tier   string `json:"tier,omitempty"`
	Force  bool   `json:"force,omitempty"`
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
	Addr    string `json:"addr"`
	GuestIP string `json:"guest_ip"`
	State   string `json:"state"`
}

type statusResponse struct {
	User     string `json:"user"`
	App      string `json:"app"`
	State    string `json:"state"`
	Addr     string `json:"addr,omitempty"`
	GuestIP  string `json:"guest_ip,omitempty"`
	LastUsed string `json:"last_used,omitempty"`
	SnapKey  string `json:"snap_key,omitempty"`
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
	writeJSON(w, ensureResponse{Addr: in.Addr, GuestIP: in.GuestIP, State: string(in.State)})
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
	if err := h.Manager.Sleep(r.Context(), req.User, agentApp(req)); err != nil {
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
	writeJSON(w, ensureResponse{Addr: in.Addr, GuestIP: in.GuestIP, State: string(in.State)})
}

func (h *Handler) evict(w http.ResponseWriter, r *http.Request) {
	req, ok := decodeInstanceRequest(w, r)
	if !ok {
		return
	}
	if err := h.Manager.Evict(req.User, agentApp(req)); err != nil {
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
	if req.Force {
		in, err = h.Manager.AdoptForced(r.Context(), req.User, agentApp(req))
	} else {
		in, err = h.Manager.Adopt(r.Context(), req.User, agentApp(req))
	}
	if err != nil {
		writeManagerError(w, err)
		return
	}
	writeJSON(w, ensureResponse{Addr: in.Addr, GuestIP: in.GuestIP, State: string(in.State)})
}

func (h *Handler) setNoIdle(w http.ResponseWriter, r *http.Request) {
	req, ok := decodeInstanceRequest(w, r)
	if !ok {
		return
	}
	if err := h.Manager.SetNoIdle(req.User, agentApp(req), req.NoIdle); err != nil {
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
	st, ok := h.Manager.Status(user, app)
	if !ok {
		http.Error(w, "not found", http.StatusNotFound)
		return
	}
	resp := statusResponse{
		User:    user,
		App:     app,
		State:   string(st.State),
		Addr:    st.Addr,
		GuestIP: st.GuestIP,
		SnapKey: st.SnapKey,
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

func (h *Handler) cordon(w http.ResponseWriter, r *http.Request) {
	if err := h.Manager.Cordon(r.Context()); err != nil {
		http.Error(w, err.Error(), http.StatusInternalServerError)
		return
	}
	w.WriteHeader(http.StatusNoContent)
}

func (h *Handler) uncordon(w http.ResponseWriter, _ *http.Request) {
	if err := h.Manager.SetCordoned(false); err != nil {
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

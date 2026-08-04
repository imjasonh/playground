package agent

import (
	"encoding/json"
	"net/http"
	"strings"
	"time"

	"github.com/imjasonh/playground/sshcloud/internal/genid"
	"github.com/imjasonh/playground/sshcloud/internal/image"
)

// Handler serves the host agent HTTP API.
type Handler struct {
	Manager *Manager
}

// Mount registers routes on mux (Go 1.22+ method patterns).
func (h *Handler) Mount(mux *http.ServeMux) {
	mux.HandleFunc("POST /v1/instances/ensure", h.ensure)
	mux.HandleFunc("POST /v1/instances/stop", h.stop)
	mux.HandleFunc("POST /v1/instances/sleep", h.sleep)
	mux.HandleFunc("POST /v1/instances/wake", h.wake)
	mux.HandleFunc("POST /v1/instances/evict", h.evict)
	mux.HandleFunc("POST /v1/instances/adopt", h.adopt)
	mux.HandleFunc("GET /v1/instances/status", h.status)
	mux.HandleFunc("GET /healthz", func(w http.ResponseWriter, _ *http.Request) {
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
}

func agentApp(req instanceRequest) string {
	return genid.AgentApp(req.App, req.Gen)
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
	var req instanceRequest
	if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
		http.Error(w, err.Error(), http.StatusBadRequest)
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
	in, err := h.Manager.EnsureWith(r.Context(), req.User, app, EnsureOpts{Image: req.Image})
	if err != nil {
		http.Error(w, err.Error(), http.StatusInternalServerError)
		return
	}
	h.Manager.SetNoIdle(req.User, app, req.NoIdle)
	writeJSON(w, ensureResponse{Addr: in.Addr, GuestIP: in.GuestIP, State: string(in.State)})
}

func (h *Handler) stop(w http.ResponseWriter, r *http.Request) {
	var req instanceRequest
	if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
		http.Error(w, err.Error(), http.StatusBadRequest)
		return
	}
	if err := h.Manager.Stop(req.User, agentApp(req)); err != nil {
		http.Error(w, err.Error(), http.StatusInternalServerError)
		return
	}
	w.WriteHeader(http.StatusNoContent)
}

func (h *Handler) sleep(w http.ResponseWriter, r *http.Request) {
	var req instanceRequest
	if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
		http.Error(w, err.Error(), http.StatusBadRequest)
		return
	}
	if err := h.Manager.Sleep(r.Context(), req.User, agentApp(req)); err != nil {
		http.Error(w, err.Error(), http.StatusConflict)
		return
	}
	writeJSON(w, statusResponse{User: req.User, App: req.App, State: string(StateSleeping)})
}

func (h *Handler) wake(w http.ResponseWriter, r *http.Request) {
	var req instanceRequest
	if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
		http.Error(w, err.Error(), http.StatusBadRequest)
		return
	}
	in, err := h.Manager.Ensure(r.Context(), req.User, agentApp(req))
	if err != nil {
		http.Error(w, err.Error(), http.StatusInternalServerError)
		return
	}
	writeJSON(w, ensureResponse{Addr: in.Addr, GuestIP: in.GuestIP, State: string(in.State)})
}

func (h *Handler) evict(w http.ResponseWriter, r *http.Request) {
	var req instanceRequest
	if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
		http.Error(w, err.Error(), http.StatusBadRequest)
		return
	}
	if err := h.Manager.Evict(req.User, agentApp(req)); err != nil {
		http.Error(w, err.Error(), http.StatusConflict)
		return
	}
	w.WriteHeader(http.StatusNoContent)
}

func (h *Handler) adopt(w http.ResponseWriter, r *http.Request) {
	var req instanceRequest
	if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
		http.Error(w, err.Error(), http.StatusBadRequest)
		return
	}
	in, err := h.Manager.Adopt(r.Context(), req.User, agentApp(req))
	if err != nil {
		http.Error(w, err.Error(), http.StatusInternalServerError)
		return
	}
	writeJSON(w, ensureResponse{Addr: in.Addr, GuestIP: in.GuestIP, State: string(in.State)})
}

func (h *Handler) status(w http.ResponseWriter, r *http.Request) {
	user := r.URL.Query().Get("user")
	app := r.URL.Query().Get("app")
	gen := r.URL.Query().Get("gen")
	if user == "" || app == "" {
		http.Error(w, "user and app query params required", http.StatusBadRequest)
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

func writeJSON(w http.ResponseWriter, v any) {
	w.Header().Set("Content-Type", "application/json")
	_ = json.NewEncoder(w).Encode(v)
}

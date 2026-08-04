package agent

import (
	"encoding/json"
	"net/http"
)

// Handler serves the host agent HTTP API.
type Handler struct {
	Manager *Manager
}

func (h *Handler) Mount(mux *http.ServeMux) {
	mux.HandleFunc("POST /v1/instances/ensure", h.ensure)
	mux.HandleFunc("POST /v1/instances/stop", h.stop)
	mux.HandleFunc("GET /healthz", func(w http.ResponseWriter, _ *http.Request) {
		w.WriteHeader(http.StatusOK)
		_, _ = w.Write([]byte("ok"))
	})
}

type ensureRequest struct {
	User string `json:"user"`
	App  string `json:"app"`
}

type ensureResponse struct {
	Addr    string `json:"addr"`
	GuestIP string `json:"guest_ip"`
}

func (h *Handler) ensure(w http.ResponseWriter, r *http.Request) {
	var req ensureRequest
	if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
		http.Error(w, err.Error(), http.StatusBadRequest)
		return
	}
	in, err := h.Manager.Ensure(r.Context(), req.User, req.App)
	if err != nil {
		http.Error(w, err.Error(), http.StatusInternalServerError)
		return
	}
	_ = json.NewEncoder(w).Encode(ensureResponse{Addr: in.Addr, GuestIP: in.GuestIP})
}

func (h *Handler) stop(w http.ResponseWriter, r *http.Request) {
	var req ensureRequest
	if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
		http.Error(w, err.Error(), http.StatusBadRequest)
		return
	}
	if err := h.Manager.Stop(req.User, req.App); err != nil {
		http.Error(w, err.Error(), http.StatusInternalServerError)
		return
	}
	w.WriteHeader(http.StatusNoContent)
}

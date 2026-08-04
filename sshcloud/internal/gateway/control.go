package gateway

import (
	"context"
	"crypto/rand"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"io"
	"net/http"
	"sync"
	"time"

	"github.com/imjasonh/playground/sshcloud/internal/controlauth"
	"github.com/imjasonh/playground/sshcloud/internal/genid"
	"github.com/imjasonh/playground/sshcloud/internal/names"
)

// ControlHandler serves the orchestrator→gateway migration API.
type ControlHandler struct {
	Hub       *Hub
	Token     string
	MaxFreeze time.Duration

	mu     sync.Mutex
	frozen map[string]frozenSession
}

type frozenSession struct {
	User  string
	App   string
	Gen   string
	timer *time.Timer
}

type freezeRequest struct {
	User      string `json:"user"`
	App       string `json:"app"`
	Gen       string `json:"gen,omitempty"`
	TimeoutMS int64  `json:"timeout_ms,omitempty"`
}

type thawRequest struct {
	Token string `json:"token"`
}

// Mount registers authenticated migration control routes.
func (h *ControlHandler) Mount(mux *http.ServeMux) {
	if h.MaxFreeze <= 0 {
		h.MaxFreeze = 30 * time.Second
	}
	if h.frozen == nil {
		h.frozen = make(map[string]frozenSession)
	}
	api := http.NewServeMux()
	api.HandleFunc("POST /v1/sessions/freeze", h.freeze)
	api.HandleFunc("POST /v1/sessions/thaw", h.thaw)
	api.HandleFunc("POST /v1/sessions/abort", h.abort)
	mux.Handle("/v1/", controlauth.Require(h.Token, api))
	mux.HandleFunc("GET /healthz", func(w http.ResponseWriter, _ *http.Request) {
		w.WriteHeader(http.StatusOK)
		_, _ = w.Write([]byte("ok"))
	})
}

func (h *ControlHandler) freeze(w http.ResponseWriter, r *http.Request) {
	var req freezeRequest
	if !decodeControlJSON(w, r, &req) || !validateControlIdentity(w, req.User, req.App, req.Gen) {
		return
	}
	timeout := time.Duration(req.TimeoutMS) * time.Millisecond
	if timeout <= 0 || timeout > h.MaxFreeze {
		timeout = h.MaxFreeze
	}
	freezeCtx, cancel := context.WithTimeout(r.Context(), 10*time.Second)
	defer cancel()
	count, err := h.Hub.FreezeApp(freezeCtx, req.User, req.App, req.Gen)
	if err != nil {
		http.Error(w, err.Error(), http.StatusConflict)
		return
	}
	token := migrationToken()
	op := frozenSession{User: req.User, App: req.App, Gen: req.Gen}
	op.timer = time.AfterFunc(timeout, func() {
		h.mu.Lock()
		current, ok := h.frozen[token]
		if ok {
			delete(h.frozen, token)
		}
		h.mu.Unlock()
		if ok {
			h.Hub.KickApp(current.User, current.App, current.Gen)
		}
	})
	h.mu.Lock()
	h.frozen[token] = op
	h.mu.Unlock()
	writeControlJSON(w, map[string]any{
		"token": token, "sessions": count, "deadline": time.Now().Add(timeout).UTC(),
	})
}

func (h *ControlHandler) thaw(w http.ResponseWriter, r *http.Request) {
	var req thawRequest
	if !decodeControlJSON(w, r, &req) {
		return
	}
	op, ok := h.take(req.Token)
	if !ok {
		http.Error(w, "unknown or expired freeze token", http.StatusNotFound)
		return
	}
	ctx, cancel := context.WithTimeout(r.Context(), 10*time.Second)
	defer cancel()
	count, err := h.Hub.ThawApp(ctx, op.User, op.App, op.Gen)
	if err != nil {
		http.Error(w, err.Error(), http.StatusConflict)
		return
	}
	writeControlJSON(w, map[string]any{"sessions": count})
}

func (h *ControlHandler) abort(w http.ResponseWriter, r *http.Request) {
	var req thawRequest
	if !decodeControlJSON(w, r, &req) {
		return
	}
	op, ok := h.take(req.Token)
	if !ok {
		http.Error(w, "unknown or expired freeze token", http.StatusNotFound)
		return
	}
	count := h.Hub.KickApp(op.User, op.App, op.Gen)
	writeControlJSON(w, map[string]any{"sessions": count})
}

func (h *ControlHandler) take(token string) (frozenSession, bool) {
	h.mu.Lock()
	defer h.mu.Unlock()
	op, ok := h.frozen[token]
	if ok {
		delete(h.frozen, token)
		op.timer.Stop()
	}
	return op, ok
}

func migrationToken() string {
	var b [16]byte
	if _, err := rand.Read(b[:]); err != nil {
		return fmt.Sprintf("freeze-%d", time.Now().UnixNano())
	}
	return hex.EncodeToString(b[:])
}

func validateControlIdentity(w http.ResponseWriter, user, app, gen string) bool {
	if err := names.ValidateIdent(user); err != nil {
		http.Error(w, "invalid user: "+err.Error(), http.StatusBadRequest)
		return false
	}
	if err := names.ValidateIdent(app); err != nil {
		http.Error(w, "invalid app: "+err.Error(), http.StatusBadRequest)
		return false
	}
	if gen != "" {
		if err := genid.Validate(gen); err != nil {
			http.Error(w, err.Error(), http.StatusBadRequest)
			return false
		}
	}
	return true
}

func decodeControlJSON(w http.ResponseWriter, r *http.Request, dst any) bool {
	r.Body = http.MaxBytesReader(w, r.Body, 8<<10)
	dec := json.NewDecoder(r.Body)
	dec.DisallowUnknownFields()
	if err := dec.Decode(dst); err != nil {
		http.Error(w, "invalid JSON: "+err.Error(), http.StatusBadRequest)
		return false
	}
	if err := dec.Decode(&struct{}{}); err != io.EOF {
		http.Error(w, "request body must contain one JSON object", http.StatusBadRequest)
		return false
	}
	return true
}

func writeControlJSON(w http.ResponseWriter, value any) {
	w.Header().Set("Content-Type", "application/json")
	_ = json.NewEncoder(w).Encode(value)
}

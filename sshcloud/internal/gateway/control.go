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

	"github.com/imjasonh/playground/sshcloud/internal/genid"
	"github.com/imjasonh/playground/sshcloud/internal/healthhttp"
	"github.com/imjasonh/playground/sshcloud/internal/names"
	"github.com/imjasonh/playground/sshcloud/internal/session"
)

// ControlHandler serves the orchestrator→gateway migration API.
type ControlHandler struct {
	Hub       *Hub
	MaxFreeze time.Duration

	mu        sync.Mutex
	frozen    map[string]frozenSession
	bySession map[session.ID]string
	finished  map[string]time.Time
}

type frozenSession struct {
	User  string
	App   string
	Gen   string
	IDs   []session.ID
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

// Mount registers migration control routes. The production command wraps this
// mux in orchestrator-only mTLS and GCE identity-token authentication.
func (h *ControlHandler) Mount(mux *http.ServeMux) {
	if h.MaxFreeze <= 0 {
		h.MaxFreeze = 30 * time.Second
	}
	if h.frozen == nil {
		h.frozen = make(map[string]frozenSession)
	}
	if h.bySession == nil {
		h.bySession = make(map[session.ID]string)
	}
	if h.finished == nil {
		h.finished = make(map[string]time.Time)
	}
	api := http.NewServeMux()
	api.HandleFunc("POST /v1/sessions/freeze", h.freeze)
	api.HandleFunc("POST /v1/sessions/thaw", h.thaw)
	api.HandleFunc("POST /v1/sessions/abort", h.abort)
	mux.Handle("/v1/", api)
}

// MountHealth registers only body-free health endpoints on a separate HTTP
// listener.
func (h *ControlHandler) MountHealth(mux *http.ServeMux) {
	ready := func(w http.ResponseWriter, r *http.Request) {
		if h.Hub == nil {
			http.Error(w, "unavailable", http.StatusServiceUnavailable)
			return
		}
		readyCtx, cancel := context.WithTimeout(r.Context(), 4*time.Second)
		defer cancel()
		if err := h.Hub.Ready(readyCtx); err != nil {
			http.Error(w, "unavailable", http.StatusServiceUnavailable)
			return
		}
		w.WriteHeader(http.StatusOK)
		_, _ = w.Write([]byte("ok"))
	}
	healthhttp.Mount(mux, ready)
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
	ids := h.Hub.SessionIDs(req.User, req.App, req.Gen)
	token := migrationToken()
	op := frozenSession{User: req.User, App: req.App, Gen: req.Gen, IDs: ids}
	h.mu.Lock()
	for _, id := range ids {
		if existing := h.bySession[id]; existing != "" {
			h.mu.Unlock()
			http.Error(w, "session already has active freeze token "+existing, http.StatusConflict)
			return
		}
	}
	h.frozen[token] = op
	for _, id := range ids {
		h.bySession[id] = token
	}
	h.mu.Unlock()

	freezeCtx, cancel := context.WithTimeout(r.Context(), 10*time.Second)
	err := h.Hub.FreezeSessions(freezeCtx, ids)
	cancel()
	if err != nil {
		rollbackCtx, rollbackCancel := context.WithTimeout(context.Background(), 5*time.Second)
		rollbackErr := h.Hub.ThawSessions(rollbackCtx, ids)
		rollbackCancel()
		if rollbackErr != nil {
			h.Hub.KickSessions(ids)
		}
		h.remove(token)
		http.Error(w, err.Error(), http.StatusConflict)
		return
	}
	op.timer = time.AfterFunc(timeout, func() {
		current, ok := h.remove(token)
		if ok {
			h.Hub.KickSessions(current.IDs)
		}
	})
	h.mu.Lock()
	if _, ok := h.frozen[token]; ok {
		h.frozen[token] = op
	}
	h.mu.Unlock()
	writeControlJSON(w, map[string]any{
		"token": token, "sessions": len(ids), "deadline": time.Now().Add(timeout).UTC(),
	})
}

func (h *ControlHandler) thaw(w http.ResponseWriter, r *http.Request) {
	var req thawRequest
	if !decodeControlJSON(w, r, &req) {
		return
	}
	op, ok := h.get(req.Token)
	if !ok {
		if h.wasFinished(req.Token) {
			writeControlJSON(w, map[string]any{"sessions": 0, "already_thawed": true})
			return
		}
		http.Error(w, "unknown or expired freeze token", http.StatusNotFound)
		return
	}
	ctx, cancel := context.WithTimeout(r.Context(), 10*time.Second)
	defer cancel()
	err := h.Hub.ThawSessions(ctx, op.IDs)
	if err != nil {
		http.Error(w, err.Error(), http.StatusConflict)
		return
	}
	h.remove(req.Token)
	h.markFinished(req.Token)
	writeControlJSON(w, map[string]any{"sessions": len(op.IDs)})
}

func (h *ControlHandler) abort(w http.ResponseWriter, r *http.Request) {
	var req thawRequest
	if !decodeControlJSON(w, r, &req) {
		return
	}
	op, ok := h.remove(req.Token)
	if !ok {
		http.Error(w, "unknown or expired freeze token", http.StatusNotFound)
		return
	}
	count := h.Hub.KickSessions(op.IDs)
	writeControlJSON(w, map[string]any{"sessions": count})
}

func (h *ControlHandler) get(token string) (frozenSession, bool) {
	h.mu.Lock()
	defer h.mu.Unlock()
	op, ok := h.frozen[token]
	return op, ok
}

func (h *ControlHandler) remove(token string) (frozenSession, bool) {
	h.mu.Lock()
	defer h.mu.Unlock()
	op, ok := h.frozen[token]
	if ok {
		delete(h.frozen, token)
		for _, id := range op.IDs {
			if h.bySession[id] == token {
				delete(h.bySession, id)
			}
		}
		if op.timer != nil {
			op.timer.Stop()
		}
	}
	return op, ok
}

func (h *ControlHandler) markFinished(token string) {
	h.mu.Lock()
	defer h.mu.Unlock()
	now := time.Now()
	for existing, until := range h.finished {
		if !until.After(now) {
			delete(h.finished, existing)
		}
	}
	h.finished[token] = now.Add(time.Minute)
}

func (h *ControlHandler) wasFinished(token string) bool {
	h.mu.Lock()
	defer h.mu.Unlock()
	until, ok := h.finished[token]
	if ok && !until.After(time.Now()) {
		delete(h.finished, token)
		return false
	}
	return ok
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

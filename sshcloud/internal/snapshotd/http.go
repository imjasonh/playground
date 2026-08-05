package snapshotd

import (
	"context"
	"encoding/json"
	"errors"
	"io"
	"net/http"
	"os"
	"path/filepath"
	"time"

	"github.com/imjasonh/playground/sshcloud/internal/controlauth"
	"github.com/imjasonh/playground/sshcloud/internal/observability"
	"github.com/imjasonh/playground/sshcloud/internal/snapshot"
)

type Handler struct {
	Store          snapshot.Store
	Authorizer     *Authorizer
	ExpectedLayout string
	TempDir        string
}

func (h *Handler) Mount(mux *http.ServeMux) {
	mux.HandleFunc("GET /v1/healthz", h.health)
	mux.HandleFunc("PUT /v1/snapshots/package", h.put)
	mux.HandleFunc("POST /v1/snapshots/get", h.get)
	mux.HandleFunc("POST /v1/snapshots/has", h.has)
	mux.HandleFunc("POST /v1/snapshots/meta", h.meta)
	mux.HandleFunc("POST /v1/snapshots/delete", h.delete)
}

func (h *Handler) MountHealth(mux *http.ServeMux) {
	mux.HandleFunc("GET /livez", func(w http.ResponseWriter, _ *http.Request) {
		w.WriteHeader(http.StatusOK)
		_, _ = w.Write([]byte("ok"))
	})
	mux.HandleFunc("GET /readyz", h.health)
	mux.HandleFunc("GET /healthz", h.health)
}

func (h *Handler) health(w http.ResponseWriter, r *http.Request) {
	if h.Store == nil {
		http.Error(w, "unavailable", http.StatusServiceUnavailable)
		return
	}
	if err := h.Store.Health(r.Context()); err != nil {
		http.Error(w, "unavailable", http.StatusServiceUnavailable)
		return
	}
	if h.Authorizer == nil || h.Authorizer.Placement == nil {
		http.Error(w, "unavailable", http.StatusServiceUnavailable)
		return
	}
	if _, err := h.Authorizer.Placement.ListRecords(r.Context()); err != nil {
		http.Error(w, "unavailable", http.StatusServiceUnavailable)
		return
	}
	w.WriteHeader(http.StatusOK)
	_, _ = w.Write([]byte("ok"))
}

func (h *Handler) put(w http.ResponseWriter, r *http.Request) {
	ref, err := snapshot.ParseRefHeader(r)
	if err != nil {
		http.Error(w, "invalid snapshot reference", http.StatusBadRequest)
		return
	}
	startedAt := time.Now()
	outcome := observability.OutcomeFailure
	defer func() { emitSnapshotEvent(ref, "put", outcome, startedAt) }()
	if !h.authorize(w, r, ref, ActionPut) {
		outcome = observability.OutcomeRejected
		return
	}
	r.Body = http.MaxBytesReader(w, r.Body, snapshot.MaxRequestBytes)
	temp, err := h.tempPackage("put")
	if err != nil {
		http.Error(w, "snapshot staging unavailable", http.StatusInternalServerError)
		return
	}
	defer os.RemoveAll(filepath.Dir(temp))
	if _, err := snapshot.ReadArchive(r.Context(), r.Body, ref, temp, h.ExpectedLayout); err != nil {
		var tooLarge *http.MaxBytesError
		if errors.As(err, &tooLarge) {
			http.Error(w, "snapshot request is too large", http.StatusRequestEntityTooLarge)
			return
		}
		http.Error(w, "invalid snapshot package", http.StatusBadRequest)
		return
	}
	var trailing [1]byte
	if n, err := r.Body.Read(trailing[:]); n != 0 || (err != nil && err != io.EOF) {
		http.Error(w, "snapshot package contains trailing bytes", http.StatusBadRequest)
		return
	}
	if err := h.Store.Put(r.Context(), ref, snapshot.NewPackageDir(temp)); err != nil {
		writeStoreError(w, err)
		return
	}
	w.WriteHeader(http.StatusNoContent)
	outcome = observability.OutcomeSuccess
}

func (h *Handler) get(w http.ResponseWriter, r *http.Request) {
	ref, ok := decodeRef(w, r)
	if !ok {
		return
	}
	startedAt := time.Now()
	outcome := observability.OutcomeFailure
	defer func() { emitSnapshotEvent(ref, "get", outcome, startedAt) }()
	if !h.authorize(w, r, ref, ActionGet) {
		outcome = observability.OutcomeRejected
		return
	}
	temp, err := h.tempPackage("get")
	if err != nil {
		http.Error(w, "snapshot staging unavailable", http.StatusInternalServerError)
		return
	}
	defer os.RemoveAll(filepath.Dir(temp))
	pkg, err := h.Store.Get(r.Context(), ref, temp)
	if err != nil {
		writeStoreError(w, err)
		return
	}
	w.Header().Set("Content-Type", "application/vnd.sshcloud.snapshot+tar")
	w.Header().Set("X-Content-Type-Options", "nosniff")
	if err := snapshot.WriteArchive(r.Context(), w, ref, pkg, h.ExpectedLayout); err != nil {
		return
	}
	outcome = observability.OutcomeSuccess
}

func (h *Handler) has(w http.ResponseWriter, r *http.Request) {
	ref, ok := decodeRef(w, r)
	if !ok {
		return
	}
	startedAt := time.Now()
	outcome := observability.OutcomeFailure
	defer func() { emitSnapshotEvent(ref, "has", outcome, startedAt) }()
	if !h.authorize(w, r, ref, ActionHas) {
		outcome = observability.OutcomeRejected
		return
	}
	exists, err := h.Store.Has(r.Context(), ref)
	if err != nil {
		writeStoreError(w, err)
		return
	}
	writeJSON(w, map[string]bool{"exists": exists})
	outcome = observability.OutcomeSuccess
}

func (h *Handler) meta(w http.ResponseWriter, r *http.Request) {
	ref, ok := decodeRef(w, r)
	if !ok {
		return
	}
	startedAt := time.Now()
	outcome := observability.OutcomeFailure
	defer func() { emitSnapshotEvent(ref, "meta", outcome, startedAt) }()
	if !h.authorize(w, r, ref, ActionMeta) {
		outcome = observability.OutcomeRejected
		return
	}
	meta, err := h.Store.Meta(r.Context(), ref)
	if err != nil {
		writeStoreError(w, err)
		return
	}
	writeJSON(w, meta)
	outcome = observability.OutcomeSuccess
}

func (h *Handler) delete(w http.ResponseWriter, r *http.Request) {
	ref, ok := decodeRef(w, r)
	if !ok {
		return
	}
	startedAt := time.Now()
	outcome := observability.OutcomeFailure
	defer func() { emitSnapshotEvent(ref, "delete", outcome, startedAt) }()
	if !h.authorize(w, r, ref, ActionDelete) {
		outcome = observability.OutcomeRejected
		return
	}
	if err := h.Store.Delete(r.Context(), ref); err != nil {
		writeStoreError(w, err)
		return
	}
	w.WriteHeader(http.StatusNoContent)
	outcome = observability.OutcomeSuccess
}

func emitSnapshotEvent(ref snapshot.Ref, action string, outcome observability.Outcome, startedAt time.Time) {
	observability.Emit(observability.SnapshotEvent{
		Identity: observability.RuntimeIdentity{User: ref.User, App: ref.App, Generation: ref.Gen},
		Action:   action, Outcome: outcome, Duration: time.Since(startedAt),
	})
}

func (h *Handler) authorize(w http.ResponseWriter, r *http.Request, ref snapshot.Ref, action Action) bool {
	identity, ok := controlauth.IdentityFromContext(r.Context())
	if !ok || h.Authorizer == nil {
		http.Error(w, "forbidden", http.StatusForbidden)
		return false
	}
	if err := h.Authorizer.Authorize(r.Context(), identity, ref, action); err != nil {
		if errors.Is(err, ErrForbidden) {
			http.Error(w, "forbidden", http.StatusForbidden)
		} else {
			http.Error(w, "authorization unavailable", http.StatusServiceUnavailable)
		}
		return false
	}
	return true
}

func (h *Handler) tempPackage(operation string) (string, error) {
	root, err := os.MkdirTemp(h.TempDir, "sshcloud-snapshotd-"+operation+"-")
	if err != nil {
		return "", err
	}
	return filepath.Join(root, "package"), nil
}

func decodeRef(w http.ResponseWriter, r *http.Request) (snapshot.Ref, bool) {
	r.Body = http.MaxBytesReader(w, r.Body, 8<<10)
	var ref snapshot.Ref
	decoder := json.NewDecoder(r.Body)
	decoder.DisallowUnknownFields()
	if err := decoder.Decode(&ref); err != nil {
		http.Error(w, "invalid snapshot reference", http.StatusBadRequest)
		return snapshot.Ref{}, false
	}
	if err := decoder.Decode(&struct{}{}); err != io.EOF {
		http.Error(w, "snapshot reference must contain one JSON object", http.StatusBadRequest)
		return snapshot.Ref{}, false
	}
	if err := ref.Validate(); err != nil {
		http.Error(w, "invalid snapshot reference", http.StatusBadRequest)
		return snapshot.Ref{}, false
	}
	return ref, true
}

func writeStoreError(w http.ResponseWriter, err error) {
	switch {
	case errors.Is(err, os.ErrNotExist), errors.Is(err, snapshot.ErrObjectNotFound):
		http.Error(w, "snapshot not found", http.StatusNotFound)
	case errors.Is(err, snapshot.ErrConcurrentPublication), errors.Is(err, snapshot.ErrObjectPrecondition):
		http.Error(w, "snapshot publication conflict", http.StatusConflict)
	case errors.Is(err, context.Canceled), errors.Is(err, context.DeadlineExceeded):
		http.Error(w, "snapshot operation canceled", http.StatusRequestTimeout)
	default:
		http.Error(w, "snapshot operation failed", http.StatusInternalServerError)
	}
}

func writeJSON(w http.ResponseWriter, value any) {
	w.Header().Set("Content-Type", "application/json")
	w.Header().Set("X-Content-Type-Options", "nosniff")
	_ = json.NewEncoder(w).Encode(value)
}

package main

import (
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"net/http"

	"github.com/imjasonh/playground/sshcloud/internal/backend"
	"github.com/imjasonh/playground/sshcloud/internal/genid"
	"github.com/imjasonh/playground/sshcloud/internal/names"
	"github.com/imjasonh/playground/sshcloud/internal/placement"
	"github.com/imjasonh/playground/sshcloud/internal/quota"
)

func validateIdentity(user, app, gen string) error {
	if err := names.ValidateIdent(user); err != nil {
		return fmt.Errorf("invalid user: %w", err)
	}
	if err := names.ValidateIdent(app); err != nil {
		return fmt.Errorf("invalid app: %w", err)
	}
	if gen != "" {
		if err := genid.Validate(gen); err != nil {
			return err
		}
	}
	return nil
}

func decodeJSON(w http.ResponseWriter, r *http.Request, dst any) bool {
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

func writeControlError(w http.ResponseWriter, err error) {
	var held placement.ErrLeaseHeld
	var lost placement.ErrLeaseLost
	var recovery placement.ErrRecoveryRequired
	var capacity backend.ErrAgentCapacity
	var exceeded quota.ErrExceeded
	switch {
	case errors.As(err, &exceeded):
		http.Error(w, err.Error(), http.StatusTooManyRequests)
	case errors.As(err, &held), errors.As(err, &lost), errors.As(err, &recovery):
		http.Error(w, err.Error(), http.StatusConflict)
	case errors.As(err, &capacity):
		http.Error(w, err.Error(), http.StatusServiceUnavailable)
	default:
		http.Error(w, err.Error(), http.StatusInternalServerError)
	}
}

package gateway

import (
	"errors"

	"github.com/imjasonh/playground/sshcloud/internal/access"
)

type forbiddenError struct {
	reason string
}

func (e forbiddenError) Error() string {
	return "forbidden: " + e.reason
}

func (h *Hub) currentAccessPolicy() (access.Policy, error) {
	if h.Access == nil {
		return access.LocalDevelopmentPolicy(), nil
	}
	return h.Access.Load()
}

func (h *Hub) authorizeUse(keyFingerprint string) error {
	policy, err := h.currentAccessPolicy()
	if err != nil {
		return forbiddenError{reason: "the access policy is unavailable; contact the operator"}
	}
	if !policy.AllowsUse(keyFingerprint) {
		return forbiddenError{reason: "this SSH key is not admitted by the current access policy"}
	}
	return nil
}

// AllowsKey reports whether the current policy still permits a key to use the
// platform. SSH servers use it to terminate already-open connections after an
// operator removes a key from a private allowlist.
func (h *Hub) AllowsKey(keyFingerprint string) bool {
	return h.authorizeUse(keyFingerprint) == nil
}

func (h *Hub) authorizeDeploy(keyFingerprint, userID string) error {
	policy, err := h.currentAccessPolicy()
	if err != nil {
		return forbiddenError{reason: "the access policy is unavailable; contact the operator"}
	}
	if !policy.AllowsDeploy(keyFingerprint, userID != "") {
		return forbiddenError{reason: "this SSH key is not allowed to deploy"}
	}
	return nil
}

func isForbidden(err error) bool {
	var forbidden forbiddenError
	return errors.As(err, &forbidden)
}

func forbiddenMessage(err error) string {
	var forbidden forbiddenError
	if errors.As(err, &forbidden) {
		return "Forbidden: " + forbidden.reason + "."
	}
	return "Forbidden."
}

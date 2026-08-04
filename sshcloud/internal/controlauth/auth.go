// Package controlauth authenticates requests between trusted platform services.
//
// This bearer-token mechanism is an interim control-plane boundary for the
// single-environment prototype. It is deliberately small so it can be replaced
// by workload identity plus mTLS without changing individual API handlers.
package controlauth

import (
	"crypto/subtle"
	"fmt"
	"net/http"
	"os"
	"strings"
)

const header = "Authorization"

// LoadFile reads a control-plane bearer token from path.
func LoadFile(path string) (string, error) {
	path = strings.TrimSpace(path)
	if path == "" {
		return "", nil
	}
	b, err := os.ReadFile(path)
	if err != nil {
		return "", err
	}
	token := strings.TrimSpace(string(b))
	if len(token) < 32 {
		return "", fmt.Errorf("control token must be at least 32 characters")
	}
	return token, nil
}

// Add attaches token to an outgoing request. Empty tokens are allowed for
// explicit local development configurations where the server also has no token.
func Add(req *http.Request, token string) {
	if req != nil && token != "" {
		req.Header.Set(header, "Bearer "+token)
	}
}

// Require protects an HTTP handler with a constant-time bearer-token check.
// An empty token leaves the handler open for local development.
func Require(token string, next http.Handler) http.Handler {
	if token == "" {
		return next
	}
	return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		got := strings.TrimPrefix(r.Header.Get(header), "Bearer ")
		if len(got) != len(token) || subtle.ConstantTimeCompare([]byte(got), []byte(token)) != 1 {
			w.Header().Set("WWW-Authenticate", "Bearer")
			http.Error(w, "unauthorized", http.StatusUnauthorized)
			return
		}
		next.ServeHTTP(w, r)
	})
}

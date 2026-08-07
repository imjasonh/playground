// Package healthhttp provides the uniform, unauthenticated health-only HTTP
// surface shared by sshcloud services.
package healthhttp

import (
	"net/http"
	"time"

	"github.com/imjasonh/playground/sshcloud/internal/observability"
)

// Mount registers the standard liveness and readiness routes.
func Mount(mux *http.ServeMux, ready http.HandlerFunc) {
	mux.HandleFunc("GET /livez", func(w http.ResponseWriter, _ *http.Request) {
		w.WriteHeader(http.StatusOK)
		_, _ = w.Write([]byte("ok"))
	})
	mux.HandleFunc("GET /readyz", ready)
	mux.HandleFunc("GET /healthz", ready)
}

// NewServer constructs a bounded server on a dedicated health listener.
func NewServer(addr string, mount func(*http.ServeMux)) *http.Server {
	mux := http.NewServeMux()
	mount(mux)
	mux.Handle("GET /metrics", observability.MetricsHandler())
	return &http.Server{
		Addr: addr, Handler: mux,
		ReadHeaderTimeout: 5 * time.Second, ReadTimeout: 5 * time.Second,
		WriteTimeout: 5 * time.Second, IdleTimeout: 30 * time.Second,
	}
}

// Package handler is the hello-world HTTP service this app ships.
//
// It is deliberately ordinary net/http. Nothing in here knows about
// WebAssembly: the same http.Handler serves a real TCP listener when built for
// a real OS (see ../main.go) and is driven one request at a time by the host
// when built for wasip1 (see ../wasm.go). Keeping the wasm-ness out of the
// handler is the point — the payload is just a Go web service.
package handler

import (
	"encoding/json"
	"fmt"
	"io"
	"net/http"
	"runtime"
	"sort"
	"sync/atomic"
	"time"
)

// Service holds the state that outlives a single request. The iOS host keeps
// one instantiated module alive across requests, so a counter here is a cheap
// way to see, from the outside, that the guest really is long-lived rather
// than re-instantiated per request.
type Service struct {
	started  time.Time
	requests atomic.Uint64
	greeting string
}

// New returns the service's routes. `greeting` is whatever the host wants the
// root page to say; empty means the default.
func New(greeting string) http.Handler {
	if greeting == "" {
		greeting = "Hello from Go, compiled to WebAssembly."
	}
	service := &Service{started: time.Now(), greeting: greeting}

	mux := http.NewServeMux()
	mux.HandleFunc("/", service.root)
	mux.HandleFunc("/healthz", service.health)
	mux.HandleFunc("/info", service.info)
	mux.HandleFunc("/echo", service.echo)
	return service.count(mux)
}

// count increments the request counter around every request, including the
// 404s the mux generates, so /info reports the honest total.
func (s *Service) count(next http.Handler) http.Handler {
	return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		s.requests.Add(1)
		next.ServeHTTP(w, r)
	})
}

func (s *Service) root(w http.ResponseWriter, r *http.Request) {
	if r.URL.Path != "/" {
		http.NotFound(w, r)
		return
	}
	w.Header().Set("Content-Type", "text/plain; charset=utf-8")
	fmt.Fprintf(w, "%s\n\n", s.greeting)
	fmt.Fprintf(w, "runtime:  %s %s/%s\n", runtime.Version(), runtime.GOOS, runtime.GOARCH)
	fmt.Fprintf(w, "uptime:   %s\n", s.uptime())
	fmt.Fprintf(w, "requests: %d\n", s.requests.Load())
	fmt.Fprintf(w, "\nTry /healthz, /info, or POST to /echo.\n")
}

func (s *Service) health(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "text/plain; charset=utf-8")
	fmt.Fprintln(w, "ok")
}

func (s *Service) info(w http.ResponseWriter, r *http.Request) {
	body := map[string]any{
		"greeting":   s.greeting,
		"goVersion":  runtime.Version(),
		"goos":       runtime.GOOS,
		"goarch":     runtime.GOARCH,
		"uptime":     s.uptime().String(),
		"requests":   s.requests.Load(),
		"goroutines": runtime.NumGoroutine(),
	}
	w.Header().Set("Content-Type", "application/json")
	encoder := json.NewEncoder(w)
	encoder.SetIndent("", "  ")
	_ = encoder.Encode(body)
}

// echo reflects the request back, which is the quickest way to confirm the
// host handed the guest a well-formed request rather than something mangled by
// the trip through linear memory.
func (s *Service) echo(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "text/plain; charset=utf-8")
	fmt.Fprintf(w, "%s %s %s\n", r.Method, r.URL.RequestURI(), r.Proto)
	fmt.Fprintf(w, "Host: %s\n", r.Host)
	for _, name := range sortedKeys(r.Header) {
		for _, value := range r.Header[name] {
			fmt.Fprintf(w, "%s: %s\n", name, value)
		}
	}
	fmt.Fprintln(w)
	if r.Body != nil {
		_, _ = copyBody(w, r)
	}
}

// uptime is rounded because the exact nanosecond is noise, and because it
// makes the /info response stable enough to eyeball.
func (s *Service) uptime() time.Duration {
	return time.Since(s.started).Round(time.Millisecond)
}

func sortedKeys(header http.Header) []string {
	names := make([]string, 0, len(header))
	for name := range header {
		names = append(names, name)
	}
	sort.Strings(names)
	return names
}

func copyBody(w http.ResponseWriter, r *http.Request) (int64, error) {
	// Bounded so a runaway client cannot make the guest allocate the host's
	// memory limit; the guest has nowhere to spill to.
	return io.Copy(w, io.LimitReader(r.Body, 1<<20))
}

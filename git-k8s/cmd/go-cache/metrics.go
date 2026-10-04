package main

import (
	"fmt"
	"maps"
	"net/http"
	"slices"
	"strings"
	"sync"
	"sync/atomic"
)

// metrics counts go-cache's requests, in the Prometheus text format.
type metrics struct {
	mu      sync.Mutex
	build   map[string]int64 // by method and result, as "GET hit"
	modules map[string]int64 // by result

	stored  atomic.Int64
	evicted atomic.Int64
}

func newMetrics() *metrics {
	m := &metrics{build: map[string]int64{}, modules: map[string]int64{}}
	for _, r := range []string{"hit", "miss", "invalid", "denied", "error"} {
		m.build["GET "+r] = 0
	}
	for _, r := range []string{"created", "exists", "conflict", "invalid", "denied", "full", "busy", "error"} {
		m.build["PUT "+r] = 0
	}
	for _, r := range []string{"hit", "fetched", "passthrough", "not_found", "full", "busy", "error"} {
		m.modules[r] = 0
	}
	return m
}

func (m *metrics) buildRequest(method, result string) {
	m.mu.Lock()
	defer m.mu.Unlock()
	m.build[method+" "+result]++
}

func (m *metrics) moduleRequest(result string) {
	m.mu.Lock()
	defer m.mu.Unlock()
	m.modules[result]++
}

func (m *metrics) serve(w http.ResponseWriter, _ *http.Request) {
	var b strings.Builder
	m.mu.Lock()
	b.WriteString("# HELP go_cache_build_requests_total Requests to the build caches, by method and result.\n")
	b.WriteString("# TYPE go_cache_build_requests_total counter\n")
	for _, k := range slices.Sorted(maps.Keys(m.build)) {
		method, result, _ := strings.Cut(k, " ")
		fmt.Fprintf(&b, "go_cache_build_requests_total{method=%q,result=%q} %d\n", method, result, m.build[k])
	}
	b.WriteString("# HELP go_cache_module_requests_total Requests to the module proxy, by result.\n")
	b.WriteString("# TYPE go_cache_module_requests_total counter\n")
	for _, k := range slices.Sorted(maps.Keys(m.modules)) {
		fmt.Fprintf(&b, "go_cache_module_requests_total{result=%q} %d\n", k, m.modules[k])
	}
	m.mu.Unlock()
	b.WriteString("# HELP go_cache_stored_bytes Bytes of modules and build outputs in the store.\n")
	b.WriteString("# TYPE go_cache_stored_bytes gauge\n")
	fmt.Fprintf(&b, "go_cache_stored_bytes %d\n", m.stored.Load())
	b.WriteString("# HELP go_cache_evicted_bytes_total Bytes that the store removed to stay under -max-size.\n")
	b.WriteString("# TYPE go_cache_evicted_bytes_total counter\n")
	fmt.Fprintf(&b, "go_cache_evicted_bytes_total %d\n", m.evicted.Load())
	w.Header().Set("Content-Type", "text/plain; version=0.0.4; charset=utf-8")
	fmt.Fprint(w, b.String())
}

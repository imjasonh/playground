// Package observe records latency histograms and serves them in the
// Prometheus text format. It has no dependencies, so it doesn't export to
// Cloud Monitoring or Cloud Trace the way cloudrun-sqlite does; the
// histogram names match that service's, so the same queries work on both.
package observe

import (
	"fmt"
	"io"
	"log/slog"
	"net/http"
	"slices"
	"strconv"
	"strings"
	"sync"
	"time"
)

// Histogram names.
const (
	// HTTPServer is a request's time in the server, labeled with its route.
	HTTPServer = "http.server"
	// StorePhase is one part of a read or write, labeled with its phase.
	StorePhase = "store.phase"
	// StoreWrite is a write from the call to its acknowledgement, labeled
	// with durable and result.
	StoreWrite = "store.write"
	// ReplicaOperation is one object-storage call, labeled with op.
	ReplicaOperation = "replica.operation"
)

var help = map[string]string{
	HTTPServer:       "Time a request spent in the server.",
	StorePhase:       "Time in one phase of a read or write.",
	StoreWrite:       "Time from a write call to its acknowledgement.",
	ReplicaOperation: "Time of one object-storage call.",
}

// bounds are the histogram bucket upper bounds in seconds.
var bounds = []float64{0.0005, 0.001, 0.0025, 0.005, 0.01, 0.025, 0.05, 0.1, 0.25, 0.5, 1, 2.5, 5, 10, 30}

type series struct {
	labels string
	counts []uint64
	sum    float64
	n      uint64
}

var (
	mu   sync.Mutex
	hist = map[string]map[string]*series{}
)

// Measure adds d to the named histogram. labels are key, value pairs.
func Measure(name string, d time.Duration, labels ...string) {
	var b strings.Builder
	for i := 0; i+1 < len(labels); i += 2 {
		if i > 0 {
			b.WriteByte(',')
		}
		fmt.Fprintf(&b, "%s=%q", labels[i], labels[i+1])
	}
	key := b.String()
	secs := d.Seconds()
	mu.Lock()
	defer mu.Unlock()
	m := hist[name]
	if m == nil {
		m = map[string]*series{}
		hist[name] = m
	}
	s := m[key]
	if s == nil {
		s = &series{labels: key, counts: make([]uint64, len(bounds))}
		m[key] = s
	}
	for i, ub := range bounds {
		if secs <= ub {
			s.counts[i]++
		}
	}
	s.sum += secs
	s.n++
}

// Metrics serves every histogram in the Prometheus text format, with dots
// in names replaced by underscores and _seconds appended.
func Metrics() http.Handler {
	return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		w.Header().Set("Content-Type", "text/plain; version=0.0.4")
		write(w)
	})
}

func write(w io.Writer) {
	mu.Lock()
	defer mu.Unlock()
	names := make([]string, 0, len(hist))
	for n := range hist {
		names = append(names, n)
	}
	slices.Sort(names)
	for _, n := range names {
		prom := strings.ReplaceAll(n, ".", "_") + "_seconds"
		fmt.Fprintf(w, "# HELP %s %s\n# TYPE %s histogram\n", prom, help[n], prom)
		keys := make([]string, 0, len(hist[n]))
		for k := range hist[n] {
			keys = append(keys, k)
		}
		slices.Sort(keys)
		for _, k := range keys {
			s := hist[n][k]
			sep := ""
			if k != "" {
				sep = ","
			}
			for i, ub := range bounds {
				fmt.Fprintf(w, "%s_bucket{%s%sle=%q} %d\n", prom, k, sep, strconv.FormatFloat(ub, 'g', -1, 64), s.counts[i])
			}
			fmt.Fprintf(w, "%s_bucket{%s%sle=\"+Inf\"} %d\n", prom, k, sep, s.n)
			fmt.Fprintf(w, "%s_sum{%s} %g\n%s_count{%s} %d\n", prom, k, s.sum, prom, k, s.n)
		}
	}
}

type statusWriter struct {
	http.ResponseWriter
	code int
}

func (w *statusWriter) WriteHeader(code int) {
	w.code = code
	w.ResponseWriter.WriteHeader(code)
}

func (w *statusWriter) Unwrap() http.ResponseWriter { return w.ResponseWriter }

// HTTP times each request by the route pattern that served it, and logs
// requests that took 200 ms or more or failed with a 5xx.
func HTTP(next http.Handler) http.Handler {
	return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		sw := &statusWriter{ResponseWriter: w, code: http.StatusOK}
		start := time.Now()
		next.ServeHTTP(sw, r)
		route := r.Pattern
		if route == "" {
			route = "unmatched"
		}
		d := time.Since(start)
		Measure(HTTPServer, d, "route", route)
		if route != "GET /events" && (d >= 200*time.Millisecond || sw.code >= 500) {
			slog.InfoContext(r.Context(), "slow or failed request", "route", route, "status", sw.code, "duration_ms", float64(d.Microseconds())/1000)
		}
	})
}

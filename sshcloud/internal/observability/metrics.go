package observability

import (
	"fmt"
	"io"
	"net/http"
	"sort"
	"strconv"
	"strings"
	"sync"
	"time"
)

type metricKind string

const (
	metricCounter metricKind = "counter"
	metricGauge   metricKind = "gauge"
)

type metricKey struct {
	name   string
	labels string
}

type metricValue struct {
	help  string
	kind  metricKind
	value float64
}

// Registry contains only platform-wide, low-cardinality metric dimensions.
// Its API deliberately has no user, app, generation, run, or session label.
type Registry struct {
	mu      sync.Mutex
	values  map[metricKey]metricValue
	collect []func()
}

// NewRegistry returns an aggregate registry with a fixed process heartbeat.
func NewRegistry() *Registry {
	registry := &Registry{values: make(map[metricKey]metricValue)}
	registry.set(
		"sshcloud_up",
		"Whether the sshcloud process metrics endpoint is running.",
		"", 1,
	)
	return registry
}

var defaultMetrics = NewRegistry()

// DefaultMetrics is the process-wide Prometheus/OpenTelemetry-compatible
// registry.
func DefaultMetrics() *Registry { return defaultMetrics }

func labels(values ...string) string {
	if len(values)%2 != 0 {
		panic("metric labels must be key/value pairs")
	}
	var pairs []string
	for i := 0; i < len(values); i += 2 {
		pairs = append(pairs, values[i]+`="`+escapeLabel(values[i+1])+`"`)
	}
	sort.Strings(pairs)
	return strings.Join(pairs, ",")
}

func escapeLabel(value string) string {
	value = strings.ReplaceAll(value, `\`, `\\`)
	value = strings.ReplaceAll(value, "\n", `\n`)
	return strings.ReplaceAll(value, `"`, `\"`)
}

func (r *Registry) add(name, help string, kind metricKind, labelSet string, value float64) {
	if value < 0 && kind == metricCounter {
		return
	}
	r.mu.Lock()
	defer r.mu.Unlock()
	key := metricKey{name: name, labels: labelSet}
	current := r.values[key]
	current.help = help
	current.kind = kind
	current.value += value
	r.values[key] = current
}

func (r *Registry) set(name, help string, labelSet string, value float64) {
	r.mu.Lock()
	defer r.mu.Unlock()
	r.values[metricKey{name: name, labels: labelSet}] = metricValue{
		help: help, kind: metricGauge, value: value,
	}
}

// AddAppLogBytes records bytes that were accepted for emission or dropped by
// the host-side nonblocking console guard.
func (r *Registry) AddAppLogBytes(result string, bytes int) {
	if bytes <= 0 || !oneOf(result, "accepted", "dropped") {
		return
	}
	r.add(
		"sshcloud_app_log_bytes_total",
		"App console bytes accepted or dropped by the host log guard.",
		metricCounter, labels("result", result), float64(bytes),
	)
}

// AddConsoleRecord records bounded console/telemetry/diagnostic outcomes.
func (r *Registry) AddConsoleRecord(kind, result string) {
	if !oneOf(kind, "log", "telemetry", "diagnostic") ||
		!oneOf(result, "accepted", "dropped", "invalid", "truncated") {
		return
	}
	r.add(
		"sshcloud_console_records_total",
		"Bounded host console records by fixed kind and result.",
		metricCounter, labels("kind", kind, "result", result), 1,
	)
}

// AddDiagnosticsQueueBytes updates aggregate bounded VMM output queue
// pressure across every console sink in the process.
func (r *Registry) AddDiagnosticsQueueBytes(delta int64) {
	r.mu.Lock()
	defer r.mu.Unlock()
	key := metricKey{name: "sshcloud_diagnostics_queue_bytes"}
	current := r.values[key]
	current.help = "Bytes currently queued by nonblocking VMM output drains."
	current.kind = metricGauge
	current.value += float64(delta)
	if current.value < 0 {
		current.value = 0
	}
	r.values[key] = current
}

// ObserveOperation records one fixed platform operation. Values outside the
// schema are ignored to prevent label-cardinality expansion.
func (r *Registry) ObserveOperation(family, operation, outcome string, duration time.Duration) {
	if !allowedOperation(family, operation) ||
		!oneOf(outcome, "success", "failure", "rejected", "timeout") {
		return
	}
	name := "sshcloud_" + family + "_operations_total"
	help := "Metadata-only " + family + " operations by fixed operation and outcome."
	labelSet := labels("operation", operation, "outcome", outcome)
	r.add(name, help, metricCounter, labelSet, 1)
	if duration < 0 {
		duration = 0
	}
	durationLabels := labels("operation", operation)
	r.add(
		"sshcloud_"+family+"_operation_duration_seconds_sum",
		"Total duration of metadata-only "+family+" operations.",
		metricCounter, durationLabels, duration.Seconds(),
	)
	r.add(
		"sshcloud_"+family+"_operation_duration_seconds_count",
		"Count of timed metadata-only "+family+" operations.",
		metricCounter, durationLabels, 1,
	)
}

func allowedOperation(family, operation string) bool {
	switch family {
	case "lifecycle":
		return oneOf(operation, "boot", "restore", "sleep", "wake", "evict", "stop", "cordon", "uncordon")
	case "session":
		return oneOf(operation, "admit", "start", "end", "freeze", "thaw", "abort")
	case "deploy":
		return oneOf(operation, "deploy", "reconcile", "drain", "retire")
	case "snapshot":
		return oneOf(operation, "put", "get", "has", "meta", "delete", "create", "load")
	case "migration":
		return oneOf(operation, "migrate", "freeze", "thaw", "drain")
	default:
		return false
	}
}

// SetHostCapacity records one host's aggregate capacity. Cloud resource labels
// identify the host; metric labels remain fixed and tenant-free.
func (r *Registry) SetHostCapacity(totalVCPUs, usedVCPUs, reservedVCPUs, totalMemMiB, usedMemMiB, reservedMemMiB int64, cordoned bool) {
	for state, value := range map[string]int64{
		"total": totalVCPUs, "used": usedVCPUs, "reserved": reservedVCPUs,
	} {
		r.set("sshcloud_host_vcpus", "Host guest vCPU capacity.", labels("state", state), float64(max(value, 0)))
	}
	for state, value := range map[string]int64{
		"total": totalMemMiB, "used": usedMemMiB, "reserved": reservedMemMiB,
	} {
		r.set("sshcloud_host_memory_bytes", "Host guest memory capacity in bytes.", labels("state", state), float64(max(value, 0))*(1<<20))
	}
	cordon := 0.0
	if cordoned {
		cordon = 1
	}
	r.set("sshcloud_host_cordoned", "Whether this Firecracker host is cordoned.", "", cordon)
}

// SetHostInstances records aggregate inventory counts by bounded state.
func (r *Registry) SetHostInstances(running, sleeping, failed int) {
	for state, value := range map[string]int{
		"running": running, "sleeping": sleeping, "failed": failed,
	} {
		if value < 0 {
			value = 0
		}
		r.set("sshcloud_host_instances", "Host app instance inventory.", labels("state", state), float64(value))
	}
}

// RegisterCollector adds a bounded callback run immediately before exposition.
func (r *Registry) RegisterCollector(collector func()) {
	if collector == nil {
		return
	}
	r.mu.Lock()
	r.collect = append(r.collect, collector)
	r.mu.Unlock()
}

func (r *Registry) runCollectors() {
	r.mu.Lock()
	collectors := append([]func(){}, r.collect...)
	r.mu.Unlock()
	for _, collector := range collectors {
		collector()
	}
}

// Value returns one sample for tests and local diagnostics.
func (r *Registry) Value(name string, labelValues ...string) float64 {
	r.mu.Lock()
	defer r.mu.Unlock()
	return r.values[metricKey{name: name, labels: labels(labelValues...)}].value
}

// WritePrometheus emits the Prometheus text format accepted by both
// Prometheus and the Ops Agent's OpenTelemetry pipeline.
func (r *Registry) WritePrometheus(output io.Writer) error {
	r.runCollectors()
	r.mu.Lock()
	snapshot := make(map[metricKey]metricValue, len(r.values))
	for key, value := range r.values {
		snapshot[key] = value
	}
	r.mu.Unlock()

	keys := make([]metricKey, 0, len(snapshot))
	for key := range snapshot {
		keys = append(keys, key)
	}
	sort.Slice(keys, func(i, j int) bool {
		if keys[i].name != keys[j].name {
			return keys[i].name < keys[j].name
		}
		return keys[i].labels < keys[j].labels
	})
	described := make(map[string]bool)
	for _, key := range keys {
		value := snapshot[key]
		if !described[key.name] {
			if _, err := fmt.Fprintf(output, "# HELP %s %s\n# TYPE %s %s\n", key.name, value.help, key.name, value.kind); err != nil {
				return err
			}
			described[key.name] = true
		}
		name := key.name
		if key.labels != "" {
			name += "{" + key.labels + "}"
		}
		if _, err := fmt.Fprintf(output, "%s %s\n", name, strconv.FormatFloat(value.value, 'g', -1, 64)); err != nil {
			return err
		}
	}
	return nil
}

// Handler serves aggregate metrics only. It never accepts request parameters
// or exposes tenant/session metadata.
func (r *Registry) Handler() http.Handler {
	return http.HandlerFunc(func(w http.ResponseWriter, request *http.Request) {
		if request.Method != http.MethodGet {
			w.WriteHeader(http.StatusMethodNotAllowed)
			return
		}
		w.Header().Set("Content-Type", "text/plain; version=0.0.4; charset=utf-8")
		w.Header().Set("X-Content-Type-Options", "nosniff")
		_ = r.WritePrometheus(w)
	})
}

// MetricsHandler serves the process-wide registry.
func MetricsHandler() http.Handler { return defaultMetrics.Handler() }

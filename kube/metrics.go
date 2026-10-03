package kube

import (
	"fmt"
	"io"
	"maps"
	"slices"
	"strconv"
	"strings"
	"sync"
)

// metrics is a minimal Prometheus registry. Its methods are safe to call on
// a nil receiver.
type metrics struct {
	mu       sync.Mutex
	counters map[string]map[string]float64
	hists    map[string]map[string]*histogram
	gauges   []gaugeDef
}

type sample struct {
	labels []string
	value  float64
}

type gaugeDef struct {
	name, help string
	fn         func() []sample
}

type histogram struct {
	counts []uint64
	sum    float64
	count  uint64
}

var buckets = []float64{.001, .005, .01, .025, .05, .1, .25, .5, 1, 2.5, 5, 10}

var help = map[string]string{
	"kube_reconcile_total":            "Reconciles by controller and result.",
	"kube_reconcile_duration_seconds": "Time spent in reconcile, including writes.",
	"kube_apply_total":                "Server-side applies by result. Skipped applies matched the cache.",
	"kube_delete_total":               "Objects deleted by controllers.",
	"kube_status_writes_total":        "Status writes.",
	"kube_watch_events_total":         "Watch events received, by type.",
	"kube_watch_errors_total":         "Failed lists and watches, by type.",
	"kube_cache_relists_total":        "Relists after a watch's resource version expired.",
	"kube_webhook_requests_total":     "Admission and conversion webhook requests, by path and result.",
	"kube_webhook_duration_seconds":   "Time spent answering webhook requests, by path.",
	"kube_shard_transitions_total":    "Shards this replica acquired, released to another replica, or lost.",
}

func newMetrics() *metrics {
	return &metrics{counters: map[string]map[string]float64{}, hists: map[string]map[string]*histogram{}}
}

func labelString(labels []string) string {
	var b strings.Builder
	for i := 0; i+1 < len(labels); i += 2 {
		if i > 0 {
			b.WriteByte(',')
		}
		b.WriteString(labels[i])
		b.WriteString(`="`)
		b.WriteString(strings.NewReplacer(`\`, `\\`, `"`, `\"`, "\n", `\n`).Replace(labels[i+1]))
		b.WriteByte('"')
	}
	return b.String()
}

func (m *metrics) inc(name string, labels ...string) {
	if m == nil {
		return
	}
	ls := labelString(labels)
	m.mu.Lock()
	defer m.mu.Unlock()
	c := m.counters[name]
	if c == nil {
		c = map[string]float64{}
		m.counters[name] = c
	}
	c[ls]++
}

func (m *metrics) observe(name string, v float64, labels ...string) {
	if m == nil {
		return
	}
	ls := labelString(labels)
	m.mu.Lock()
	defer m.mu.Unlock()
	hs := m.hists[name]
	if hs == nil {
		hs = map[string]*histogram{}
		m.hists[name] = hs
	}
	h := hs[ls]
	if h == nil {
		h = &histogram{counts: make([]uint64, len(buckets))}
		hs[ls] = h
	}
	for i, b := range buckets {
		if v <= b {
			h.counts[i]++
		}
	}
	h.sum += v
	h.count++
}

func (m *metrics) gauge(name, help string, fn func() []sample) {
	if m == nil {
		return
	}
	m.mu.Lock()
	defer m.mu.Unlock()
	m.gauges = append(m.gauges, gaugeDef{name, help, fn})
}

// counter returns a counter's value, for tests.
func (m *metrics) counter(name string, labels ...string) float64 {
	m.mu.Lock()
	defer m.mu.Unlock()
	return m.counters[name][labelString(labels)]
}

// series names one series of a metric in the text format.
func series(name, labels string) string {
	if labels == "" {
		return name
	}
	return name + "{" + labels + "}"
}

func (m *metrics) write(w io.Writer) {
	m.mu.Lock()
	for _, name := range slices.Sorted(maps.Keys(m.counters)) {
		fmt.Fprintf(w, "# HELP %s %s\n# TYPE %s counter\n", name, help[name], name)
		for _, ls := range slices.Sorted(maps.Keys(m.counters[name])) {
			fmt.Fprintf(w, "%s %s\n", series(name, ls), strconv.FormatFloat(m.counters[name][ls], 'g', -1, 64))
		}
	}
	for _, name := range slices.Sorted(maps.Keys(m.hists)) {
		fmt.Fprintf(w, "# HELP %s %s\n# TYPE %s histogram\n", name, help[name], name)
		for _, ls := range slices.Sorted(maps.Keys(m.hists[name])) {
			h := m.hists[name][ls]
			sep := ""
			if ls != "" {
				sep = ","
			}
			for i, b := range buckets {
				fmt.Fprintf(w, "%s_bucket{%s%sle=\"%s\"} %d\n", name, ls, sep, strconv.FormatFloat(b, 'g', -1, 64), h.counts[i])
			}
			fmt.Fprintf(w, "%s_bucket{%s%sle=\"+Inf\"} %d\n", name, ls, sep, h.count)
			fmt.Fprintf(w, "%s %s\n%s %d\n", series(name+"_sum", ls), strconv.FormatFloat(h.sum, 'g', -1, 64), series(name+"_count", ls), h.count)
		}
	}
	gauges := slices.Clone(m.gauges)
	m.mu.Unlock()
	// Gauge functions take other locks, so they run without m.mu, which
	// code holding those locks may also take.
	byName := map[string][]gaugeDef{}
	for _, g := range gauges {
		byName[g.name] = append(byName[g.name], g)
	}
	for _, name := range slices.Sorted(maps.Keys(byName)) {
		fmt.Fprintf(w, "# HELP %s %s\n# TYPE %s gauge\n", name, byName[name][0].help, name)
		for _, g := range byName[name] {
			for _, s := range g.fn() {
				fmt.Fprintf(w, "%s %s\n", series(name, labelString(s.labels)), strconv.FormatFloat(s.value, 'g', -1, 64))
			}
		}
	}
}

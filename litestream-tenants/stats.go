//go:build vfs

package main

import (
	"fmt"
	"sort"
	"strings"
	"sync"
	"sync/atomic"
	"time"
)

// Stats collects latency samples and error counters for a bench run.
type Stats struct {
	mu       sync.Mutex
	samples  []time.Duration
	ok       atomic.Int64
	err      atomic.Int64
	conflict atomic.Int64
	busy     atomic.Int64
}

func (s *Stats) Record(d time.Duration, err error) {
	if err != nil {
		// Deadline/cancel from the bench harness is not a DB failure.
		if strings.Contains(err.Error(), "context deadline exceeded") ||
			strings.Contains(err.Error(), "context canceled") {
			return
		}
		s.err.Add(1)
		msg := strings.ToLower(err.Error())
		if strings.Contains(msg, "conflict") ||
			strings.Contains(msg, "newer transactions") ||
			strings.Contains(msg, "expected txid") {
			s.conflict.Add(1)
		}
		if strings.Contains(msg, "busy") || strings.Contains(msg, "locked") {
			s.busy.Add(1)
		}
		return
	}
	s.ok.Add(1)
	s.mu.Lock()
	s.samples = append(s.samples, d)
	s.mu.Unlock()
}

func (s *Stats) Snapshot() Report {
	s.mu.Lock()
	samples := append([]time.Duration(nil), s.samples...)
	s.mu.Unlock()
	sort.Slice(samples, func(i, j int) bool { return samples[i] < samples[j] })

	r := Report{
		OK:       s.ok.Load(),
		Errors:   s.err.Load(),
		Conflict: s.conflict.Load(),
		Busy:     s.busy.Load(),
		N:        int64(len(samples)),
	}
	if len(samples) == 0 {
		return r
	}
	var sum time.Duration
	for _, d := range samples {
		sum += d
	}
	r.Avg = sum / time.Duration(len(samples))
	r.Min = samples[0]
	r.Max = samples[len(samples)-1]
	r.P50 = percentile(samples, 50)
	r.P95 = percentile(samples, 95)
	r.P99 = percentile(samples, 99)
	return r
}

// Report is a printable summary of a Stats snapshot.
type Report struct {
	OK, Errors, Conflict, Busy, N int64
	Min, Avg, P50, P95, P99, Max  time.Duration
	Duration                      time.Duration
	Label                         string
}

func (r Report) RPS() float64 {
	if r.Duration <= 0 {
		return 0
	}
	return float64(r.OK) / r.Duration.Seconds()
}

func (r Report) String() string {
	label := r.Label
	if label == "" {
		label = "bench"
	}
	return fmt.Sprintf(
		"%s: ok=%d err=%d conflict=%d busy=%d rps=%.0f lat(min/p50/p95/p99/max)=%s/%s/%s/%s/%s",
		label, r.OK, r.Errors, r.Conflict, r.Busy, r.RPS(),
		r.Min.Round(time.Microsecond),
		r.P50.Round(time.Microsecond),
		r.P95.Round(time.Microsecond),
		r.P99.Round(time.Microsecond),
		r.Max.Round(time.Microsecond),
	)
}

func percentile(sorted []time.Duration, p int) time.Duration {
	if len(sorted) == 0 {
		return 0
	}
	if p <= 0 {
		return sorted[0]
	}
	if p >= 100 {
		return sorted[len(sorted)-1]
	}
	idx := (p * len(sorted)) / 100
	if idx >= len(sorted) {
		idx = len(sorted) - 1
	}
	return sorted[idx]
}

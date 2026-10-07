package main

import (
	"strings"
	"testing"
)

func TestComparison(t *testing.T) {
	digest := strings.Repeat("0123456789abcdef", 4)
	before := &summary{
		Repos: 1, N: 20, Landed: 20, Poll: "2s", Gotest: true, Drain: 149.24, PerMin: 8.1,
		Errors: errorSummary{ErrorResults: []string{"a", "b"}, ReconcileErrors: map[string]float64{"check-base/check-base": 14, "git-k8s/merge": 1}},
		Waits:  waitSummary{Waits: make([]resultWait, 6), StalledCycles: 2, StalledSeconds: 9.54},
		CPU:    cpuSummary{HostAvg: 3.04},
	}
	after := &summary{
		Repos: 1, N: 20, Landed: 20, Poll: "2s", Gotest: true, Drain: 139.7,
		Images: map[string]string{"git-k8s/git-k8s": "registry:5000/gk-stress/git-k8s@sha256:" + digest},
		Waits:  waitSummary{Gone: make([]goneAnswer, 7)},
	}
	got := comparison([]string{"runs/before", "runs/after"}, map[string]*summary{"runs/before": before, "runs/after": after})
	for _, want := range []string{
		"| before | 1 × 20 | 2s | true | 149.2 | 8.1 |",
		"| after | 1 × 20 | 2s | true | 139.7 | 0.0 |",
		"| before | unknown | 2 | 15 | 6 | 0 | 2 (9.5 s) | 3.0 |",
		"| after | `0123456789ab` | 0 | 0 | 0 | 7 | 0 (0.0 s) | 0.0 |",
	} {
		if !strings.Contains(got, want) {
			t.Errorf("the comparison doesn't have %q:\n%s", want, got)
		}
	}
	if n := strings.Count(got, "| Run |"); n != 2 {
		t.Errorf("%d tables, want 2:\n%s", n, got)
	}
}

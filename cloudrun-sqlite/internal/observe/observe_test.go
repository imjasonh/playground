package observe

import (
	"log/slog"
	"net/http/httptest"
	"strings"
	"testing"
	"time"

	"github.com/chainguard-dev/clog"
)

func TestMetricsServesHistograms(t *testing.T) {
	stop := Start(clog.WithLogger(t.Context(), clog.New(slog.DiscardHandler)))
	defer stop(t.Context())

	Measure(t.Context(), VFSPageRead, 30*time.Microsecond, "source", "paged_in")
	Measure(t.Context(), VFSPageRead, 40*time.Millisecond, "source", "cold")
	Measure(t.Context(), StoreWrite, 60*time.Millisecond, "durable", "true", "result", "ok")

	rec := httptest.NewRecorder()
	Metrics().ServeHTTP(rec, httptest.NewRequest("GET", "/metrics", nil))
	body := rec.Body.String()
	for _, want := range []string{
		`# HELP vfs_page_read_seconds Time for one SQLite page read`,
		`vfs_page_read_seconds_bucket{source="paged_in",le="2.5e-05"} 0`,
		`vfs_page_read_seconds_bucket{source="paged_in",le="5e-05"} 1`,
		`vfs_page_read_seconds_bucket{source="cold",le="0.05"} 1`,
		`store_write_seconds_count{durable="true",result="ok"} 1`,
	} {
		if !strings.Contains(body, want) {
			t.Errorf("/metrics is missing %q", want)
		}
	}
	if t.Failed() {
		t.Log(body)
	}
}

func TestParseCloudTrace(t *testing.T) {
	traceID, spanID, sampled, ok := parseCloudTrace("0123456789abcdef0123456789abcdef/17;o=1")
	if !ok || !sampled {
		t.Fatalf("parsed ok=%v sampled=%v", ok, sampled)
	}
	if traceID.String() != "0123456789abcdef0123456789abcdef" {
		t.Fatalf("trace = %s", traceID)
	}
	if spanID.String() != "0000000000000011" {
		t.Fatalf("span = %s", spanID)
	}
	if _, _, _, ok := parseCloudTrace("not-a-header"); ok {
		t.Fatal("accepted a bad header")
	}
}

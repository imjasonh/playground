package main

import (
	"database/sql"
	"encoding/json"
	"log/slog"
	"net/http/httptest"
	"os"
	"regexp"
	"strings"
	"testing"

	"github.com/chainguard-dev/clog"
	"github.com/imjasonh/playground/cloudrun-sqlite/internal/observe"
	"github.com/imjasonh/playground/cloudrun-sqlite/internal/store"
)

var (
	metricTypeRE = regexp.MustCompile(`metric\.type="workload\.googleapis\.com/([^"]+)"`)
	labelEqRE    = regexp.MustCompile(`metric\.label\.(\w+)="([^"]*)"`)
	labelOneOfRE = regexp.MustCompile(`metric\.label\.(\w+)=one_of\(([^)]*)\)`)
)

// TestDashboardMatchesMetrics checks that each chart in
// terraform/dashboard.json selects series the server emits. It runs durable
// writes, then cold and paged-in reads from a second instance, and looks
// for every metric and label value the charts filter or group by in
// /metrics, which reads the same histograms that go to Cloud Monitoring.
func TestDashboardMatchesMetrics(t *testing.T) {
	stop := observe.Start(clog.WithLogger(t.Context(), clog.New(slog.DiscardHandler)))
	defer stop(t.Context())

	replica := t.TempDir()
	open := func() *store.Store {
		cfg := store.DefaultConfig()
		cfg.ReplicaURL = "file://" + replica
		cfg.Dir = t.TempDir()
		s, err := store.Open(clog.WithLogger(t.Context(), clog.New(slog.DiscardHandler)), cfg)
		if err != nil {
			t.Fatal(err)
		}
		return s
	}
	write := func(s *store.Store, query string) {
		t.Helper()
		if err := s.Write(t.Context(), func(tx *sql.Tx) error {
			_, err := tx.Exec(query)
			return err
		}); err != nil {
			t.Fatal(err)
		}
	}
	s := open()
	write(s, "CREATE TABLE t (id INTEGER PRIMARY KEY, v BLOB)")
	for range 10 {
		write(s, "INSERT INTO t (v) VALUES (randomblob(3000))")
	}
	if err := s.Close(); err != nil {
		t.Fatal(err)
	}
	s = open()
	defer s.Close()
	for range 2 {
		if err := s.Read(t.Context(), func(db *sql.DB) error {
			var n int
			return db.QueryRow("SELECT count(*) FROM t").Scan(&n)
		}); err != nil {
			t.Fatal(err)
		}
	}

	rec := httptest.NewRecorder()
	observe.Metrics().ServeHTTP(rec, httptest.NewRequest("GET", "/metrics", nil))
	var counts []string
	for _, line := range strings.Split(rec.Body.String(), "\n") {
		if strings.Contains(line, "_seconds_count{") && !strings.HasSuffix(line, " 0") {
			counts = append(counts, line)
		}
	}

	b, err := os.ReadFile("terraform/dashboard.json")
	if err != nil {
		t.Fatal(err)
	}
	var dashboard struct {
		MosaicLayout struct {
			Tiles []struct {
				Widget struct {
					Title   string `json:"title"`
					XYChart struct {
						DataSets []struct {
							TimeSeriesQuery struct {
								TimeSeriesFilter struct {
									Filter      string `json:"filter"`
									Aggregation struct {
										GroupByFields []string `json:"groupByFields"`
									} `json:"aggregation"`
								} `json:"timeSeriesFilter"`
							} `json:"timeSeriesQuery"`
						} `json:"dataSets"`
					} `json:"xyChart"`
				} `json:"widget"`
			} `json:"tiles"`
		} `json:"mosaicLayout"`
	}
	if err := json.Unmarshal(b, &dashboard); err != nil {
		t.Fatal(err)
	}
	if len(dashboard.MosaicLayout.Tiles) == 0 {
		t.Fatal("dashboard has no charts")
	}
	for _, tile := range dashboard.MosaicLayout.Tiles {
		for _, ds := range tile.Widget.XYChart.DataSets {
			q := ds.TimeSeriesQuery.TimeSeriesFilter
			m := metricTypeRE.FindStringSubmatch(q.Filter)
			if m == nil {
				t.Errorf("%q: filter %q has no workload metric type", tile.Widget.Title, q.Filter)
				continue
			}
			name := strings.ReplaceAll(m[1], ".", "_") + "_seconds_count{"
			var want []string
			for _, eq := range labelEqRE.FindAllStringSubmatch(q.Filter, -1) {
				want = append(want, eq[1]+`="`+eq[2]+`"`)
			}
			alternatives := [][]string{nil}
			for _, oneOf := range labelOneOfRE.FindAllStringSubmatch(q.Filter, -1) {
				alternatives = nil
				for _, v := range strings.Split(oneOf[2], ",") {
					alternatives = append(alternatives, []string{oneOf[1] + `=` + strings.TrimSpace(v)})
				}
			}
			for _, g := range q.Aggregation.GroupByFields {
				want = append(want, strings.TrimPrefix(g, "metric.label.")+`="`)
			}
			for _, alt := range alternatives {
				labels := append(append([]string{}, want...), alt...)
				if !hasSeries(counts, name, labels) {
					t.Errorf("%q: no recorded %s series with %v", tile.Widget.Title, strings.TrimSuffix(name, "{"), labels)
				}
			}
		}
	}
	// The page read chart groups by source, so check both sources exist.
	for _, source := range []string{"paged_in", "cold"} {
		if !hasSeries(counts, "vfs_page_read_seconds_count{", []string{`source="` + source + `"`}) {
			t.Errorf("no recorded %s page reads", source)
		}
	}
	if t.Failed() {
		t.Logf("recorded series:\n%s", strings.Join(counts, "\n"))
	}
}

func hasSeries(counts []string, name string, labels []string) bool {
	for _, line := range counts {
		if !strings.HasPrefix(line, name) {
			continue
		}
		found := true
		for _, l := range labels {
			if !strings.Contains(line, l) {
				found = false
				break
			}
		}
		if found {
			return true
		}
	}
	return false
}

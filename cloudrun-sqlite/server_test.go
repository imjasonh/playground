package main

import (
	"log/slog"
	"net/http"
	"net/http/httptest"
	"regexp"
	"strings"
	"testing"
	"time"

	"github.com/chainguard-dev/clog"
	"github.com/imjasonh/playground/cloudrun-sqlite/internal/store"
)

func TestWriteTook(t *testing.T) {
	cases := []struct {
		d    time.Duration
		want string
	}{
		{0, "under 1 ms"},
		{400 * time.Microsecond, "under 1 ms"},
		{600 * time.Microsecond, "1 ms"},
		{842 * time.Millisecond, "842 ms"},
		{1500 * time.Millisecond, "1.5 s"},
	}
	for _, tc := range cases {
		if got := writeTook(tc.d); got != tc.want {
			t.Errorf("writeTook(%s) = %q, want %q", tc.d, got, tc.want)
		}
	}
}

func TestClickDisablesUntilWriteReturns(t *testing.T) {
	ctx := clog.WithLogger(t.Context(), clog.New(slog.DiscardHandler))
	cfg := store.DefaultConfig()
	cfg.ReplicaURL = "file://" + t.TempDir()
	cfg.Dir = t.TempDir()
	cfg.SnapshotPlanLen = 0
	st, err := store.Open(ctx, cfg)
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { st.Close() })
	if err := migrate(ctx, st); err != nil {
		t.Fatal(err)
	}

	h := newServer(st, "test", time.Now(), "").routes()
	index := httptest.NewRecorder()
	h.ServeHTTP(index, httptest.NewRequest(http.MethodGet, "/", nil))
	if index.Code != http.StatusOK {
		t.Fatalf("GET /: %d %s", index.Code, index.Body)
	}
	page := index.Body.String()
	if !strings.Contains(page, `hx-disabled-elt="this"`) {
		t.Fatalf("click button is not disabled during the request:\n%s", page)
	}
	if strings.Contains(page, " ms<") || strings.Contains(page, " s<") {
		t.Fatalf("index shows a write duration before any click:\n%s", page)
	}

	click := httptest.NewRecorder()
	h.ServeHTTP(click, httptest.NewRequest(http.MethodPost, "/click", nil))
	if click.Code != http.StatusOK {
		t.Fatalf("POST /click: %d %s", click.Code, click.Body)
	}
	body := click.Body.String()
	if !strings.Contains(body, "Clicks: 1") {
		t.Fatalf("click count: %s", body)
	}
	if !strings.Contains(body, `hx-disabled-elt="this"`) {
		t.Fatalf("replaced button is not disabled during the next request:\n%s", body)
	}
	if strings.Contains(body, " disabled") || strings.Contains(body, "disabled=") {
		t.Fatalf("replaced button stays disabled:\n%s", body)
	}
	took := regexp.MustCompile(`<small>(?:under 1 ms|\d+ ms|\d+\.\d s)</small>`)
	if !took.MatchString(body) {
		t.Fatalf("write duration missing beside the button:\n%s", body)
	}
}

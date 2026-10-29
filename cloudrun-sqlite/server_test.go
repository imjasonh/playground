package main

import (
	"bufio"
	"context"
	"io"
	"log/slog"
	"net/http"
	"net/http/httptest"
	"regexp"
	"strings"
	"testing"
	"time"

	"github.com/chainguard-dev/clog"
	"github.com/imjasonh/playground/cloudrun-sqlite/internal/fanout"
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
	h := testServer(t)
	index := httptest.NewRecorder()
	h.ServeHTTP(index, httptest.NewRequest(http.MethodGet, "/", nil))
	if index.Code != http.StatusOK {
		t.Fatalf("GET /: %d %s", index.Code, index.Body)
	}
	page := index.Body.String()
	if !strings.Contains(page, `hx-disabled-elt="this"`) {
		t.Fatalf("click button is not disabled during the request:\n%s", page)
	}
	if !strings.Contains(page, `sse-connect="/events"`) {
		t.Fatalf("page has no event connection:\n%s", page)
	}
	if strings.Contains(page, " ms<") || strings.Contains(page, " s<") {
		t.Fatalf("index shows a write duration before any click:\n%s", page)
	}
	script := httptest.NewRecorder()
	h.ServeHTTP(script, httptest.NewRequest(http.MethodGet, "/htmx.js", nil))
	if script.Code != http.StatusOK || !strings.Contains(script.Body.String(), "htmx") {
		t.Fatalf("GET /htmx.js: %d %s", script.Code, script.Body)
	}

	click := httptest.NewRecorder()
	h.ServeHTTP(click, httptest.NewRequest(http.MethodPost, "/click", nil))
	if click.Code != http.StatusOK {
		t.Fatalf("POST /click: %d %s", click.Code, click.Body)
	}
	body := click.Body.String()
	if strings.Contains(body, "Clicks:") {
		t.Fatalf("click response updates the count for this page only:\n%s", body)
	}
	if !strings.Contains(body, `hx-disabled-elt="this"`) {
		t.Fatalf("replaced button is not disabled during the next request:\n%s", body)
	}
	if strings.Contains(body, " disabled") || strings.Contains(body, "disabled=") {
		t.Fatalf("replaced button stays disabled:\n%s", body)
	}
	took := regexp.MustCompile(`<span class="status">(?:under 1 ms|\d+ ms|\d+\.\d s)</span>`)
	if !took.MatchString(body) {
		t.Fatalf("write duration missing beside the button:\n%s", body)
	}

	after := httptest.NewRecorder()
	h.ServeHTTP(after, httptest.NewRequest(http.MethodGet, "/", nil))
	if after.Code != http.StatusOK || !strings.Contains(after.Body.String(), "Clicks: 1") {
		t.Fatalf("count after click: %d %s", after.Code, after.Body)
	}
}

func TestClickReachesEveryEventConnection(t *testing.T) {
	srv := httptest.NewServer(testServer(t))
	t.Cleanup(srv.Close)
	ctx, cancel := context.WithTimeout(t.Context(), 15*time.Second)
	defer cancel()

	a := openEvents(ctx, t, srv.URL+"/events")
	b := openEvents(ctx, t, srv.URL+"/events")
	defer a.Close()
	defer b.Close()
	waitEvent(t, a, "clicks", "Clicks: 0")
	waitEvent(t, b, "clicks", "Clicks: 0")

	for _, want := range []string{"Clicks: 1", "Clicks: 2"} {
		res, err := http.Post(srv.URL+"/click", "text/plain", nil)
		if err != nil {
			t.Fatal(err)
		}
		res.Body.Close()
		if res.StatusCode != http.StatusOK {
			t.Fatalf("POST /click: %s", res.Status)
		}
		waitEvent(t, a, "clicks", want)
		waitEvent(t, b, "clicks", want)
		waitEvent(t, a, "notice", "count "+want[len("Clicks: "):])
		waitEvent(t, b, "notice", "count "+want[len("Clicks: "):])
	}
}

func TestReadOnlyReplicaFollowsWriter(t *testing.T) {
	replica := t.TempDir()
	writer := httptest.NewServer(testServerAt(t, replica, false))
	t.Cleanup(writer.Close)
	reader := httptest.NewServer(testServerAt(t, replica, true))
	t.Cleanup(reader.Close)

	res, err := http.Get(reader.URL + "/")
	if err != nil {
		t.Fatal(err)
	}
	page, _ := io.ReadAll(res.Body)
	res.Body.Close()
	if res.StatusCode != http.StatusOK {
		t.Fatalf("GET / on the replica: %s %s", res.Status, page)
	}
	if strings.Contains(string(page), `hx-post="/click"`) {
		t.Fatalf("replica page has a click button:\n%s", page)
	}
	if !strings.Contains(string(page), "read-only replica") {
		t.Fatalf("replica page doesn't say it's read-only:\n%s", page)
	}

	for _, path := range []string{"/click", "/items", "/admin/snapshot"} {
		res, err := http.Post(reader.URL+path, "text/plain", strings.NewReader("x"))
		if err != nil {
			t.Fatal(err)
		}
		res.Body.Close()
		if res.StatusCode != http.StatusMethodNotAllowed {
			t.Errorf("POST %s on the replica: %s, want 405", path, res.Status)
		}
	}

	ctx, cancel := context.WithTimeout(t.Context(), 15*time.Second)
	defer cancel()
	events := openEvents(ctx, t, reader.URL+"/events")
	defer events.Close()
	waitEvent(t, events, "clicks", "Clicks: 0")
	res, err = http.Post(writer.URL+"/click", "text/plain", nil)
	if err != nil {
		t.Fatal(err)
	}
	res.Body.Close()
	if res.StatusCode != http.StatusOK {
		t.Fatalf("POST /click on the writer: %s", res.Status)
	}
	waitEvent(t, events, "clicks", "Clicks: 1")
	waitEvent(t, events, "notice", "count 1")
}

type eventStream struct {
	body io.ReadCloser
	r    *bufio.Reader
}

func openEvents(ctx context.Context, t *testing.T, url string) *eventStream {
	t.Helper()
	req, err := http.NewRequestWithContext(ctx, http.MethodGet, url, nil)
	if err != nil {
		t.Fatal(err)
	}
	res, err := http.DefaultClient.Do(req)
	if err != nil {
		t.Fatal(err)
	}
	if res.StatusCode != http.StatusOK {
		body, _ := io.ReadAll(res.Body)
		res.Body.Close()
		t.Fatalf("GET /events: %d %s", res.StatusCode, body)
	}
	if ct := res.Header.Get("Content-Type"); !strings.HasPrefix(ct, "text/event-stream") {
		res.Body.Close()
		t.Fatalf("Content-Type %q", ct)
	}
	return &eventStream{body: res.Body, r: bufio.NewReader(res.Body)}
}

func (e *eventStream) Close() { e.body.Close() }

func waitEvent(t *testing.T, e *eventStream, name, contains string) {
	t.Helper()
	for {
		gotName, data, err := readEvent(e.r)
		if err != nil {
			t.Fatalf("read event: %v", err)
		}
		if gotName == name && strings.Contains(data, contains) {
			return
		}
	}
}

func readEvent(r *bufio.Reader) (name, data string, err error) {
	for {
		line, err := r.ReadString('\n')
		if err != nil {
			return "", "", err
		}
		line = strings.TrimRight(line, "\r\n")
		if line == "" {
			return name, data, nil
		}
		if strings.HasPrefix(line, ":") {
			continue
		}
		if strings.HasPrefix(line, "event:") {
			name = strings.TrimSpace(strings.TrimPrefix(line, "event:"))
		}
		if strings.HasPrefix(line, "data:") {
			data = strings.TrimSpace(strings.TrimPrefix(line, "data:"))
		}
	}
}

func testServer(t *testing.T) http.Handler {
	t.Helper()
	return testServerAt(t, t.TempDir(), false)
}

// testServerAt serves the replica in dir. A read-only server must start
// after a writer, because opening waits until the database exists.
func testServerAt(t *testing.T, dir string, readOnly bool) http.Handler {
	t.Helper()
	ctx, cancel := context.WithCancel(clog.WithLogger(t.Context(), clog.New(slog.DiscardHandler)))
	cfg := store.DefaultConfig()
	cfg.ReplicaURL = "file://" + dir
	cfg.Dir = t.TempDir()
	cfg.SnapshotPlanLen = 0
	cfg.ReadOnly = readOnly
	if readOnly {
		cfg.PollInterval = 50 * time.Millisecond
	}
	st, err := store.Open(ctx, cfg)
	if err != nil {
		cancel()
		t.Fatal(err)
	}
	if !readOnly {
		if err := migrate(ctx, st); err != nil {
			cancel()
			st.Close()
			t.Fatal(err)
		}
	}
	live := fanout.New()
	s := newServer(st, live, "test", time.Now(), "")
	s.readOnly, s.pollInterval = readOnly, cfg.PollInterval
	if readOnly {
		go s.followReplica(ctx)
	}
	t.Cleanup(func() {
		cancel()
		live.Close()
		st.Close()
	})
	return s.routes()
}

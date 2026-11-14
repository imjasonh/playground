package whbiab

import (
	"context"
	"flag"
	"io"
	"net/http"
	"net/http/httptest"
	"net/url"
	"slices"
	"strings"
	"sync"
	"testing"
	"time"
)

type recorder struct {
	mu   sync.Mutex
	reqs []*http.Request
}

func (r *recorder) ServeHTTP(w http.ResponseWriter, req *http.Request) {
	r.mu.Lock()
	r.reqs = append(r.reqs, req)
	r.mu.Unlock()
	w.WriteHeader(http.StatusForbidden)
}

func (r *recorder) requests() []*http.Request {
	r.mu.Lock()
	defer r.mu.Unlock()
	return slices.Clone(r.reqs)
}

func newServer(t *testing.T) *recorder {
	t.Helper()
	rec := &recorder{}
	srv := httptest.NewServer(rec)
	t.Cleanup(srv.Close)
	t.Setenv("WHBIAB_ENDPOINT", srv.URL+"/wehadababyitsaboy")
	t.Setenv("DO_NOT_TRACK", "")
	t.Setenv("WHBIAB_DISABLE", "")
	t.Setenv("CI", "")
	return rec
}

func TestTrackSendsPing(t *testing.T) {
	rec := newServer(t)

	wait := Track(t.Context(), "My CLI", "Query", "format", "max_width", "a/b")
	wait()

	reqs := rec.requests()
	if len(reqs) != 1 {
		t.Fatalf("got %d requests, want 1", len(reqs))
	}
	req := reqs[0]
	if want := "/wehadababyitsaboy/my-cli/query.format.max_width.a-b"; req.URL.Path != want {
		t.Errorf("path = %q, want %q", req.URL.Path, want)
	}
	if !strings.HasPrefix(req.URL.RawQuery, "bob=wehadababyitsaboy&") {
		t.Errorf("query = %q, want it to start with bob=wehadababyitsaboy&", req.URL.RawQuery)
	}
	q := req.URL.Query()
	for _, key := range []string{"v", "os", "arch"} {
		if q.Get(key) == "" {
			t.Errorf("query is missing %q: %s", key, req.URL.RawQuery)
		}
	}
	if q.Has("ci") {
		t.Errorf("query has ci with CI unset: %s", req.URL.RawQuery)
	}
	if got := req.UserAgent(); !strings.HasPrefix(got, "my-cli/") || !strings.HasSuffix(got, " (whbiab)") {
		t.Errorf("user agent = %q", got)
	}
}

func TestTrackWithoutParts(t *testing.T) {
	rec := newServer(t)

	Track(t.Context(), "tool")()

	reqs := rec.requests()
	if len(reqs) != 1 {
		t.Fatalf("got %d requests, want 1", len(reqs))
	}
	if want := "/wehadababyitsaboy/tool/run"; reqs[0].URL.Path != want {
		t.Errorf("path = %q, want %q", reqs[0].URL.Path, want)
	}
}

func TestTrackMarksCI(t *testing.T) {
	rec := newServer(t)
	t.Setenv("CI", "true")

	Track(t.Context(), "tool")()

	reqs := rec.requests()
	if len(reqs) != 1 {
		t.Fatalf("got %d requests, want 1", len(reqs))
	}
	if got := reqs[0].URL.Query().Get("ci"); got != "1" {
		t.Errorf("ci = %q, want 1", got)
	}
}

func TestTrackOptOut(t *testing.T) {
	for _, tc := range []struct {
		name, key, value string
		want             int
	}{
		{"DO_NOT_TRACK on", "DO_NOT_TRACK", "1", 0},
		{"DO_NOT_TRACK any value", "DO_NOT_TRACK", "yes", 0},
		{"DO_NOT_TRACK zero", "DO_NOT_TRACK", "0", 1},
		{"WHBIAB_DISABLE on", "WHBIAB_DISABLE", "1", 0},
		{"WHBIAB_DISABLE zero", "WHBIAB_DISABLE", "0", 1},
	} {
		t.Run(tc.name, func(t *testing.T) {
			rec := newServer(t)
			t.Setenv(tc.key, tc.value)

			Track(t.Context(), "tool", "query")()

			if got := len(rec.requests()); got != tc.want {
				t.Errorf("got %d requests, want %d", got, tc.want)
			}
		})
	}
}

func TestTrackSkipsEmptyClient(t *testing.T) {
	rec := newServer(t)

	Track(t.Context(), " // ", "query")()

	if got := len(rec.requests()); got != 0 {
		t.Errorf("got %d requests, want 0", got)
	}
}

func TestTrackUnreachable(t *testing.T) {
	srv := httptest.NewServer(http.NotFoundHandler())
	url := srv.URL
	srv.Close()
	t.Setenv("WHBIAB_ENDPOINT", url)
	t.Setenv("DO_NOT_TRACK", "")
	t.Setenv("WHBIAB_DISABLE", "")

	Track(t.Context(), "tool")()
}

func TestTrackTimesOut(t *testing.T) {
	release := make(chan struct{})
	srv := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		<-release
	}))
	t.Cleanup(srv.Close)
	t.Cleanup(func() { close(release) })
	t.Setenv("WHBIAB_ENDPOINT", srv.URL)
	t.Setenv("DO_NOT_TRACK", "")
	t.Setenv("WHBIAB_DISABLE", "")

	old := requestTimeout
	requestTimeout = 50 * time.Millisecond
	t.Cleanup(func() { requestTimeout = old })

	start := time.Now()
	Track(t.Context(), "tool")()
	if elapsed := time.Since(start); elapsed > 2*time.Second {
		t.Errorf("wait took %v, want it bounded by the timeout", elapsed)
	}
}

func TestTrackStopsWhenContextEnds(t *testing.T) {
	rec := newServer(t)
	ctx, cancel := context.WithCancel(t.Context())
	cancel()

	Track(ctx, "tool")()

	if got := len(rec.requests()); got != 0 {
		t.Errorf("got %d requests with a canceled context, want 0", got)
	}
}

func TestFlags(t *testing.T) {
	fs := flag.NewFlagSet("tool", flag.ContinueOnError)
	fs.SetOutput(io.Discard)
	fs.String("query", "", "")
	fs.Bool("offline", false, "")
	fs.Int("width", 60, "")
	if err := fs.Parse([]string{"-width=80", "-query", "SELECT secret", "-offline", "positional"}); err != nil {
		t.Fatal(err)
	}

	got := Flags(fs)

	if want := []string{"offline", "query", "width"}; !slices.Equal(got, want) {
		t.Errorf("Flags = %v, want %v", got, want)
	}
}

func TestFlagsUnset(t *testing.T) {
	fs := flag.NewFlagSet("tool", flag.ContinueOnError)
	fs.String("query", "", "")
	if err := fs.Parse(nil); err != nil {
		t.Fatal(err)
	}

	if got := Flags(fs); len(got) != 0 {
		t.Errorf("Flags = %v, want none", got)
	}
}

func TestClean(t *testing.T) {
	for _, tc := range []struct{ in, want string }{
		{"query", "query"},
		{"Query", "query"},
		{"max_width", "max_width"},
		{"no-renames", "no-renames"},
		{"a b", "a-b"},
		{"a/b", "a-b"},
		{"a.b", "a-b"},
		{"../etc/passwd", "etc-passwd"},
		{"SELECT * FROM t", "select---from-t"},
		{"héllo", "h-llo"},
		{"--", ""},
		{"", ""},
		{strings.Repeat("a", 100), strings.Repeat("a", maxPartLen)},
	} {
		if got := clean(tc.in); got != tc.want {
			t.Errorf("clean(%q) = %q, want %q", tc.in, got, tc.want)
		}
	}
}

func TestPingURLBoundsParts(t *testing.T) {
	var parts []string
	for range 40 {
		parts = append(parts, "flag")
	}

	target, ok := pingURL(config{Endpoint: "https://example.test/b/"}, "tool", parts)
	if !ok {
		t.Fatal("pingURL returned !ok")
	}
	u, err := url.Parse(target)
	if err != nil {
		t.Fatal(err)
	}
	if got := strings.Count(u.Path, "flag"); got != maxParts {
		t.Errorf("path has %d parts, want %d: %s", got, maxParts, u.Path)
	}
	if !strings.HasPrefix(u.Path, "/b/tool/") {
		t.Errorf("path = %q, want it under /b/tool/", u.Path)
	}
}

type countingTransport struct{ calls int }

func (c *countingTransport) RoundTrip(*http.Request) (*http.Response, error) {
	c.calls++
	return nil, io.ErrUnexpectedEOF
}

func TestTrackSkipsInTestBinaryWithoutEndpoint(t *testing.T) {
	t.Setenv("WHBIAB_ENDPOINT", "")
	t.Setenv("DO_NOT_TRACK", "")
	t.Setenv("WHBIAB_DISABLE", "")
	transport := &countingTransport{}
	old := http.DefaultTransport
	http.DefaultTransport = transport
	t.Cleanup(func() { http.DefaultTransport = old })

	Track(t.Context(), "tool")()

	if transport.calls != 0 {
		t.Errorf("sent %d requests to the default endpoint from a test binary, want 0", transport.calls)
	}
}

func TestPingURLDefaultEndpoint(t *testing.T) {
	target, ok := pingURL(config{}, "tool", []string{"query"})
	if !ok {
		t.Fatal("pingURL returned !ok")
	}
	if want := defaultEndpoint + "/tool/query?bob=wehadababyitsaboy&"; !strings.HasPrefix(target, want) {
		t.Errorf("target = %q, want prefix %q", target, want)
	}
}

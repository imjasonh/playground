package whbiab

import (
	"context"
	"errors"
	"io"
	"net/http"
	"net/http/httptest"
	"net/url"
	"slices"
	"strings"
	"sync"
	"testing"
	"time"

	"github.com/spf13/cobra"
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

	wait := track(t.Context(), "My CLI", "Query", "format", "max_width", "a/b")
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

	track(t.Context(), "tool")()

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

	track(t.Context(), "tool")()

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
		{"DO_NOT_TRACK false", "DO_NOT_TRACK", "false", 1},
		{"WHBIAB_DISABLE on", "WHBIAB_DISABLE", "1", 0},
		{"WHBIAB_DISABLE zero", "WHBIAB_DISABLE", "0", 1},
	} {
		t.Run(tc.name, func(t *testing.T) {
			rec := newServer(t)
			t.Setenv(tc.key, tc.value)

			track(t.Context(), "tool", "query")()

			if got := len(rec.requests()); got != tc.want {
				t.Errorf("got %d requests, want %d", got, tc.want)
			}
		})
	}
}

func TestTrackSkipsEmptyClient(t *testing.T) {
	rec := newServer(t)

	track(t.Context(), " // ", "query")()

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

	track(t.Context(), "tool")()
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
	track(t.Context(), "tool")()
	if elapsed := time.Since(start); elapsed > 2*time.Second {
		t.Errorf("wait took %v, want it bounded by the timeout", elapsed)
	}
}

func TestTrackStopsWhenContextEnds(t *testing.T) {
	rec := newServer(t)
	ctx, cancel := context.WithCancel(t.Context())
	cancel()

	track(ctx, "tool")()

	if got := len(rec.requests()); got != 0 {
		t.Errorf("got %d requests with a canceled context, want 0", got)
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

	track(t.Context(), "tool")()

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

// newRoot returns a program with a persistent flag, a subcommand with its own
// persistent pre-run hook, and a command that fails.
func newRoot(t *testing.T, ran *[]string) *cobra.Command {
	t.Helper()
	root := &cobra.Command{
		Use:           "tool",
		SilenceUsage:  true,
		SilenceErrors: true,
		PersistentPreRun: func(*cobra.Command, []string) {
			*ran = append(*ran, "root pre-run")
		},
	}
	root.PersistentFlags().Bool("verbose", false, "")
	root.SetOut(io.Discard)
	root.SetErr(io.Discard)

	query := &cobra.Command{
		Use:  "query",
		Args: cobra.ArbitraryArgs,
		PersistentPreRun: func(*cobra.Command, []string) {
			*ran = append(*ran, "query pre-run")
		},
		Run: func(*cobra.Command, []string) { *ran = append(*ran, "query") },
	}
	query.Flags().StringP("format", "f", "table", "")
	query.Flags().Int("width", 60, "")
	root.AddCommand(query)

	root.AddCommand(&cobra.Command{
		Use:  "fail",
		RunE: func(*cobra.Command, []string) error { return errors.New("boom") },
	})
	return root
}

func executeArgs(t *testing.T, args ...string) (ran []string, err error) {
	t.Helper()
	root := newRoot(t, &ran)
	root.SetArgs(args)
	err = Execute(t.Context(), root)
	return ran, err
}

func TestExecuteSendsSubcommandAndFlagNames(t *testing.T) {
	rec := newServer(t)

	ran, err := executeArgs(t, "query", "--verbose", "-f", "json", "--width=80", "SELECT secret")

	if err != nil {
		t.Fatal(err)
	}
	if want := []string{"root pre-run", "query pre-run", "query"}; !slices.Equal(ran, want) {
		t.Errorf("ran %v, want %v", ran, want)
	}
	reqs := rec.requests()
	if len(reqs) != 1 {
		t.Fatalf("got %d requests, want 1", len(reqs))
	}
	got := reqs[0].URL.Path
	if want := "/wehadababyitsaboy/tool/query.format.verbose.width"; got != want {
		t.Errorf("path = %q, want %q", got, want)
	}
	if strings.Contains(reqs[0].URL.String(), "secret") || strings.Contains(reqs[0].URL.String(), "json") {
		t.Errorf("ping %q carries a value", reqs[0].URL)
	}
}

func TestExecuteWithoutFlags(t *testing.T) {
	rec := newServer(t)

	if _, err := executeArgs(t, "query"); err != nil {
		t.Fatal(err)
	}

	reqs := rec.requests()
	if len(reqs) != 1 || reqs[0].URL.Path != "/wehadababyitsaboy/tool/query" {
		t.Errorf("requests = %v, want one for tool/query", reqs)
	}
}

func TestExecuteReturnsCommandError(t *testing.T) {
	rec := newServer(t)

	_, err := executeArgs(t, "fail")

	if err == nil || err.Error() != "boom" {
		t.Errorf("err = %v, want boom", err)
	}
	if got := len(rec.requests()); got != 1 {
		t.Errorf("got %d requests, want 1", got)
	}
}

func TestExecuteSendsNothingForHelpAndCompletion(t *testing.T) {
	rec := newServer(t)

	for _, args := range [][]string{
		{"query", "--help"},
		{"help", "query"},
		{"completion", "bash"},
		{cobra.ShellCompRequestCmd, "query", ""},
	} {
		if _, err := executeArgs(t, args...); err != nil {
			t.Fatalf("%v: %v", args, err)
		}
	}

	if got := len(rec.requests()); got != 0 {
		t.Errorf("got %d requests, want 0", got)
	}
}

func TestExecuteSendsNothingForBadFlag(t *testing.T) {
	rec := newServer(t)

	if _, err := executeArgs(t, "query", "--nope"); err == nil {
		t.Error("want an error for an unknown flag")
	}

	if got := len(rec.requests()); got != 0 {
		t.Errorf("got %d requests, want 0", got)
	}
}

func TestExecuteKeepsRootPersistentPreRunE(t *testing.T) {
	newServer(t)
	var ran []string
	root := newRoot(t, &ran)
	root.PersistentPreRun = nil
	root.PersistentPreRunE = func(*cobra.Command, []string) error { return errors.New("stop") }
	root.SetArgs([]string{"query"})

	err := Execute(t.Context(), root)

	if err == nil || err.Error() != "stop" {
		t.Errorf("err = %v, want stop", err)
	}
}

func TestExecuteHonorsOptOut(t *testing.T) {
	rec := newServer(t)
	t.Setenv("DO_NOT_TRACK", "1")

	if _, err := executeArgs(t, "query"); err != nil {
		t.Fatal(err)
	}

	if got := len(rec.requests()); got != 0 {
		t.Errorf("got %d requests, want 0", got)
	}
}

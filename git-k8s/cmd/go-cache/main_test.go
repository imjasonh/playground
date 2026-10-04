package main

import (
	"archive/zip"
	"bufio"
	"bytes"
	"context"
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"log/slog"
	"net"
	"net/http"
	"net/http/httptest"
	"net/url"
	"os"
	"os/exec"
	"path/filepath"
	"slices"
	"strings"
	"sync"
	"sync/atomic"
	"testing"
	"time"

	"github.com/imjasonh/playground/git-k8s/internal/gocache"
)

// TestMain runs the test binary as a GOCACHEPROG program for the go command
// in TestGoCommand.
func TestMain(m *testing.M) {
	if dir := os.Getenv("GO_CACHE_TEST_DIR"); dir != "" {
		p := &gocache.Prog{Dir: dir, Remote: os.Getenv("GO_CACHE_TEST_REMOTE"), TokenFile: os.Getenv("GO_CACHE_TEST_TOKEN"), Log: os.Stderr}
		if err := p.Run(context.Background(), os.Stdin, os.Stdout); err != nil { // pasta:ignore use_t_context — TestMain has no t
			fmt.Fprintln(os.Stderr, err)
			os.Exit(1)
		}
		os.Exit(0)
	}
	os.Exit(m.Run())
}

// fakeReviewer accepts the tokens it holds, for their audiences.
type fakeReviewer map[string]fakeToken

type fakeToken struct {
	namespace string
	audiences []string
}

func (f fakeReviewer) review(_ context.Context, token, audience string) (string, error) {
	t, ok := f[token]
	if !ok || !slices.Contains(t.audiences, audience) {
		return "", fmt.Errorf("%w: no", errDenied)
	}
	return t.namespace, nil
}

func newTestServer(t *testing.T, upstream string, rev reviewer) (*server, *httptest.Server) {
	t.Helper()
	m := newMetrics()
	log := slog.New(slog.DiscardHandler)
	st, err := openStore(t.TempDir(), 1<<30, m, log)
	if err != nil {
		t.Fatal(err)
	}
	s := &server{store: st, upstream: upstream, client: http.DefaultClient, reviewer: rev, metrics: m, log: log}
	srv := httptest.NewServer(s.handler())
	t.Cleanup(srv.Close)
	return s, srv
}

func (m *metrics) count(key string) int64 {
	m.mu.Lock()
	defer m.mu.Unlock()
	if v, ok := m.build[key]; ok {
		return v
	}
	return m.modules[key]
}

func id(s string) string {
	sum := sha256.Sum256([]byte(s))
	return hex.EncodeToString(sum[:])
}

func do(t *testing.T, method, url, token string, body io.Reader, header map[string]string) (*http.Response, string) {
	t.Helper()
	req, err := http.NewRequest(method, url, body)
	if err != nil {
		t.Fatal(err)
	}
	if token != "" {
		req.Header.Set("Authorization", "Bearer "+token)
	}
	for k, v := range header {
		req.Header.Set(k, v)
	}
	resp, err := http.DefaultClient.Do(req)
	if err != nil {
		t.Fatal(err)
	}
	defer resp.Body.Close()
	b, err := io.ReadAll(resp.Body)
	if err != nil {
		t.Fatal(err)
	}
	return resp, string(b)
}

func TestBuildCache(t *testing.T) {
	read, write := gocache.ReadAudience("ns", "app"), gocache.WriteAudience("ns", "app")
	s, srv := newTestServer(t, "", fakeReviewer{
		"reader": {"ns", []string{read}},
		"writer": {"ns", []string{write}},
		"other":  {"other", []string{read, write}},
	})
	action := id("action")
	url := srv.URL + gocache.Path("ns", "app") + "/" + action
	put := func(token, body, output string) int {
		resp, msg := do(t, http.MethodPut, url, token, strings.NewReader(body), map[string]string{gocache.OutputIDHeader: output})
		t.Logf("PUT %q: %s %s", body, resp.Status, strings.TrimSpace(msg))
		return resp.StatusCode
	}
	if resp, _ := do(t, http.MethodGet, url, "reader", nil, nil); resp.StatusCode != http.StatusNotFound {
		t.Errorf("GET before PUT: %s, want 404", resp.Status)
	}
	for _, tc := range []struct {
		token, body, output string
		want                int
	}{
		{"", "compiled", id("compiled"), http.StatusUnauthorized},
		{"reader", "compiled", id("compiled"), http.StatusForbidden},
		{"other", "compiled", id("compiled"), http.StatusForbidden},
		{"writer", "compiled", id("something else"), http.StatusBadRequest},
		{"writer", "compiled", strings.ToUpper(id("compiled")), http.StatusBadRequest},
		{"writer", "compiled", id("compiled"), http.StatusCreated},
		{"writer", "compiled", id("compiled"), http.StatusOK},
		{"writer", "tampered", id("tampered"), http.StatusConflict},
	} {
		if got := put(tc.token, tc.body, tc.output); got != tc.want {
			t.Errorf("PUT %q with token %q and output ID %.8s: %d, want %d", tc.body, tc.token, tc.output, got, tc.want)
		}
	}
	for token, want := range map[string]int{"writer": http.StatusForbidden, "other": http.StatusForbidden, "": http.StatusUnauthorized} {
		if resp, _ := do(t, http.MethodGet, url, token, nil, nil); resp.StatusCode != want {
			t.Errorf("GET with token %q: %s, want %d", token, resp.Status, want)
		}
	}
	resp, body := do(t, http.MethodGet, url, "reader", nil, nil)
	if resp.StatusCode != http.StatusOK || body != "compiled" || resp.Header.Get(gocache.OutputIDHeader) != id("compiled") || resp.ContentLength != 8 {
		t.Errorf("GET: %s %q, output ID %q, length %d", resp.Status, body, resp.Header.Get(gocache.OutputIDHeader), resp.ContentLength)
	}

	t.Log("A PUT needs a Content-Length, and a body that's that long.")
	chunked := io.MultiReader(strings.NewReader("compiled"))
	if resp, _ := do(t, http.MethodPut, srv.URL+gocache.Path("ns", "app")+"/"+id("chunked"), "writer", chunked, map[string]string{gocache.OutputIDHeader: id("compiled")}); resp.StatusCode != http.StatusLengthRequired {
		t.Errorf("chunked PUT: %s, want 411", resp.Status)
	}
	short := gocache.Path("ns", "app") + "/" + id("short")
	if code := putShort(t, srv.URL, short, "writer"); code != http.StatusBadRequest {
		t.Errorf("PUT of a body shorter than its Content-Length: %d, want 400", code)
	}
	if resp, _ := do(t, http.MethodGet, srv.URL+short, "reader", nil, nil); resp.StatusCode != http.StatusNotFound {
		t.Errorf("GET after a short PUT: %s, want 404", resp.Status)
	}

	t.Log("Requests with bad paths fail before go-cache checks their tokens.")
	for _, path := range []string{
		gocache.Path("NS", "app") + "/" + action,
		gocache.Path("ns", "a..b") + "/" + action,
		gocache.Path("ns", "app") + "/" + action[:10],
		gocache.Path("ns", "app") + "/" + strings.ToUpper(action),
	} {
		if resp, _ := do(t, http.MethodGet, srv.URL+path, "reader", nil, nil); resp.StatusCode != http.StatusBadRequest {
			t.Errorf("GET %s: %s, want 400", path, resp.Status)
		}
	}
	for key, want := range map[string]int64{"GET hit": 1, "GET miss": 2, "PUT created": 1, "PUT exists": 1, "PUT conflict": 1, "PUT invalid": 4, "GET invalid": 4} {
		if got := s.metrics.count(key); got != want {
			t.Errorf("%s requests: %d, want %d", key, got, want)
		}
	}
}

// putShort sends a PUT whose body ends before its Content-Length, as a
// client that fails partway does, and returns the status.
func putShort(t *testing.T, srvURL, path, token string) int {
	t.Helper()
	u, err := url.Parse(srvURL)
	if err != nil {
		t.Fatal(err)
	}
	conn, err := net.Dial("tcp", u.Host)
	if err != nil {
		t.Fatal(err)
	}
	defer conn.Close()
	fmt.Fprintf(conn, "PUT %s HTTP/1.1\r\nHost: %s\r\nAuthorization: Bearer %s\r\n%s: %s\r\nContent-Length: 8\r\n\r\ncomp",
		path, u.Host, token, gocache.OutputIDHeader, id("compiled"))
	if err := conn.(*net.TCPConn).CloseWrite(); err != nil {
		t.Fatal(err)
	}
	resp, err := http.ReadResponse(bufio.NewReader(conn), nil)
	if err != nil {
		t.Fatal(err)
	}
	resp.Body.Close()
	return resp.StatusCode
}

func TestBuildCacheNeedsAReviewer(t *testing.T) {
	_, srv := newTestServer(t, "", nil)
	if resp, _ := do(t, http.MethodGet, srv.URL+gocache.Path("ns", "app")+"/"+id("a"), "token", nil, nil); resp.StatusCode != http.StatusServiceUnavailable {
		t.Errorf("GET without a reviewer: %s, want 503", resp.Status)
	}
}

func TestParseModuleRequest(t *testing.T) {
	for p, want := range map[string]string{
		"example.com/!greet/@v/list":                                 "example.com/!greet @v/list",
		"example.com/greet/@v/v1.2.3.info":                           "example.com/greet @v/v1.2.3.info",
		"example.com/greet/@v/v1.2.3-pre.1+incompatible.zip":         "example.com/greet @v/v1.2.3-pre.1+incompatible.zip",
		"example.com/greet/@v/master.info":                           "example.com/greet @v/master.info",
		"example.com/greet/@latest":                                  "example.com/greet @latest",
		"golang.org/x/mod/@v/v0.0.0-20240101000000-0123456789ab.mod": "golang.org/x/mod @v/v0.0.0-20240101000000-0123456789ab.mod",
	} {
		if m, f, ok := parseModuleRequest(p); !ok || m+" "+f != want {
			t.Errorf("parseModuleRequest(%q) = %q, %q, %v; want %q", p, m, f, ok, want)
		}
	}
	for _, p := range []string{
		"", "example.com/greet", "example.com/greet/@v/", "example.com/greet/@v/v1.2.3",
		"example.com/greet/@v/v1.2.3.exe", "example.com/greet/@v/.info", "../greet/@v/list",
		"example.com/../greet/@v/list", "example.com//greet/@v/list", "example.com/Greet/@v/list",
		"example.com/greet/@v/v1/2.info", "example.com/gr%65et/@v/list", "/@latest",
		"sumdb/sum.golang.org/supported",
	} {
		if m, f, ok := parseModuleRequest(p); ok {
			t.Errorf("parseModuleRequest(%q) = %q, %q; want an error", p, m, f)
		}
	}
}

func TestModuleProxy(t *testing.T) {
	var mu sync.Mutex
	requests := map[string]int{}
	files := map[string]string{
		"/example.com/!greet/@v/list":        "v1.0.0\n",
		"/example.com/!greet/@v/v1.0.0.mod":  "module example.com/Greet\n",
		"/example.com/!greet/@v/master.info": `{"Version":"v1.0.1-0.20240101000000-0123456789ab"}`,
		"/example.com/!greet/@latest":        `{"Version":"v1.0.0"}`,
	}
	upstream := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		mu.Lock()
		requests[r.URL.Path]++
		mu.Unlock()
		if r.URL.Path == "/example.com/broken/@v/v1.0.0.mod" {
			http.Error(w, "upstream is broken", http.StatusInternalServerError)
			return
		}
		body, ok := files[r.URL.Path]
		if !ok {
			http.Error(w, "not found: "+r.URL.Path, http.StatusGone)
			return
		}
		io.WriteString(w, body)
	}))
	t.Cleanup(upstream.Close)
	upstreamRequests := func(path string) int {
		mu.Lock()
		defer mu.Unlock()
		return requests[path]
	}
	s, srv := newTestServer(t, upstream.URL, nil)
	for _, tc := range []struct {
		path, body, contentType string
		status, upstream        int
	}{
		{"example.com/!greet/@v/v1.0.0.mod", "module example.com/Greet\n", "text/plain; charset=utf-8", 200, 1},
		{"example.com/!greet/@v/v1.0.0.mod", "module example.com/Greet\n", "text/plain; charset=utf-8", 200, 1},
		{"example.com/!greet/@v/list", "v1.0.0\n", "text/plain; charset=utf-8", 200, 1},
		{"example.com/!greet/@v/list", "v1.0.0\n", "text/plain; charset=utf-8", 200, 2},
		{"example.com/!greet/@latest", `{"Version":"v1.0.0"}`, "application/json", 200, 1},
		{"example.com/!greet/@v/master.info", `{"Version":"v1.0.1-0.20240101000000-0123456789ab"}`, "application/json", 200, 1},
		{"example.com/!greet/@v/master.info", `{"Version":"v1.0.1-0.20240101000000-0123456789ab"}`, "application/json", 200, 2},
		{"example.com/!greet/@v/v9.9.9.info", "not found: /example.com/!greet/@v/v9.9.9.info\n", "text/plain; charset=utf-8", 410, 1},
		{"example.com/broken/@v/v1.0.0.mod", "", "", 502, 1},
		{"example.com/broken/@v/v1.0.0.mod", "", "", 502, 2},
		{"example.com/Greet/@v/list", "", "", 404, 0},
	} {
		resp, body := do(t, http.MethodGet, srv.URL+"/mod/"+tc.path, "", nil, nil)
		if resp.StatusCode != tc.status || (tc.body != "" && body != tc.body) || (tc.contentType != "" && resp.Header.Get("Content-Type") != tc.contentType) {
			t.Errorf("GET %s: %s %q (%s); want %d %q (%s)", tc.path, resp.Status, body, resp.Header.Get("Content-Type"), tc.status, tc.body, tc.contentType)
		}
		if got := upstreamRequests("/" + tc.path); got != tc.upstream {
			t.Errorf("after GET %s, %d upstream requests for it, want %d", tc.path, got, tc.upstream)
		}
	}
	for result, want := range map[string]int64{"hit": 1, "fetched": 1, "passthrough": 5, "not_found": 2, "error": 2} {
		if got := s.metrics.count(result); got != want {
			t.Errorf("%s module requests: %d, want %d", result, got, want)
		}
	}
}

func moduleZip(t *testing.T, prefix string, files map[string]string) []byte {
	t.Helper()
	var buf bytes.Buffer
	zw := zip.NewWriter(&buf)
	for name, body := range files {
		w, err := zw.Create(prefix + name)
		if err != nil {
			t.Fatal(err)
		}
		io.WriteString(w, body)
	}
	if err := zw.Close(); err != nil {
		t.Fatal(err)
	}
	return buf.Bytes()
}

func goEnv(home string, env ...string) []string {
	return append(os.Environ(), append([]string{
		"HOME=" + home, "GOENV=off", "GOFLAGS=-modcacherw", "GOPATH=" + filepath.Join(home, "go"),
		"GOCACHE=" + filepath.Join(home, "go-build"), "GOTOOLCHAIN=local", "CGO_ENABLED=0",
		"GOSUMDB=off", "GOPROXY=off",
	}, env...)...)
}

// TestGoModDownload downloads a module with the go command through
// go-cache twice, into empty module caches. The second download doesn't
// reach the upstream proxy.
func TestGoModDownload(t *testing.T) {
	gobin, err := exec.LookPath("go")
	if err != nil {
		t.Skip("go isn't installed")
	}
	mod := "module example.com/greet\n\ngo 1.24\n"
	files := map[string][]byte{
		"/example.com/greet/@v/list":        []byte("v1.0.0\n"),
		"/example.com/greet/@v/v1.0.0.info": []byte(`{"Version":"v1.0.0","Time":"2024-01-01T00:00:00Z"}`),
		"/example.com/greet/@v/v1.0.0.mod":  []byte(mod),
		"/example.com/greet/@v/v1.0.0.zip": moduleZip(t, "example.com/greet@v1.0.0/", map[string]string{
			"go.mod":   mod,
			"greet.go": "package greet\n\nfunc Hello() string { return \"hello\" }\n",
		}),
	}
	var requests atomic.Int32
	upstream := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		requests.Add(1)
		body, ok := files[r.URL.Path]
		if !ok {
			http.NotFound(w, r)
			return
		}
		w.Write(body)
	}))
	t.Cleanup(upstream.Close)
	_, srv := newTestServer(t, upstream.URL, nil)
	download := func() {
		t.Helper()
		home := t.TempDir()
		cmd := exec.Command(gobin, "mod", "download", "-json", "example.com/greet@v1.0.0")
		cmd.Dir = home
		cmd.Env = goEnv(home, "GOPROXY="+srv.URL+"/mod")
		out, err := cmd.CombinedOutput()
		if err != nil {
			t.Fatalf("go mod download: %v\n%s", err, out)
		}
		var got struct{ Dir, Error string }
		if err := json.Unmarshal(out, &got); err != nil || got.Error != "" {
			t.Fatalf("go mod download: %v %s\n%s", err, got.Error, out)
		}
		if _, err := os.Stat(filepath.Join(got.Dir, "greet.go")); err != nil {
			t.Error(err)
		}
	}
	download()
	first := requests.Load()
	download()
	if n := requests.Load(); n != first {
		t.Errorf("the second download made %d upstream requests, want none", n-first)
	}
}

// TestGoCommand builds a module twice with the go command and
// gocache.Prog, with empty local directories, through go-cache. The second
// build reads every output that the first one uploaded.
func TestGoCommand(t *testing.T) {
	gobin, err := exec.LookPath("go")
	if err != nil {
		t.Skip("go isn't installed")
	}
	self, err := os.Executable()
	if err != nil {
		t.Fatal(err)
	}
	mod := t.TempDir()
	for name, src := range map[string]string{
		"go.mod": "module example.com/m\n\ngo 1.24\n",
		"a/a.go": "package a\n\nimport \"example.com/m/b\"\n\nfunc A() int { return b.B() + 1 }\n",
		"b/b.go": "package b\n\nfunc B() int { return 1 }\n",
	} {
		if err := os.MkdirAll(filepath.Join(mod, filepath.Dir(name)), 0o755); err != nil {
			t.Fatal(err)
		}
		if err := os.WriteFile(filepath.Join(mod, name), []byte(src), 0o644); err != nil {
			t.Fatal(err)
		}
	}
	tokens := t.TempDir()
	tokenFile := func(token string) string {
		f := filepath.Join(tokens, token)
		if err := os.WriteFile(f, []byte(token+"\n"), 0o600); err != nil {
			t.Fatal(err)
		}
		return f
	}
	s, srv := newTestServer(t, "", fakeReviewer{
		"reader": {"ns", []string{gocache.ReadAudience("ns", "app")}},
		"writer": {"ns", []string{gocache.WriteAudience("ns", "app")}},
	})
	remote := srv.URL + gocache.Path("ns", "app")
	home := t.TempDir()
	build := func(dir string) string {
		t.Helper()
		cmd := exec.Command(gobin, "list", "-export", "-f={{.Export}}", "./...")
		cmd.Dir = mod
		cmd.Env = goEnv(home, "GOCACHEPROG="+self,
			"GO_CACHE_TEST_DIR="+dir, "GO_CACHE_TEST_REMOTE="+remote, "GO_CACHE_TEST_TOKEN="+tokenFile("reader"))
		var stderr bytes.Buffer
		cmd.Stderr = &stderr
		out, err := cmd.Output()
		if err != nil || stderr.Len() > 0 {
			t.Fatalf("go list: %v\n%s", err, stderr.Bytes())
		}
		return string(out)
	}

	first := t.TempDir()
	build(first)
	if _, _, err := gocache.Upload(t.Context(), nil, first, remote, tokenFile("reader")); err == nil {
		t.Error("Upload with the token that reads succeeded")
	}
	stored, had, err := gocache.Upload(t.Context(), nil, first, remote, tokenFile("writer"))
	if err != nil || stored == 0 || had != 0 {
		t.Fatalf("Upload = %d stored, %d had, %v", stored, had, err)
	}

	second := t.TempDir()
	for _, export := range strings.Fields(build(second)) {
		if !strings.HasPrefix(export, second+string(filepath.Separator)) {
			t.Errorf("export data %s isn't from the second build's directory", export)
		}
	}
	// The go command stores some entries, such as the list of a package's
	// compiled files, that a later build doesn't read.
	if hits := s.metrics.count("GET hit"); hits < 2 || hits > int64(stored) {
		t.Errorf("the second build read %d outputs from go-cache, want 2 to %d", hits, stored)
	}
	again, had, err := gocache.Upload(t.Context(), nil, second, remote, tokenFile("writer"))
	if err != nil || again != 0 || had != 0 {
		t.Errorf("Upload after the second build = %d stored, %d had, %v; want nothing, because it compiled nothing", again, had, err)
	}
}

func TestTokenReviewer(t *testing.T) {
	var calls atomic.Int32
	api := httptest.NewTLSServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		calls.Add(1)
		if r.Method != http.MethodPost || r.URL.Path != "/apis/authentication.k8s.io/v1/tokenreviews" || r.Header.Get("Authorization") != "Bearer own-token" {
			http.Error(w, "unexpected request", http.StatusBadRequest)
			return
		}
		var tr tokenReview
		if err := json.NewDecoder(r.Body).Decode(&tr); err != nil || tr.Kind != "TokenReview" {
			http.Error(w, "bad TokenReview", http.StatusBadRequest)
			return
		}
		s := &tr.Status
		switch tr.Spec.Token {
		case "good":
			s.Authenticated, s.User.Username = true, "system:serviceaccount:ns:default"
			if slices.Contains(tr.Spec.Audiences, "aud") {
				s.Audiences = []string{"aud"}
			}
		case "audience-unaware":
			s.Authenticated, s.User.Username = true, "system:serviceaccount:ns:default"
		case "user":
			s.Authenticated, s.User.Username, s.Audiences = true, "alice", tr.Spec.Audiences
		case "broken":
			http.Error(w, "etcd is down", http.StatusInternalServerError)
			return
		default:
			s.Error = "invalid bearer token"
		}
		w.WriteHeader(http.StatusCreated)
		json.NewEncoder(w).Encode(tr)
	}))
	t.Cleanup(api.Close)
	tokenFile := filepath.Join(t.TempDir(), "token")
	if err := os.WriteFile(tokenFile, []byte("own-token\n"), 0o600); err != nil {
		t.Fatal(err)
	}
	r := newTokenReviewer(api.URL, tokenFile, api.Client())
	review := func(token string) (string, error) {
		t.Helper()
		return r.review(t.Context(), token, "aud")
	}

	for range 2 {
		if ns, err := review("good"); err != nil || ns != "ns" {
			t.Errorf("review of a good token = %q, %v", ns, err)
		}
	}
	if n := calls.Load(); n != 1 {
		t.Errorf("%d reviews of the same token, want 1", n)
	}
	for _, token := range []string{"bad", "audience-unaware", "user", "bad"} {
		if ns, err := review(token); !errors.Is(err, errDenied) {
			t.Errorf("review of %q = %q, %v; want it denied", token, ns, err)
		}
	}
	if n := calls.Load(); n != 4 {
		t.Errorf("%d reviews, want 4, because denials are remembered too", n)
	}
	for range 2 {
		if _, err := review("broken"); err == nil || errors.Is(err, errDenied) {
			t.Errorf("review when the API server fails = %v, want an error that isn't a denial", err)
		}
	}
	if n := calls.Load(); n != 6 {
		t.Errorf("%d reviews, want 6, because failures aren't remembered", n)
	}
	if _, err := r.review(t.Context(), "good", "another audience"); err == nil {
		t.Error("a review for one audience let the token through for another")
	}
}

func TestStore(t *testing.T) {
	dir := t.TempDir()
	m := newMetrics()
	s, err := openStore(dir, 100, m, slog.New(slog.DiscardHandler))
	if err != nil {
		t.Fatal(err)
	}
	put := func(key string, age time.Duration) bool {
		t.Helper()
		created, err := s.put(key, func(w io.Writer) error {
			_, err := w.Write(bytes.Repeat([]byte("x"), 40))
			return err
		})
		if err != nil {
			t.Fatal(err)
		}
		if created {
			then := time.Now().Add(-age)
			if err := os.Chtimes(s.path(key), then, then); err != nil {
				t.Fatal(err)
			}
		}
		return created
	}
	exists := func(key string) bool {
		_, err := os.Stat(s.path(key))
		return err == nil
	}
	put("mod/a", 3*time.Hour)
	put("mod/b", 2*time.Hour)
	if put("mod/b", 0) {
		t.Error("a second put of a key created it again")
	}
	put("build/c", 30*time.Minute)
	if exists("mod/a") || !exists("mod/b") || !exists("build/c") || m.stored.Load() != 80 || m.evicted.Load() != 40 {
		t.Errorf("after passing the limit: a %v, b %v, c %v, %d stored, %d evicted; want only the oldest, a, evicted",
			exists("mod/a"), exists("mod/b"), exists("build/c"), m.stored.Load(), m.evicted.Load())
	}

	t.Log("Reading a file marks it as used.")
	f, err := s.open("mod/b")
	if err != nil {
		t.Fatal(err)
	}
	f.Close()
	put("build/d", 0)
	if !exists("mod/b") || exists("build/c") {
		t.Errorf("after reading b: b %v, c %v; want c evicted", exists("mod/b"), exists("build/c"))
	}

	t.Log("Reopening the store counts its files and removes temporary ones.")
	if err := os.WriteFile(filepath.Join(dir, "tmp", "put-1"), []byte("partial"), 0o644); err != nil {
		t.Fatal(err)
	}
	m2 := newMetrics()
	if _, err := openStore(dir, 100, m2, slog.New(slog.DiscardHandler)); err != nil {
		t.Fatal(err)
	}
	if m2.stored.Load() != 80 {
		t.Errorf("reopened store holds %d bytes, want 80", m2.stored.Load())
	}
	if _, err := os.Stat(filepath.Join(dir, "tmp", "put-1")); err == nil {
		t.Error("reopening the store left a temporary file")
	}
}

func TestParseSize(t *testing.T) {
	for s, want := range map[string]int64{"1": 1, "512Mi": 512 << 20, "8Gi": 8 << 30, "2Ti": 2 << 40, "10k": 10e3, "3G": 3e9} {
		if got, err := parseSize(s); err != nil || got != want {
			t.Errorf("parseSize(%q) = %d, %v; want %d", s, got, err, want)
		}
	}
	for _, s := range []string{"", "0", "-1Gi", "1.5Gi", "Gi", "1Gb", "99999999999Ti"} {
		if got, err := parseSize(s); err == nil {
			t.Errorf("parseSize(%q) = %d, want an error", s, got)
		}
	}
}

func TestMetricsPage(t *testing.T) {
	s, srv := newTestServer(t, "", nil)
	s.metrics.buildRequest("GET", "hit")
	s.metrics.moduleRequest("fetched")
	s.metrics.stored.Store(42)
	resp, body := do(t, http.MethodGet, srv.URL+"/metrics", "", nil, nil)
	for _, line := range []string{
		`go_cache_build_requests_total{method="GET",result="hit"} 1`,
		`go_cache_build_requests_total{method="PUT",result="created"} 0`,
		`go_cache_module_requests_total{result="fetched"} 1`,
		`go_cache_stored_bytes 42`,
		`go_cache_evicted_bytes_total 0`,
	} {
		if !strings.Contains(body, line+"\n") {
			t.Errorf("/metrics (%s) lacks %q:\n%s", resp.Status, line, body)
		}
	}
}

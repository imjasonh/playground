package main

import (
	"archive/zip"
	"bufio"
	"bytes"
	"context"
	"crypto/sha256"
	"encoding/base64"
	"encoding/hex"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"io/fs"
	"log/slog"
	"net"
	"net/http"
	"net/http/httptest"
	"net/url"
	"os"
	"os/exec"
	"path/filepath"
	"slices"
	"strconv"
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
		p := &gocache.Prog{Dir: dir, Remote: os.Getenv("GO_CACHE_TEST_REMOTE"), TokenFile: os.Getenv("GO_CACHE_TEST_TOKEN"), Share: true, Log: os.Stderr}
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

// newTestServer starts a go-cache server, after letting each of configure
// change its store.
func newTestServer(t *testing.T, upstream string, rev reviewer, configure ...func(*store)) (*server, *httptest.Server) {
	t.Helper()
	m := newMetrics()
	log := slog.New(slog.DiscardHandler)
	st, err := openStore(t.TempDir(), 1<<30, m, log)
	if err != nil {
		t.Fatal(err)
	}
	for _, c := range configure {
		c(st)
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

// TestConcurrentModuleFetches sends 20 requests at once for a 5 MiB zip that
// go-cache doesn't have, with a store that holds 10 MiB. The upstream sends
// half of the zip, and the rest once every request has reached go-cache.
func TestConcurrentModuleFetches(t *testing.T) {
	const size, maxSize, clients = 5 << 20, 10 << 20, 20
	zip := bytes.Repeat([]byte("z"), size)
	want := sha256.Sum256(zip)
	var fetches atomic.Int32
	release := make(chan struct{})
	upstream := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		fetches.Add(1)
		w.Header().Set("Content-Length", strconv.Itoa(size))
		w.Write(zip[:size/2])
		w.(http.Flusher).Flush()
		select {
		case <-release:
			w.Write(zip[size/2:])
		case <-r.Context().Done():
		}
	}))
	t.Cleanup(upstream.Close)
	s, _ := newTestServer(t, upstream.URL, nil, func(st *store) { st.max = maxSize })
	var entered atomic.Int32
	h := s.handler()
	srv := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		entered.Add(1)
		h.ServeHTTP(w, r)
	}))
	t.Cleanup(srv.Close)
	releaseUpstream := sync.OnceFunc(func() { close(release) })
	t.Cleanup(releaseUpstream)

	// usage returns the bytes in the store's files, and counts a file with
	// two links once.
	usage := func() int64 {
		var seen []fs.FileInfo
		var total int64
		filepath.WalkDir(s.store.dir, func(_ string, d fs.DirEntry, err error) error {
			if err != nil || d.IsDir() {
				return nil
			}
			fi, err := d.Info()
			if err != nil || slices.ContainsFunc(seen, func(o fs.FileInfo) bool { return os.SameFile(o, fi) }) {
				return nil
			}
			seen = append(seen, fi)
			total += fi.Size()
			return nil
		})
		return total
	}
	var peak int64
	stop, sampled := make(chan struct{}), make(chan struct{})
	go func() {
		defer close(sampled)
		for {
			peak = max(peak, usage())
			select {
			case <-stop:
				return
			case <-t.Context().Done():
				return
			case <-time.After(time.Millisecond):
			}
		}
	}()

	type result struct {
		status int
		sum    [sha256.Size]byte
		err    error
	}
	results := make([]result, clients)
	var wg sync.WaitGroup
	for i := range clients {
		wg.Go(func() {
			resp, err := http.Get(srv.URL + "/mod/example.com/big/@v/v1.0.0.zip")
			if err != nil {
				results[i].err = err
				return
			}
			defer resp.Body.Close()
			h := sha256.New()
			_, err = io.Copy(h, resp.Body)
			results[i] = result{resp.StatusCode, [sha256.Size]byte(h.Sum(nil)), err}
		})
	}
	deadline := time.Now().Add(time.Minute)
	for entered.Load() < clients {
		if time.Now().After(deadline) {
			t.Fatalf("only %d of %d requests reached go-cache", entered.Load(), clients)
		}
		time.Sleep(time.Millisecond)
	}
	// Requests that each fetched the zip would all be waiting on the
	// upstream by now, with half of it in a temporary file.
	time.Sleep(200 * time.Millisecond)
	releaseUpstream()
	wg.Wait()
	close(stop)
	<-sampled

	if n := fetches.Load(); n != 1 {
		t.Errorf("%d requests at once for a zip that go-cache didn't have fetched it from the upstream %d times, want once", clients, n)
	}
	for i, r := range results {
		if r.err != nil || r.status != http.StatusOK || r.sum != want {
			t.Errorf("request %d: %d, %v; body matches the zip: %v", i, r.status, r.err, r.sum == want)
		}
	}
	t.Logf("The store's files took up to %d bytes.", peak)
	if peak > maxSize {
		t.Errorf("the store's files took up to %d bytes, more than its maximum of %d", peak, maxSize)
	}
	s.store.mu.Lock()
	stored, reserved := s.store.size, s.store.reserved
	s.store.mu.Unlock()
	if stored != size || reserved != 0 {
		t.Errorf("the store holds %d bytes, and writes hold %d; want %d and 0", stored, reserved, size)
	}
	for result, want := range map[string]int64{"fetched": 1, "hit": clients - 1} {
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

// testToken returns a token shaped like a service account token, with a
// subject, and aud, which can be a string or a list of strings.
func testToken(t *testing.T, subject string, aud any) string {
	t.Helper()
	enc := func(v any) string {
		b, err := json.Marshal(v)
		if err != nil {
			t.Fatal(err)
		}
		return base64.RawURLEncoding.EncodeToString(b)
	}
	return enc(map[string]string{"alg": "RS256"}) + "." + enc(map[string]any{"aud": aud, "sub": subject}) + ".c2lnbmF0dXJl"
}

// tokenSubject returns the subject of a token from testToken.
func tokenSubject(token string) string {
	parts := strings.Split(token, ".")
	if len(parts) != 3 {
		return ""
	}
	b, err := base64.RawURLEncoding.DecodeString(parts[1])
	if err != nil {
		return ""
	}
	var claims struct {
		Sub string `json:"sub"`
	}
	json.Unmarshal(b, &claims)
	return claims.Sub
}

// newTokenAPI starts a fake API server that answers TokenReviews with
// answer, and returns a tokenReviewer that uses it.
func newTokenAPI(t *testing.T, answer func(w http.ResponseWriter, r *http.Request, tr *tokenReview)) *tokenReviewer {
	t.Helper()
	api := httptest.NewTLSServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		if r.Method != http.MethodPost || r.URL.Path != "/apis/authentication.k8s.io/v1/tokenreviews" || r.Header.Get("Authorization") != "Bearer own-token" {
			http.Error(w, "unexpected request", http.StatusBadRequest)
			return
		}
		var tr tokenReview
		if err := json.NewDecoder(r.Body).Decode(&tr); err != nil || tr.Kind != "TokenReview" {
			http.Error(w, "bad TokenReview", http.StatusBadRequest)
			return
		}
		answer(w, r, &tr)
	}))
	t.Cleanup(api.Close)
	tokenFile := filepath.Join(t.TempDir(), "token")
	if err := os.WriteFile(tokenFile, []byte("own-token\n"), 0o600); err != nil {
		t.Fatal(err)
	}
	return newTokenReviewer(api.URL, tokenFile, api.Client())
}

func TestTokenReviewer(t *testing.T) {
	var calls atomic.Int32
	r := newTokenAPI(t, func(w http.ResponseWriter, _ *http.Request, tr *tokenReview) {
		calls.Add(1)
		s := &tr.Status
		switch tokenSubject(tr.Spec.Token) {
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
	})
	review := func(token string) (string, error) {
		t.Helper()
		return r.review(t.Context(), token, "aud")
	}

	for range 2 {
		if ns, err := review(testToken(t, "good", "aud")); err != nil || ns != "ns" {
			t.Errorf("review of a good token = %q, %v", ns, err)
		}
	}
	if n := calls.Load(); n != 1 {
		t.Errorf("%d reviews of the same token, want 1", n)
	}
	for _, sub := range []string{"bad", "audience-unaware", "user", "bad"} {
		if ns, err := review(testToken(t, sub, []string{"other", "aud"})); !errors.Is(err, errDenied) {
			t.Errorf("review of %q = %q, %v; want it denied", sub, ns, err)
		}
	}
	if n := calls.Load(); n != 4 {
		t.Errorf("%d reviews, want 4, because denials are remembered too", n)
	}
	for range 2 {
		if _, err := review(testToken(t, "broken", "aud")); err == nil || errors.Is(err, errDenied) {
			t.Errorf("review when the API server fails = %v, want an error that isn't a denial", err)
		}
	}
	if n := calls.Load(); n != 6 {
		t.Errorf("%d reviews, want 6, because failures aren't remembered", n)
	}
	if _, err := r.review(t.Context(), testToken(t, "good", []string{"aud", "another audience"}), "another audience"); !errors.Is(err, errDenied) {
		t.Errorf("review for an audience that the API server didn't confirm = %v, want it denied", err)
	}
	if n := calls.Load(); n != 7 {
		t.Errorf("%d reviews, want 7", n)
	}

	t.Log("Tokens that aren't JWTs for the audience are denied without a TokenReview.")
	header, payload := strings.Split(testToken(t, "good", "aud"), ".")[0], strings.Split(testToken(t, "good", "aud"), ".")[1]
	for name, token := range map[string]string{
		"not a JWT":            "good",
		"two parts":            header + "." + payload,
		"four parts":           header + "." + payload + ".sig.more",
		"no header":            "." + payload + ".sig",
		"no signature":         header + "." + payload + ".",
		"payload isn't base64": header + ".!!!.sig",
		"payload isn't JSON":   header + "." + base64.RawURLEncoding.EncodeToString([]byte("aud")) + ".sig",
		"no aud":               header + "." + base64.RawURLEncoding.EncodeToString([]byte(`{"sub":"good"}`)) + ".sig",
		"aud isn't a string":   header + "." + base64.RawURLEncoding.EncodeToString([]byte(`{"aud":7}`)) + ".sig",
		"another audience":     testToken(t, "good", "another audience"),
		"other audiences":      testToken(t, "good", []string{"x", "y"}),
		"null aud":             testToken(t, "good", nil),
		"larger than 16 KiB":   testToken(t, strings.Repeat("x", maxTokenSize), "aud"),
	} {
		if _, err := review(token); !errors.Is(err, errDenied) {
			t.Errorf("review of a token with %s = %v, want it denied", name, err)
		}
	}
	if n := calls.Load(); n != 7 {
		t.Errorf("%d reviews, want still 7", n)
	}
}

func TestReviewCache(t *testing.T) {
	key := func(s string) [sha256.Size]byte { return sha256.Sum256([]byte(s)) }
	has := func(c *reviewCache, k string, now time.Time) bool {
		_, ok := c.get(key(k), now)
		return ok
	}
	t0 := time.Now()
	c := newReviewCache(2, time.Minute)
	c.add(key("a"), review{namespace: "a"}, t0)
	c.add(key("b"), review{namespace: "b"}, t0)
	if r, ok := c.get(key("a"), t0.Add(time.Second)); !ok || r.namespace != "a" {
		t.Errorf("get(a) = %v, %v", r, ok)
	}
	c.add(key("c"), review{namespace: "c"}, t0.Add(2*time.Second))
	if has(c, "b", t0.Add(3*time.Second)) || !has(c, "a", t0.Add(3*time.Second)) || !has(c, "c", t0.Add(3*time.Second)) {
		t.Error("a full cache didn't forget only b, the least recently used review")
	}
	if has(c, "a", t0.Add(time.Minute)) {
		t.Error("the cache returned a review a minute old")
	}

	t.Log("A full cache forgets expired reviews before the least recently used one.")
	c = newReviewCache(2, time.Minute)
	c.add(key("old"), review{}, t0)
	c.add(key("young"), review{}, t0.Add(30*time.Second))
	has(c, "old", t0.Add(59*time.Second))
	c.add(key("new"), review{}, t0.Add(61*time.Second))
	now := t0.Add(62 * time.Second)
	if has(c, "old", now) || !has(c, "young", now) || !has(c, "new", now) {
		t.Error("a full cache didn't forget only old, which had expired")
	}
}

func TestTokenReviewerLimits(t *testing.T) {
	var calls, inFlight atomic.Int32
	release := make(chan struct{})
	r := newTokenAPI(t, func(w http.ResponseWriter, req *http.Request, tr *tokenReview) {
		calls.Add(1)
		inFlight.Add(1)
		defer inFlight.Add(-1)
		s := &tr.Status
		switch sub := tokenSubject(tr.Spec.Token); {
		case strings.HasPrefix(sub, "slow"):
			select {
			case <-release:
			case <-req.Context().Done():
				return
			}
			fallthrough
		case strings.HasPrefix(sub, "good"):
			s.Authenticated, s.User.Username, s.Audiences = true, "system:serviceaccount:ns:"+sub, tr.Spec.Audiences
		default:
			s.Error = "invalid bearer token"
		}
		w.WriteHeader(http.StatusCreated)
		json.NewEncoder(w).Encode(tr)
	})
	releaseAPI := sync.OnceFunc(func() { close(release) })
	t.Cleanup(releaseAPI)
	r.asking = make(chan struct{}, 2)
	r.askWait = 100 * time.Millisecond
	r.denied = newReviewCache(2, 10*time.Second)
	review := func(token string) (string, error) {
		return r.review(t.Context(), token, "aud")
	}
	waitInFlight := func(n int32) {
		t.Helper()
		for deadline := time.Now().Add(time.Minute); inFlight.Load() < n; time.Sleep(time.Millisecond) {
			if time.Now().After(deadline) {
				t.Fatalf("%d TokenReviews in progress, want %d", inFlight.Load(), n)
			}
		}
	}

	t.Log("Reviews of one token share one TokenReview.")
	slow, slow2, good := testToken(t, "slow", "aud"), testToken(t, "slow-2", "aud"), testToken(t, "good", "aud")
	errs := make([]error, 6)
	var wg sync.WaitGroup
	wg.Go(func() { _, errs[0] = review(slow) })
	waitInFlight(1)
	for i := range 5 {
		wg.Go(func() { _, errs[i+1] = review(slow) })
	}
	time.Sleep(50 * time.Millisecond)

	t.Log("A review waits for a free slot, and fails if none frees up.")
	var err2 error
	wg.Go(func() { _, err2 = review(slow2) })
	waitInFlight(2)
	if _, err := review(good); err == nil || errors.Is(err, errDenied) {
		t.Errorf("review while 2 of 2 TokenReviews are in progress = %v, want an error that isn't a denial", err)
	}
	releaseAPI()
	wg.Wait()
	for i, err := range append(errs, err2) {
		if err != nil {
			t.Errorf("review %d of a slow token: %v", i, err)
		}
	}
	if n := calls.Load(); n != 2 {
		t.Errorf("%d TokenReviews for 6 reviews of one token and 1 of another, want 2", n)
	}
	if _, err := review(good); err != nil {
		t.Errorf("review once slots were free: %v", err)
	}

	t.Log("Denials don't push accepted tokens out.")
	for i := range 5 {
		if _, err := review(testToken(t, fmt.Sprint("bad-", i), "aud")); !errors.Is(err, errDenied) {
			t.Errorf("review of bad token %d = %v, want it denied", i, err)
		}
	}
	before := calls.Load()
	for _, token := range []string{slow, slow2, good, testToken(t, "bad-4", "aud")} {
		if _, err := review(token); err != nil && !errors.Is(err, errDenied) {
			t.Errorf("review of %q: %v", tokenSubject(token), err)
		}
	}
	if n := calls.Load() - before; n != 0 {
		t.Errorf("%d TokenReviews for 3 accepted tokens and the latest denied one, want 0", n)
	}
	if _, err := review(testToken(t, "bad-0", "aud")); !errors.Is(err, errDenied) || calls.Load() != before+1 {
		t.Errorf("review of the oldest denied token = %v after %d TokenReviews, want a denial after 1, because the denial cache holds 2", err, calls.Load()-before)
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
		created, err := s.put(t.Context(), key, 40, func(w io.Writer) error {
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

func TestStoreReservesRoom(t *testing.T) {
	newStore := func(t *testing.T) *store {
		t.Helper()
		s, err := openStore(t.TempDir(), 100, newMetrics(), slog.New(slog.DiscardHandler))
		if err != nil {
			t.Fatal(err)
		}
		return s
	}
	write := func(n int) func(io.Writer) error {
		return func(w io.Writer) error {
			_, err := w.Write(bytes.Repeat([]byte("x"), n))
			return err
		}
	}
	exists := func(s *store, key string) bool {
		_, err := os.Stat(s.path(key))
		return err == nil
	}
	// state returns the bytes in a store's files, the room that writes in
	// progress hold, and how many temporary files there are.
	state := func(s *store) (size, reserved int64, temps int) {
		s.mu.Lock()
		size, reserved = s.size, s.reserved
		s.mu.Unlock()
		entries, _ := os.ReadDir(filepath.Join(s.dir, "tmp"))
		return size, reserved, len(entries)
	}
	// slowPut starts a put of n bytes that writes them when finish is
	// called, and returns the put's error.
	slowPut := func(t *testing.T, s *store, key string, n int) (finish func() error) {
		t.Helper()
		started, release, done := make(chan struct{}), make(chan struct{}), make(chan error, 1)
		go func() {
			_, err := s.put(t.Context(), key, int64(n), func(w io.Writer) error {
				close(started)
				<-release
				return write(n)(w)
			})
			done <- err
		}()
		select {
		case <-started:
		case err := <-done:
			t.Fatalf("put of %s: %v", key, err)
		}
		return func() error {
			close(release)
			return <-done
		}
	}

	t.Run("a write holds room for its size until it ends", func(t *testing.T) {
		s := newStore(t)
		if _, err := s.put(t.Context(), "mod/old", 20, write(20)); err != nil {
			t.Fatal(err)
		}
		finish := slowPut(t, s, "mod/slow", 60)
		if _, err := s.put(t.Context(), "mod/big", 50, write(50)); !errors.Is(err, errFull) {
			t.Errorf("put of 50 bytes while a write holds 60 of 100: %v, want errFull", err)
		}
		if !exists(s, "mod/old") {
			t.Error("a put that no eviction could make room for evicted a file")
		}
		if _, err := s.put(t.Context(), "mod/small", 20, write(20)); err != nil {
			t.Errorf("put of 20 bytes that fit beside the write: %v", err)
		}
		if err := finish(); err != nil {
			t.Fatal(err)
		}
		if size, reserved, temps := state(s); size != 100 || reserved != 0 || temps != 0 {
			t.Errorf("after the writes: %d bytes in files, %d reserved, %d temporary files; want 100, 0, 0", size, reserved, temps)
		}
	})

	t.Run("a write that fails gives its room back", func(t *testing.T) {
		s := newStore(t)
		failure := errors.New("the client went away")
		_, err := s.put(t.Context(), "mod/fails", 60, func(w io.Writer) error {
			w.Write([]byte("partial"))
			return failure
		})
		if !errors.Is(err, failure) {
			t.Errorf("put that failed partway: %v, want %v", err, failure)
		}
		if _, err := s.put(t.Context(), "mod/long", 10, write(11)); !errors.Is(err, errOverSize) {
			t.Errorf("put that wrote more than its size: %v, want errOverSize", err)
		}
		if size, reserved, temps := state(s); size != 0 || reserved != 0 || temps != 0 || exists(s, "mod/fails") || exists(s, "mod/long") {
			t.Errorf("after failed writes: %d bytes in files, %d reserved, %d temporary files; want none", size, reserved, temps)
		}
		if _, err := s.put(t.Context(), "mod/all", 100, write(100)); err != nil {
			t.Errorf("put of 100 bytes after the failed writes: %v", err)
		}
	})

	t.Run("a write of unknown size reserves room as it writes", func(t *testing.T) {
		s := newStore(t)
		if _, err := s.put(t.Context(), "mod/old", 50, write(50)); err != nil {
			t.Fatal(err)
		}
		if _, err := s.put(t.Context(), "mod/grows", -1, write(60)); err != nil {
			t.Errorf("put of 60 bytes of unknown size: %v", err)
		}
		if exists(s, "mod/old") || !exists(s, "mod/grows") {
			t.Errorf("after a write of unknown size: old %v, grows %v; want old evicted", exists(s, "mod/old"), exists(s, "mod/grows"))
		}
		_, err := s.put(t.Context(), "mod/huge", -1, func(w io.Writer) error {
			for range 3 {
				if err := write(50)(w); err != nil {
					return err
				}
			}
			return nil
		})
		if !errors.Is(err, errFull) {
			t.Errorf("put of 150 bytes of unknown size: %v, want errFull", err)
		}
		if _, reserved, temps := state(s); reserved != 0 || temps != 0 || exists(s, "mod/huge") {
			t.Errorf("after a write that passed the maximum: %d reserved, %d temporary files, huge %v; want none", reserved, temps, exists(s, "mod/huge"))
		}
	})

	t.Run("writes wait for a slot", func(t *testing.T) {
		s := newStore(t)
		s.writes = make(chan struct{}, 1)
		s.writeWait = 10 * time.Millisecond
		finish := slowPut(t, s, "mod/slow", 10)
		if _, err := s.put(t.Context(), "mod/waits", 10, write(10)); !errors.Is(err, errBusy) {
			t.Errorf("put while another write holds the only slot: %v, want errBusy", err)
		}
		ctx, cancel := context.WithCancel(t.Context())
		cancel()
		if _, err := s.put(ctx, "mod/canceled", 10, write(10)); !errors.Is(err, context.Canceled) {
			t.Errorf("put with a canceled context: %v, want context.Canceled", err)
		}
		if err := finish(); err != nil {
			t.Fatal(err)
		}
		if _, err := s.put(t.Context(), "mod/after", 10, write(10)); err != nil {
			t.Errorf("put after the slot was free: %v", err)
		}
	})

	t.Run("tryPut doesn't wait for a slot", func(t *testing.T) {
		s := newStore(t)
		s.fetches = make(chan struct{}, 1)
		s.fetches <- struct{}{}
		ctx, cancel := context.WithTimeout(t.Context(), 10*time.Second)
		defer cancel()
		if _, err := s.tryPut(ctx, "mod/tries", 10, write(10)); !errors.Is(err, errBusy) {
			t.Errorf("tryPut while another fetch holds the only fetch slot: %v, want errBusy", err)
		}
		<-s.fetches
		s.writes = make(chan struct{}, 1)
		s.writeWait = time.Hour
		finish := slowPut(t, s, "mod/slow", 10)
		if _, err := s.tryPut(ctx, "mod/after", 10, write(10)); err != nil {
			t.Errorf("tryPut while an upload holds every write slot: %v", err)
		}
		if err := finish(); err != nil {
			t.Fatal(err)
		}
	})
}

// TestStoreUnavailable checks that go-cache answers uploads that its store
// can't take with 503.
func TestStoreUnavailable(t *testing.T) {
	rev := fakeReviewer{"writer": {"ns", []string{gocache.WriteAudience("ns", "app")}}}
	full, fullSrv := newTestServer(t, "", rev, func(st *store) { st.max = 100 })
	busy, busySrv := newTestServer(t, "", rev, func(st *store) {
		st.writes = make(chan struct{}, 1)
		st.writes <- struct{}{}
		st.writeWait = time.Millisecond
	})
	output := strings.Repeat("o", 200)
	for _, tc := range []struct {
		result string
		s      *server
		url    string
	}{
		{"full", full, fullSrv.URL},
		{"busy", busy, busySrv.URL},
	} {
		resp, msg := do(t, http.MethodPut, tc.url+gocache.Path("ns", "app")+"/"+id("action"), "writer", strings.NewReader(output), map[string]string{gocache.OutputIDHeader: id(output)})
		if resp.StatusCode != http.StatusServiceUnavailable {
			t.Errorf("PUT to a %s store: %s %q, want 503", tc.result, resp.Status, msg)
		}
		if got := tc.s.metrics.count("PUT " + tc.result); got != 1 {
			t.Errorf("PUT %s requests: %d, want 1", tc.result, got)
		}
	}
}

// TestModulesWhenStoreUnavailable checks that go-cache serves a module file
// that its store can't take from the upstream at once, without keeping it.
func TestModulesWhenStoreUnavailable(t *testing.T) {
	// The file is too large for a server to buffer whole, so go-cache's
	// response has a Content-Length only if go-cache passes on the
	// upstream's.
	mod := bytes.Repeat([]byte("m"), 10000)
	upstream := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		w.Header().Set("Content-Length", strconv.Itoa(len(mod)))
		w.Write(mod)
	}))
	t.Cleanup(upstream.Close)
	full, fullSrv := newTestServer(t, upstream.URL, nil, func(st *store) { st.max = 100 })
	busy, busySrv := newTestServer(t, upstream.URL, nil, func(st *store) {
		st.fetches = make(chan struct{}, 1)
		st.fetches <- struct{}{}
		// A fetch that waited for the slot would outlast the request.
		st.writeWait = time.Hour
	})
	// If a fetch waits for the slot, freeing it lets the server close.
	t.Cleanup(func() { <-busy.store.fetches })
	for _, tc := range []struct {
		result string
		s      *server
		url    string
	}{
		{"full", full, fullSrv.URL},
		{"busy", busy, busySrv.URL},
	} {
		t.Run(tc.result, func(t *testing.T) {
			ctx, cancel := context.WithTimeout(t.Context(), 10*time.Second)
			defer cancel()
			req, err := http.NewRequestWithContext(ctx, http.MethodGet, tc.url+"/mod/example.com/m/@v/v1.0.0.mod", nil)
			if err != nil {
				t.Fatal(err)
			}
			resp, err := http.DefaultClient.Do(req)
			if err != nil {
				t.Fatal(err)
			}
			defer resp.Body.Close()
			body, err := io.ReadAll(resp.Body)
			if resp.StatusCode != http.StatusOK || err != nil || !bytes.Equal(body, mod) {
				t.Errorf("GET: %s, %v; body matches the upstream's: %v", resp.Status, err, bytes.Equal(body, mod))
			}
			if resp.ContentLength != int64(len(mod)) {
				t.Errorf("GET: Content-Length %d, want the upstream's %d", resp.ContentLength, len(mod))
			}
			if files, err := tc.s.store.files(); err != nil || len(files) != 0 {
				t.Errorf("the store holds %d files, %v; want none", len(files), err)
			}
			for result, want := range map[string]int64{tc.result: 1, "fetched": 0, "error": 0} {
				if got := tc.s.metrics.count(result); got != want {
					t.Errorf("%s module requests: %d, want %d", result, got, want)
				}
			}
		})
	}
}

// TestModulesWhileUploadsHoldEverySlot checks that uploads, which wait for
// a write slot and so take each one that frees up, can't keep go-cache from
// keeping the modules that it fetches.
func TestModulesWhileUploadsHoldEverySlot(t *testing.T) {
	mod := bytes.Repeat([]byte("m"), 200)
	upstream := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		w.Write(mod)
	}))
	t.Cleanup(upstream.Close)
	s, srv := newTestServer(t, upstream.URL, nil)
	for range cap(s.store.writes) {
		s.store.writes <- struct{}{}
	}
	resp, err := http.Get(srv.URL + "/mod/example.com/m/@v/v1.0.0.mod")
	if err != nil {
		t.Fatal(err)
	}
	defer resp.Body.Close()
	body, err := io.ReadAll(resp.Body)
	if resp.StatusCode != http.StatusOK || err != nil || !bytes.Equal(body, mod) {
		t.Errorf("GET: %s, %v; body matches the upstream's: %v", resp.Status, err, bytes.Equal(body, mod))
	}
	for result, want := range map[string]int64{"fetched": 1, "busy": 0} {
		if got := s.metrics.count(result); got != want {
			t.Errorf("%s module requests while uploads hold every write slot: %d, want %d", result, got, want)
		}
	}
}

// TestPassThroughCutShort checks that a client can tell when the upstream
// cuts short a module file that go-cache passes through.
func TestPassThroughCutShort(t *testing.T) {
	for name, length := range map[string]string{"with Content-Length": "100000", "chunked": ""} {
		t.Run(name, func(t *testing.T) {
			upstream := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
				if length != "" {
					w.Header().Set("Content-Length", length)
				}
				w.Write(bytes.Repeat([]byte("z"), 50000))
				w.(http.Flusher).Flush()
				panic(http.ErrAbortHandler)
			}))
			t.Cleanup(upstream.Close)
			// No file fits under a maximum of 1 byte, so go-cache passes
			// every one through.
			_, srv := newTestServer(t, upstream.URL, nil, func(st *store) { st.max = 1 })
			resp, err := http.Get(srv.URL + "/mod/example.com/m/@v/v1.0.0.zip")
			if err != nil {
				t.Fatal(err)
			}
			defer resp.Body.Close()
			body, err := io.ReadAll(resp.Body)
			if resp.StatusCode == http.StatusOK && err == nil {
				t.Errorf("GET of a zip that the upstream cut short after 50000 bytes: %s, %d bytes, no error", resp.Status, len(body))
			}
		})
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

package gocache

import (
	"bufio"
	"bytes"
	"context"
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"io"
	"net/http"
	"net/http/httptest"
	"os"
	"os/exec"
	"path/filepath"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"testing"
)

// TestMain runs the test binary as a GOCACHEPROG program for the go command
// in TestGoCommand.
func TestMain(m *testing.M) {
	if dir := os.Getenv("GOCACHE_TEST_DIR"); dir != "" {
		p := &Prog{Dir: dir, Remote: os.Getenv("GOCACHE_TEST_REMOTE"), TokenFile: os.Getenv("GOCACHE_TEST_TOKEN"), Share: os.Getenv("GOCACHE_TEST_SHARE") != "", Log: os.Stderr}
		if err := p.Run(context.Background(), os.Stdin, os.Stdout); err != nil { // pasta:ignore use_t_context — TestMain has no t
			fmt.Fprintln(os.Stderr, err)
			os.Exit(1)
		}
		os.Exit(0)
	}
	os.Exit(m.Run())
}

// remote is a fake go-cache build cache for one repository.
type remote struct {
	t     *testing.T
	token string

	mu      sync.Mutex
	outputs map[string][]byte
	ids     map[string]string
	gets    map[string]int
	puts    int
}

func newRemote(t *testing.T) (*remote, *httptest.Server, string) {
	r := &remote{t: t, token: "token-1", outputs: map[string][]byte{}, ids: map[string]string{}, gets: map[string]int{}}
	srv := httptest.NewServer(r)
	t.Cleanup(srv.Close)
	tokenFile := filepath.Join(t.TempDir(), "token")
	if err := os.WriteFile(tokenFile, []byte(r.token+"\n"), 0o600); err != nil {
		t.Fatal(err)
	}
	return r, srv, tokenFile
}

func (r *remote) add(action string, body []byte) {
	sum := sha256.Sum256(body)
	r.mu.Lock()
	defer r.mu.Unlock()
	r.outputs[action] = body
	r.ids[action] = hex.EncodeToString(sum[:])
}

// tamper replaces the output for action without changing its output ID.
func (r *remote) tamper(action string, body []byte) {
	r.mu.Lock()
	defer r.mu.Unlock()
	r.outputs[action] = body
}

func (r *remote) output(action string) []byte {
	r.mu.Lock()
	defer r.mu.Unlock()
	return r.outputs[action]
}

func (r *remote) stats() (hits, misses, puts int) {
	r.mu.Lock()
	defer r.mu.Unlock()
	return r.gets["hit"], r.gets["miss"], r.puts
}

func (r *remote) ServeHTTP(w http.ResponseWriter, req *http.Request) {
	if req.Header.Get("Authorization") != "Bearer "+r.token {
		http.Error(w, "bad token", http.StatusUnauthorized)
		return
	}
	action := strings.TrimPrefix(req.URL.Path, "/cache/ns/app/")
	r.mu.Lock()
	defer r.mu.Unlock()
	switch req.Method {
	case http.MethodGet:
		body, ok := r.outputs[action]
		if !ok {
			r.gets["miss"]++
			http.NotFound(w, req)
			return
		}
		r.gets["hit"]++
		w.Header().Set(OutputIDHeader, r.ids[action])
		w.Header().Set("Content-Length", strconv.Itoa(len(body)))
		w.Write(body)
	case http.MethodPut:
		r.puts++
		body, err := io.ReadAll(req.Body)
		if err != nil || int64(len(body)) != req.ContentLength {
			http.Error(w, "bad body", http.StatusBadRequest)
			return
		}
		sum := sha256.Sum256(body)
		if id := req.Header.Get(OutputIDHeader); id != hex.EncodeToString(sum[:]) {
			http.Error(w, "output ID doesn't match", http.StatusBadRequest)
			return
		}
		if _, ok := r.outputs[action]; ok {
			w.WriteHeader(http.StatusOK)
			return
		}
		r.outputs[action] = body
		r.ids[action] = hex.EncodeToString(sum[:])
		w.WriteHeader(http.StatusCreated)
	}
}

// client speaks the go command's side of the GOCACHEPROG protocol to a Prog.
type client struct {
	t   *testing.T
	in  *io.PipeWriter
	out *bufio.Scanner
	id  int64
}

func startProg(t *testing.T, p *Prog) *client {
	t.Helper()
	inR, inW := io.Pipe()
	outR, outW := io.Pipe()
	done := make(chan error, 1)
	go func() {
		done <- p.Run(t.Context(), inR, outW)
		outW.Close()
	}()
	t.Cleanup(func() {
		inW.Close()
		if err := <-done; err != nil {
			t.Errorf("Run: %v", err)
		}
	})
	c := &client{t: t, in: inW, out: bufio.NewScanner(outR)}
	c.out.Buffer(nil, 1<<20)
	if res := c.read(); res.ID != 0 || strings.Join(res.KnownCommands, ",") != "get,put,close" {
		t.Fatalf("first response = %+v, want the known commands", res)
	}
	return c
}

func (c *client) read() response {
	c.t.Helper()
	if !c.out.Scan() {
		c.t.Fatalf("reading a response: %v", c.out.Err())
	}
	var res response
	if err := json.Unmarshal(c.out.Bytes(), &res); err != nil {
		c.t.Fatal(err)
	}
	return res
}

func (c *client) send(req request, body []byte) response {
	c.t.Helper()
	c.id++
	req.ID = c.id
	b, _ := json.Marshal(req)
	b = append(b, '\n')
	if req.BodySize > 0 {
		enc, _ := json.Marshal(body)
		b = append(append(b, enc...), '\n')
	}
	if _, err := c.in.Write(b); err != nil {
		c.t.Fatal(err)
	}
	res := c.read()
	if res.ID != req.ID {
		c.t.Fatalf("response %d to request %d", res.ID, req.ID)
	}
	return res
}

func (c *client) get(action string) response {
	a, _ := hex.DecodeString(action)
	return c.send(request{Command: "get", ActionID: a}, nil)
}

func (c *client) put(action string, body []byte) response {
	a, _ := hex.DecodeString(action)
	sum := sha256.Sum256(body)
	return c.send(request{Command: "put", ActionID: a, OutputID: sum[:], BodySize: int64(len(body))}, body)
}

func id(s string) string {
	sum := sha256.Sum256([]byte(s))
	return hex.EncodeToString(sum[:])
}

func TestProgStoresOutputs(t *testing.T) {
	dir := t.TempDir()
	c := startProg(t, &Prog{Dir: dir, Share: true})
	if res := c.get(id("a")); !res.Miss {
		t.Fatalf("get from an empty cache = %+v, want a miss", res)
	}
	for _, body := range [][]byte{[]byte("compiled a"), {}} {
		action := id(fmt.Sprintf("action %q", body))
		res := c.put(action, body)
		if res.Err != "" || res.DiskPath == "" {
			t.Fatalf("put = %+v", res)
		}
		if got, err := os.ReadFile(res.DiskPath); err != nil || !bytes.Equal(got, body) {
			t.Fatalf("DiskPath holds %q, %v; want %q", got, err, body)
		}
		hit := c.get(action)
		sum := sha256.Sum256(body)
		if hit.Miss || hit.DiskPath != res.DiskPath || hit.Size != int64(len(body)) || !bytes.Equal(hit.OutputID, sum[:]) || hit.Time == nil {
			t.Errorf("get after put = %+v", hit)
		}
		if _, err := os.Stat(filepath.Join(dir, "p", action)); err != nil {
			t.Errorf("put didn't record that the go command built %s: %v", action, err)
		}
	}

	t.Log("A put whose output ID doesn't match its body fails.")
	a, _ := hex.DecodeString(id("bad"))
	wrong := sha256.Sum256([]byte("something else"))
	if res := c.send(request{Command: "put", ActionID: a, OutputID: wrong[:], BodySize: 3}, []byte("abc")); res.Err == "" {
		t.Errorf("put with the wrong output ID = %+v, want an error", res)
	}
	if res := c.send(request{Command: "close"}, nil); res.Err != "" {
		t.Errorf("close = %+v", res)
	}

	t.Log("Without Share, put records nothing for Upload to send.")
	local := t.TempDir()
	c = startProg(t, &Prog{Dir: local})
	if res := c.put(id("local"), []byte("compiled in the test container")); res.Err != "" || res.DiskPath == "" {
		t.Fatalf("put = %+v", res)
	}
	if _, err := os.Stat(filepath.Join(local, "p", id("local"))); err == nil {
		t.Error("put recorded an output for Upload without Share")
	}
}

func TestProgReadsRemote(t *testing.T) {
	r, srv, tokenFile := newRemote(t)
	r.add(id("built"), []byte("compiled elsewhere"))
	r.add(id("corrupt"), []byte("original"))
	r.tamper(id("corrupt"), []byte("tampered"))
	dir := t.TempDir()
	c := startProg(t, &Prog{Dir: dir, Remote: srv.URL + Path("ns", "app"), TokenFile: tokenFile, Share: true})

	res := c.get(id("built"))
	if res.Miss {
		t.Fatal("get missed an output that the remote has")
	}
	if got, err := os.ReadFile(res.DiskPath); err != nil || string(got) != "compiled elsewhere" {
		t.Errorf("DiskPath holds %q, %v", got, err)
	}
	if _, err := os.Stat(filepath.Join(dir, "p", id("built"))); err == nil {
		t.Error("Prog recorded an output from the remote as built here, so Upload would send it back")
	}
	if res := c.get(id("built")); res.Miss {
		t.Errorf("second get = %+v, want a local hit", res)
	}
	if hits, _, _ := r.stats(); hits != 1 {
		t.Errorf("%d remote hits, want 1", hits)
	}
	if res := c.get(id("absent")); !res.Miss {
		t.Errorf("get of an absent output = %+v, want a miss", res)
	}
	if res := c.get(id("corrupt")); !res.Miss {
		t.Errorf("get of an output that doesn't match its ID = %+v, want a miss", res)
	}

	t.Log("Prog stops using a remote that sent a corrupt output.")
	if res := c.get(id("built-2")); !res.Miss {
		t.Errorf("get = %+v, want a miss", res)
	}
	if _, misses, _ := r.stats(); misses != 1 {
		t.Errorf("%d remote misses, want 1", misses)
	}
}

func TestProgStopsUsingABrokenRemote(t *testing.T) {
	var requests atomic.Int32
	srv := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		requests.Add(1)
		http.Error(w, "no", http.StatusForbidden)
	}))
	defer srv.Close()
	tokenFile := filepath.Join(t.TempDir(), "token")
	os.WriteFile(tokenFile, []byte("x"), 0o600)
	var log bytes.Buffer
	c := startProg(t, &Prog{Dir: t.TempDir(), Remote: srv.URL, TokenFile: tokenFile, Log: &log})
	for _, a := range []string{"a", "b", "c"} {
		if res := c.get(id(a)); !res.Miss {
			t.Fatalf("get = %+v, want a miss", res)
		}
	}
	if n := requests.Load(); n != 1 || !strings.Contains(log.String(), "403 Forbidden: no") {
		t.Errorf("%d requests, log %q; want 1 request and its error logged", n, log.String())
	}
}

func TestUpload(t *testing.T) {
	r, srv, tokenFile := newRemote(t)
	r.add(id("from remote"), []byte("compiled elsewhere"))
	r.add(id("both"), []byte("same output"))
	dir := t.TempDir()
	remoteURL := srv.URL + Path("ns", "app")
	c := startProg(t, &Prog{Dir: dir, Remote: remoteURL, TokenFile: tokenFile, Share: true})
	c.get(id("from remote"))
	for action, body := range map[string]string{"new": "compiled here", "empty": "", "both": "same output"} {
		if res := c.put(id(action), []byte(body)); res.Err != "" {
			t.Fatal(res.Err)
		}
	}

	stored, had, err := Upload(t.Context(), srv.Client(), dir, remoteURL, tokenFile)
	if err != nil || stored != 2 || had != 1 {
		t.Fatalf("Upload = %d stored, %d had, %v; want 2 and 1", stored, had, err)
	}
	if _, _, puts := r.stats(); puts != 3 {
		t.Errorf("%d PUT requests; Upload must send only what the go command built", puts)
	}
	if got := r.output(id("empty")); got == nil || len(got) != 0 {
		t.Errorf("remote has %q for the empty output", got)
	}

	t.Log("Upload reports failures.")
	os.WriteFile(tokenFile, []byte("wrong"), 0o600)
	if _, _, err := Upload(t.Context(), srv.Client(), dir, remoteURL, tokenFile); err == nil || !strings.Contains(err.Error(), "3 of 3 uploads failed") {
		t.Errorf("Upload with a bad token = %v", err)
	}
}

func TestParseIndex(t *testing.T) {
	good := id("x") + " 12\n"
	if out, size, err := parseIndex([]byte(good)); err != nil || out != id("x") || size != 12 {
		t.Errorf("parseIndex(%q) = %q, %d, %v", good, out, size, err)
	}
	for _, bad := range []string{"", "abc 1", id("x") + " -1", id("x") + " 1 2", strings.ToUpper(id("x")) + " 1", "../../etc 1"} {
		if _, _, err := parseIndex([]byte(bad)); err == nil {
			t.Errorf("parseIndex(%q) succeeded", bad)
		}
	}
}

// TestGoCommand builds a module with the go command and Prog twice, with an
// empty local directory each time. The second build reads every output
// that the first one uploaded.
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
		os.MkdirAll(filepath.Join(mod, filepath.Dir(name)), 0o755)
		if err := os.WriteFile(filepath.Join(mod, name), []byte(src), 0o644); err != nil {
			t.Fatal(err)
		}
	}
	r, srv, tokenFile := newRemote(t)
	remoteURL := srv.URL + Path("ns", "app")
	home := t.TempDir()
	build := func(dir string) string {
		t.Helper()
		cmd := exec.Command(gobin, "list", "-export", "-f={{.Export}}", "./...")
		cmd.Dir = mod
		cmd.Env = append(os.Environ(),
			"HOME="+home, "GOENV=off", "GOFLAGS=", "GOPATH="+filepath.Join(home, "go"), "GOCACHE="+filepath.Join(home, "go-build"),
			"GOTOOLCHAIN=local", "GOPROXY=off", "CGO_ENABLED=0", "GOCACHEPROG="+self,
			"GOCACHE_TEST_DIR="+dir, "GOCACHE_TEST_REMOTE="+remoteURL, "GOCACHE_TEST_TOKEN="+tokenFile, "GOCACHE_TEST_SHARE=1")
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
	stored, had, err := Upload(t.Context(), nil, first, remoteURL, tokenFile)
	if err != nil || stored == 0 || had != 0 {
		t.Fatalf("Upload = %d stored, %d had, %v", stored, had, err)
	}

	second := t.TempDir()
	out := build(second)
	for _, export := range strings.Fields(out) {
		if !strings.HasPrefix(export, filepath.Join(second, "o")+string(filepath.Separator)) {
			t.Errorf("export data %s isn't from the second build's cache directory", export)
		}
	}
	built, err := os.ReadDir(filepath.Join(second, "p"))
	if hits, _, _ := r.stats(); err != nil || len(built) != 0 || hits < 2 {
		t.Errorf("the second build compiled %d outputs (%v) and read %d from the remote; want 0 compiled", len(built), err, hits)
	}
}

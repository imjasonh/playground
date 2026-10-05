package e2e_test

import (
	"context"
	"crypto/sha256"
	"crypto/tls"
	"crypto/x509"
	"encoding/base64"
	"encoding/hex"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"net"
	"net/http"
	"net/http/httptest"
	"net/http/httputil"
	"net/url"
	"os"
	"path/filepath"
	"slices"
	"strings"
	"sync"
	"syscall"
	"testing"
	"time"

	"github.com/imjasonh/playground/kube"
	"github.com/imjasonh/playground/kube/internal/client"
	"github.com/imjasonh/playground/kube/internal/e2e"
	"github.com/imjasonh/playground/kube/internal/image/imagetest"
	"github.com/imjasonh/playground/kube/internal/yaml"
)

type idleConfigMaps struct{}

func (idleConfigMaps) Reconcile(context.Context, *ConfigMapMeta) error { return nil }

// Report holds the results that clients post to a kube.Serve handler.
type Report struct {
	kube.Object `kube:"group=e2e.kube.imjasonh.github.io"`
	Status      struct {
		Results    []string         `json:"results,omitempty"`
		Conditions []kube.Condition `json:"conditions,omitempty"`
	} `json:"status,omitzero"`
}

// reports hands the results that its handler receives to its reconcile,
// which writes them to the Report's status.
type reports struct {
	// wait is how long the handler waits for the status to show a result.
	wait time.Duration
	// broken names a Report whose reconciles fail before they write.
	broken string
	// gate, if set, can stop reconciles before they read the pending
	// results.
	gate *gate
	// triggered, if set, receives each result once its handler has
	// triggered a reconcile.
	triggered chan string

	mu      sync.Mutex
	pending map[kube.Key][]string
	// fail is how many more reconciles that read a pending result fail
	// before they write it, and failed counts them.
	fail, failed int
	// reads counts the reconciles that read each pending result.
	reads map[string]int
}

func (h *reports) readCount(result string) int {
	h.mu.Lock()
	defer h.mu.Unlock()
	return h.reads[result]
}

// gate stops reconciles while it's shut, and gives the test a channel for
// each stopped reconcile that lets it continue.
type gate struct {
	mu      sync.Mutex
	shut    bool
	stopped chan chan struct{}
}

func newGate() *gate { return &gate{stopped: make(chan chan struct{})} }

func (g *gate) wait(ctx context.Context) {
	if g == nil {
		return
	}
	g.mu.Lock()
	shut := g.shut
	g.mu.Unlock()
	if !shut {
		return
	}
	resume := make(chan struct{})
	select {
	case g.stopped <- resume:
	case <-ctx.Done():
		return
	}
	select {
	case <-resume:
	case <-ctx.Done():
	}
}

func (g *gate) set(shut bool) {
	g.mu.Lock()
	defer g.mu.Unlock()
	g.shut = shut
}

// next waits for a reconcile to stop at the gate and returns the channel
// that lets it continue when closed.
func (g *gate) next(t *testing.T) chan struct{} {
	t.Helper()
	select {
	case resume := <-g.stopped:
		return resume
	case <-time.After(30 * time.Second):
		t.Fatal("no reconcile stopped at the gate within 30s")
		return nil
	}
}

// watchHold proxies requests to the API server and can hold back the events
// of the open watches of one resource, so that a manager's caches fall
// behind the API server. Watches that start during a hold aren't held.
type watchHold struct {
	resource string

	mu   sync.Mutex
	open map[*heldBody]bool
	// held is closed when the hold ends, and nil when there's no hold.
	held chan struct{}
}

// newWatchHold starts a proxy that sends an administrator's requests to the
// API server, and returns a kubeconfig file that points to it.
func newWatchHold(t *testing.T, resource string) (*watchHold, string) {
	t.Helper()
	admin, err := os.ReadFile(e2e.Env(t).Kubeconfig)
	if err != nil {
		t.Fatal(err)
	}
	var kc struct {
		Clusters []struct {
			Cluster struct {
				Server string `json:"server"`
				CA     string `json:"certificate-authority-data"`
			} `json:"cluster"`
		} `json:"clusters"`
		Users []struct {
			User struct {
				Token string `json:"token"`
			} `json:"user"`
		} `json:"users"`
	}
	if err := yaml.Unmarshal(admin, &kc); err != nil {
		t.Fatal(err)
	}
	target, err := url.Parse(kc.Clusters[0].Cluster.Server)
	if err != nil {
		t.Fatal(err)
	}
	ca, err := base64.StdEncoding.DecodeString(kc.Clusters[0].Cluster.CA)
	if err != nil {
		t.Fatal(err)
	}
	roots := x509.NewCertPool()
	roots.AppendCertsFromPEM(ca)
	w := &watchHold{resource: resource, open: map[*heldBody]bool{}}
	proxy := &httputil.ReverseProxy{
		Rewrite:   func(r *httputil.ProxyRequest) { r.SetURL(target) },
		Transport: &http.Transport{TLSClientConfig: &tls.Config{RootCAs: roots, MinVersion: tls.VersionTLS12}, ForceAttemptHTTP2: true},
		ModifyResponse: func(resp *http.Response) error {
			if req := resp.Request; req.URL.Query().Get("watch") != "" && strings.HasSuffix(req.URL.Path, "/"+w.resource) {
				b := &heldBody{ReadCloser: resp.Body, w: w, ctx: req.Context()}
				w.mu.Lock()
				w.open[b] = true
				w.mu.Unlock()
				resp.Body = b
			}
			return nil
		},
	}
	srv := httptest.NewServer(proxy)
	t.Cleanup(srv.Close)
	t.Cleanup(w.release)
	path := filepath.Join(t.TempDir(), "kubeconfig")
	body := fmt.Sprintf(`apiVersion: v1
kind: Config
current-context: proxy
clusters:
- name: proxy
  cluster:
    server: %s
contexts:
- name: proxy
  context:
    cluster: proxy
    user: admin
users:
- name: admin
  user:
    token: %s
`, srv.URL, kc.Users[0].User.Token)
	if err := os.WriteFile(path, []byte(body), 0o600); err != nil {
		t.Fatal(err)
	}
	return w, path
}

// hold holds back the events of the open watches that arrive from now until
// release.
func (w *watchHold) hold() {
	w.mu.Lock()
	defer w.mu.Unlock()
	if w.held == nil {
		w.held = make(chan struct{})
	}
	for b := range w.open {
		b.held = w.held
	}
}

// release delivers the held events, and those that arrive later.
func (w *watchHold) release() {
	w.mu.Lock()
	defer w.mu.Unlock()
	if w.held != nil {
		close(w.held)
		w.held = nil
	}
	for b := range w.open {
		b.held = nil
	}
}

type heldBody struct {
	io.ReadCloser
	w   *watchHold
	ctx context.Context
	// held is the watchHold's channel while this watch is held, and nil
	// otherwise. The watchHold's mutex guards it.
	held chan struct{}
}

func (b *heldBody) Read(p []byte) (int, error) {
	n, err := b.ReadCloser.Read(p)
	b.w.mu.Lock()
	held := b.held
	b.w.mu.Unlock()
	if held != nil {
		select {
		case <-held:
		case <-b.ctx.Done():
		}
	}
	return n, err
}

func (b *heldBody) Close() error {
	b.w.mu.Lock()
	delete(b.w.open, b)
	b.w.mu.Unlock()
	return b.ReadCloser.Close()
}

func (h *reports) ServeHTTP(w http.ResponseWriter, r *http.Request) {
	ns, name := r.PathValue("namespace"), r.PathValue("name")
	b, _ := io.ReadAll(r.Body)
	result, key := string(b), kube.Key{Namespace: ns, Name: name}
	h.mu.Lock()
	h.pending[key] = append(h.pending[key], result)
	h.mu.Unlock()
	defer func() {
		h.mu.Lock()
		defer h.mu.Unlock()
		if i := slices.Index(h.pending[key], result); i >= 0 {
			h.pending[key] = slices.Delete(h.pending[key], i, i+1)
		}
		if len(h.pending[key]) == 0 {
			delete(h.pending, key)
		}
	}()
	unavailable := func() {
		w.Header().Set("Connection", "close")
		http.Error(w, "try again", http.StatusServiceUnavailable)
	}
	if !kube.Trigger[Report](r.Context(), ns, name) {
		unavailable()
		return
	}
	if h.triggered != nil {
		h.triggered <- result
	}
	deadline := time.Now().Add(h.wait)
	for {
		if rep := kube.Get[Report](r.Context(), ns, name); rep != nil && slices.Contains(rep.Status.Results, result) {
			return
		}
		if time.Now().After(deadline) {
			unavailable()
			return
		}
		time.Sleep(50 * time.Millisecond)
	}
}

// read waits at the gate and then returns the results pending for rep and
// whether the reconcile fails before it writes them. It waits right before
// it reads the results so that TestServeHandOffWhileTheCacheLags catches a
// reconcile that reads the object with Get first.
func (h *reports) read(ctx context.Context, rep *Report) (results []string, fail bool) {
	h.gate.wait(ctx)
	h.mu.Lock()
	defer h.mu.Unlock()
	results = slices.Clone(h.pending[kube.Key{Namespace: rep.Namespace, Name: rep.Name}])
	if h.reads == nil {
		h.reads = map[string]int{}
	}
	for _, result := range results {
		h.reads[result]++
	}
	fail = rep.Name == h.broken || len(results) > 0 && h.fail > 0
	if fail && rep.Name != h.broken {
		h.fail--
		h.failed++
	}
	return results, fail
}

func (h *reports) Reconcile(ctx context.Context, rep *Report) error {
	results, fail := h.read(ctx, rep)
	if fail {
		return errors.New("the results store is down")
	}
	cur := kube.Get[Report](ctx, rep.Namespace, rep.Name)
	if cur == nil {
		return nil
	}
	rep.Status.Results = cur.Status.Results
	for _, result := range results {
		if !slices.Contains(rep.Status.Results, result) {
			rep.Status.Results = append(rep.Status.Results, result)
		}
	}
	return nil
}

// TestServeHandsDataToReconcile posts results to a kube.Serve handler that
// hands them to the reconcile, which writes them to a Report's status. The
// handler answers only once Get shows the result in the status, and the
// reconcile doesn't remove the result that it reads, so a result survives a
// reconcile that fails after reading it. A result that the reconcile never
// writes gets a 503, and a later reconcile keeps the results in the status.
func TestServeHandsDataToReconcile(t *testing.T) {
	c := e2e.Client(t)
	ns := e2e.Namespace(t, c)
	h := &reports{wait: 2 * time.Second, broken: "broken", pending: map[kube.Key][]string{}}
	mux := http.NewServeMux()
	mux.Handle("POST /reports/{namespace}/{name}", h)
	m := &kube.Manager{Name: "reports-e2e", Namespace: ns, ServeAddr: freeAddr(t)}
	e2e.Run(t, m, kube.For[Report](h, kube.Named("reports")), kube.Serve(mux))
	for _, name := range []string{"ok", "broken"} {
		e2e.Eventually(t, 30*time.Second, func() error {
			return c.Create(t.Context(), client.Path(group+"/v1", "reports", ns, ""), map[string]any{
				"apiVersion": group + "/v1", "kind": "Report", "metadata": map[string]any{"name": name},
			}, nil)
		})
	}
	report := func(name string) *Report {
		t.Helper()
		var rep Report
		if err := e2e.Get(t.Context(), c, client.Path(group+"/v1", "reports", ns, name), &rep); err != nil {
			t.Fatal(err)
		}
		return &rep
	}
	e2e.Eventually(t, 30*time.Second, func() error {
		if conds := report("ok").Status.Conditions; len(conds) == 0 {
			return errors.New("the Report hasn't been reconciled")
		}
		return nil
	})
	post := func(name, result string) (int, bool) {
		t.Helper()
		resp, err := http.Post("http://"+m.ServeAddr+"/reports/"+ns+"/"+name, "text/plain", strings.NewReader(result))
		if err != nil {
			t.Fatal(err)
		}
		resp.Body.Close()
		return resp.StatusCode, resp.Close
	}

	h.mu.Lock()
	h.fail = 1
	h.mu.Unlock()
	if code, _ := post("ok", "passed"); code != http.StatusOK {
		t.Fatalf("POST passed = %d, want 200", code)
	}
	if got := report("ok").Status.Results; !slices.Equal(got, []string{"passed"}) {
		t.Errorf("results after a 200 = %q, want the posted result", got)
	}
	h.mu.Lock()
	failed := h.failed
	h.mu.Unlock()
	if failed != 1 {
		t.Errorf("%d reconciles failed after reading the result, want 1, whose retry found the result", failed)
	}

	start := time.Now()
	if code, closed := post("broken", "lost"); code != http.StatusServiceUnavailable || !closed {
		t.Errorf("POST to a Report whose reconcile fails = %d, closed %v; want 503 with Connection: close", code, closed)
	}
	if d := time.Since(start); d < h.wait {
		t.Errorf("the handler answered 503 after %v, before the status could show the result", d)
	}
	if got := report("broken").Status.Results; len(got) != 0 {
		t.Errorf("results of a Report whose reconcile fails = %q", got)
	}

	if code, _ := post("ok", "again"); code != http.StatusOK {
		t.Fatalf("POST again = %d, want 200", code)
	}
	if got := report("ok").Status.Results; !slices.Equal(got, []string{"passed", "again"}) {
		t.Errorf("results = %q, want both, though passed was no longer pending", got)
	}
	h.mu.Lock()
	defer h.mu.Unlock()
	if len(h.pending) != 0 {
		t.Errorf("pending = %q after the handlers answered", h.pending)
	}
}

// createReport creates a Report and waits until a controller has written its
// status.
func createReport(t *testing.T, c *client.Client, ns, name string) {
	t.Helper()
	createReportWith(t, c, ns, map[string]any{"name": name})
}

// createReportWith creates a Report with the given metadata, which must
// include its name, and waits until a controller has written its status.
func createReportWith(t *testing.T, c *client.Client, ns string, meta map[string]any) {
	t.Helper()
	name := meta["name"].(string)
	e2e.Eventually(t, 30*time.Second, func() error {
		return c.Create(t.Context(), client.Path(group+"/v1", "reports", ns, ""), map[string]any{
			"apiVersion": group + "/v1", "kind": "Report", "metadata": meta,
		}, nil)
	})
	e2e.Eventually(t, 30*time.Second, func() error {
		var rep Report
		if err := e2e.Get(t.Context(), c, client.Path(group+"/v1", "reports", ns, name), &rep); err != nil {
			return err
		}
		if len(rep.Status.Conditions) == 0 {
			return fmt.Errorf("report %s hasn't been reconciled", name)
		}
		return nil
	})
}

// posts sends results to a reports handler in the background.
type posts struct {
	t     *testing.T
	codes map[string]chan int
}

func (p *posts) send(addr, ns, name, result string) {
	code := make(chan int, 1)
	p.codes[result] = code
	go func() {
		resp, err := http.Post("http://"+addr+"/reports/"+ns+"/"+name, "text/plain", strings.NewReader(result))
		if err != nil {
			p.t.Error(err)
			code <- 0
			return
		}
		resp.Body.Close()
		code <- resp.StatusCode
	}()
}

// answer waits for the response to the post of result.
func (p *posts) answer(result string) int {
	p.t.Helper()
	select {
	case code := <-p.codes[result]:
		return code
	case <-time.After(time.Minute):
		p.t.Fatalf("no answer to the post of %q within a minute", result)
		return 0
	}
}

// history records each version of a Report's results that the API server
// stores, through a watch of its own.
type history struct {
	t    *testing.T
	c    *client.Client
	path string

	mu       sync.Mutex
	versions []reportVersion
}

type reportVersion struct {
	rv      string
	results []string
}

func watchHistory(t *testing.T, c *client.Client, ns, name string) *history {
	t.Helper()
	ctx, cancel := context.WithCancel(t.Context())
	w, err := c.Watch(ctx, client.Path(group+"/v1", "reports", ns, ""), url.Values{"fieldSelector": {"metadata.name=" + name}}, "")
	if err != nil {
		cancel()
		t.Fatal(err)
	}
	h := &history{t: t, c: c, path: client.Path(group+"/v1", "reports", ns, name)}
	done := make(chan struct{})
	go func() {
		defer close(done)
		for {
			e, err := w.Next()
			if err != nil {
				return
			}
			var rep Report
			if e.Type == client.Bookmark || json.Unmarshal(e.Object, &rep) != nil {
				continue
			}
			h.mu.Lock()
			h.versions = append(h.versions, reportVersion{rep.ResourceVersion, rep.Status.Results})
			h.mu.Unlock()
		}
	}()
	t.Cleanup(func() {
		cancel()
		w.Close()
		<-done
	})
	return h
}

// holds reports whether any version held result.
func (h *history) holds(result string) bool {
	h.mu.Lock()
	defer h.mu.Unlock()
	for _, v := range h.versions {
		if slices.Contains(v.results, result) {
			return true
		}
	}
	return false
}

// check waits until the history reaches the stored version, and fails the
// test if a version removed a result that an earlier version held. Every
// handler answers 200 only once the status holds its result, so a result
// that disappears is one that a client was told was saved.
func (h *history) check() []string {
	h.t.Helper()
	var rep Report
	if err := e2e.Get(h.t.Context(), h.c, h.path, &rep); err != nil {
		h.t.Fatal(err)
	}
	var versions []reportVersion
	e2e.Eventually(h.t, 30*time.Second, func() error {
		h.mu.Lock()
		versions = slices.Clone(h.versions)
		h.mu.Unlock()
		if len(versions) == 0 || versions[len(versions)-1].rv != rep.ResourceVersion {
			return fmt.Errorf("the watch hasn't delivered resource version %s", rep.ResourceVersion)
		}
		return nil
	})
	for i, v := range versions {
		for _, later := range versions[i+1:] {
			for _, result := range v.results {
				if !slices.Contains(later.results, result) {
					h.t.Errorf("resource version %s has results %q, without %q, which version %s held", later.rv, later.results, result, v.rv)
					return rep.Status.Results
				}
			}
		}
	}
	return rep.Status.Results
}

// waitTriggered waits until the handler for result has triggered a reconcile.
func waitTriggered(t *testing.T, h *reports, result string) {
	t.Helper()
	select {
	case got := <-h.triggered:
		if got != result {
			t.Fatalf("the handler for %q triggered a reconcile, want %q", got, result)
		}
	case <-time.After(30 * time.Second):
		t.Fatalf("the handler for %q didn't trigger a reconcile within 30s", result)
	}
}

// TestServeHandOffWhileTheCacheLags holds back a manager's watch of Reports.
// A result that arrives during a reconcile triggers another, which starts
// right after the first one writes the status, with the object from before
// that write. It stops right before it reads the pending results, and
// meanwhile the handlers see the write, answer, and drop their results. A
// reconcile that added the results still pending to the object that it
// received, or to an object that it read with Get before it stopped, would
// write back the old list without the results that were confirmed. So the
// reconcile reads the pending results first, and then the object with Get.
func TestServeHandOffWhileTheCacheLags(t *testing.T) {
	c := e2e.Client(t)
	ns := e2e.Namespace(t, c)
	watches, kubeconfig := newWatchHold(t, "reports")
	h := &reports{wait: time.Minute, gate: newGate(), triggered: make(chan string, 8), pending: map[kube.Key][]string{}}
	mux := http.NewServeMux()
	mux.Handle("POST /reports/{namespace}/{name}", h)
	m := &kube.Manager{Name: "reports-lag-e2e", Kubeconfig: kubeconfig, Namespace: ns, ServeAddr: freeAddr(t)}
	e2e.Run(t, m, kube.For[Report](h, kube.Named("reports")), kube.Serve(mux))
	createReport(t, c, ns, "lag")
	versions := watchHistory(t, c, ns, "lag")
	p := &posts{t: t, codes: map[string]chan int{}}

	h.gate.set(true)
	p.send(m.ServeAddr, ns, "lag", "a")
	waitTriggered(t, h, "a")
	first := h.gate.next(t)
	p.send(m.ServeAddr, ns, "lag", "b")
	waitTriggered(t, h, "b")

	t.Log("The first reconcile writes a and b, and the next one starts before the watch delivers the write.")
	watches.hold()
	close(first)
	second := h.gate.next(t)

	t.Log("While the next reconcile waits to read the pending results, the handlers see the write and drop a and b.")
	watches.release()
	for _, result := range []string{"a", "b"} {
		if code := p.answer(result); code != http.StatusOK {
			t.Fatalf("POST %s = %d, want 200", result, code)
		}
	}

	t.Log("The second reconcile writes c, which arrived after the handlers dropped a and b.")
	p.send(m.ServeAddr, ns, "lag", "c")
	waitTriggered(t, h, "c")
	h.gate.set(false)
	close(second)
	if code := p.answer("c"); code != http.StatusOK {
		t.Fatalf("POST c = %d, want 200", code)
	}
	got := versions.check()
	for _, result := range []string{"a", "b", "c"} {
		if !slices.Contains(got, result) {
			t.Errorf("POST %s got 200, but the results are %q", result, got)
		}
	}
}

// TestServeListenFailure runs a manager, without leader election, whose
// kube.Serve address is in use. Run must return the error instead of
// stopping as if its context had ended.
func TestServeListenFailure(t *testing.T) {
	ln, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	defer ln.Close()
	m := &kube.Manager{Name: "serve-listen-e2e", Kubeconfig: e2e.Env(t).Kubeconfig, Logger: e2e.Logger(t), ServeAddr: ln.Addr().String()}
	ctx, cancel := context.WithTimeout(t.Context(), 30*time.Second)
	defer cancel()
	err = m.Run(ctx, kube.For[ConfigMapMeta](idleConfigMaps{}, kube.Named("serve-listen")), kube.Serve(http.NotFoundHandler()))
	if !errors.Is(err, syscall.EADDRINUSE) {
		t.Errorf("Run = %v, want an error that the address is in use", err)
	}
	if ctx.Err() != nil {
		t.Errorf("Run returned only once its context ended: %v", ctx.Err())
	}
}

// TestRequestToken runs a manager as a service account that may request
// tokens for itself, with a token directory that holds a token for one
// audience, as a projected volume does. RequestToken returns that token,
// and asks the API server for a token for any other audience.
func TestRequestToken(t *testing.T) {
	c := e2e.Client(t)
	ns := e2e.Namespace(t, c)
	for _, obj := range []map[string]any{
		{"apiVersion": "v1", "kind": "ServiceAccount", "metadata": map[string]any{"name": "prog"}},
		{
			"apiVersion": "rbac.authorization.k8s.io/v1", "kind": "Role", "metadata": map[string]any{"name": "prog"},
			"rules": []any{map[string]any{"apiGroups": []string{""}, "resources": []string{"serviceaccounts/token"}, "resourceNames": []string{"prog"}, "verbs": []string{"create"}}},
		},
		{
			"apiVersion": "rbac.authorization.k8s.io/v1", "kind": "RoleBinding", "metadata": map[string]any{"name": "prog"},
			"roleRef":  map[string]any{"apiGroup": "rbac.authorization.k8s.io", "kind": "Role", "name": "prog"},
			"subjects": []any{map[string]any{"kind": "ServiceAccount", "name": "prog", "namespace": ns}},
		},
	} {
		if err := c.Create(t.Context(), client.Path(obj["apiVersion"].(string), strings.ToLower(obj["kind"].(string))+"s", ns, ""), obj, nil); err != nil {
			t.Fatal(err)
		}
	}
	dir := t.TempDir()
	mounted := serviceAccountToken(t, c, ns, "prog", "mounted")
	sum := sha256.Sum256([]byte("mounted"))
	if err := os.WriteFile(filepath.Join(dir, hex.EncodeToString(sum[:])), []byte(mounted), 0o600); err != nil {
		t.Fatal(err)
	}
	m := &kube.Manager{
		Name: "request-token-e2e", Kubeconfig: serviceAccountKubeconfig(t, c, ns, "prog"), Logger: e2e.Logger(t),
		ServeAddr: freeAddr(t), TokenDir: dir,
	}
	ctx, cancel := context.WithCancel(t.Context())
	done := make(chan error, 1)
	go func() {
		done <- m.Run(ctx, kube.Serve(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
			token, expires, err := kube.RequestToken(r.Context(), r.URL.Query().Get("audience"))
			if err != nil {
				http.Error(w, err.Error(), http.StatusInternalServerError)
				return
			}
			fmt.Fprintf(w, "%s %d", token, expires.Unix())
		})))
	}()
	t.Cleanup(func() {
		cancel()
		if err := <-done; err != nil {
			t.Errorf("Run = %v", err)
		}
	})
	request := func(audience string) (string, time.Time) {
		t.Helper()
		var token string
		var expires int64
		e2e.Eventually(t, 30*time.Second, func() error {
			resp, err := http.Get("http://" + m.ServeAddr + "/?audience=" + url.QueryEscape(audience))
			if err != nil {
				return err
			}
			defer resp.Body.Close()
			b, _ := io.ReadAll(resp.Body)
			if resp.StatusCode != http.StatusOK {
				return fmt.Errorf("RequestToken(%q): %s: %s", audience, resp.Status, b)
			}
			_, err = fmt.Sscanf(string(b), "%s %d", &token, &expires)
			return err
		})
		return token, time.Unix(expires, 0)
	}

	if token, _ := request("mounted"); token != mounted {
		t.Errorf("RequestToken(mounted) = %q, want the token in the directory", token)
	}
	token, expires := request("other")
	if token == mounted || time.Until(expires) < 50*time.Minute {
		t.Errorf("RequestToken(other) = %q, which expires at %v, want a new token for about an hour", token, expires)
	}
	var review struct {
		Status kube.TokenReview `json:"status"`
	}
	if err := c.Create(t.Context(), client.Path("authentication.k8s.io/v1", "tokenreviews", "", ""), map[string]any{
		"apiVersion": "authentication.k8s.io/v1", "kind": "TokenReview",
		"spec": map[string]any{"token": token, "audiences": []string{"other"}},
	}, &review); err != nil {
		t.Fatal(err)
	}
	if r := review.Status; !r.Authenticated || r.User.Username != "system:serviceaccount:"+ns+":prog" || !slices.Equal(r.Audiences, []string{"other"}) {
		t.Errorf("TokenReview of the requested token = %+v", r)
	}
}

// TestGenerateProbe installs the probe example, which sends tokens for its
// own service account, reviews its callers' tokens, and triggers reconciles
// from its kube.Serve handler. It runs two replicas of the image's program
// with the generated RBAC rules and a token directory, and the API server
// issues and reviews the tokens.
func TestGenerateProbe(t *testing.T) {
	c := e2e.Client(t)
	reg := imagetest.Registry(t)
	imagetest.Base(t, reg+"/chainguard/static:latest", "linux/amd64")
	in := generateExample(t, reg, "examples/probe", "probe")
	byKind := map[string]string{}
	for _, obj := range in.objects {
		b, _ := json.Marshal(obj)
		byKind[obj["kind"].(string)] = string(b)
	}
	for kind, want := range map[string]string{
		"ClusterRole": `{"apiGroups":["authentication.k8s.io"],"resources":["tokenreviews"],"verbs":["create"]}`,
		"Service":     `{"name":"serve","port":80,"targetPort":"serve"}`,
		"Deployment":  `"lifecycle":{"preStop":{"sleep":{"seconds":5}}}`,
	} {
		if !strings.Contains(byKind[kind], want) {
			t.Errorf("%s = %s, want %s", kind, byKind[kind], want)
		}
	}
	for _, kind := range []string{"ClusterRole", "Role"} {
		if strings.Contains(byKind[kind], "serviceaccounts") {
			t.Errorf("the %s lets the program request tokens, though its token's audience is a constant: %s", kind, byKind[kind])
		}
	}
	if !slices.Contains(in.args, "-serve-addr=:8081") || !slices.Contains(in.args, "-leader-elect") || !slices.Contains(in.args, "-token-dir=/var/run/secrets/tokens") {
		t.Errorf("args = %q", in.args)
	}
	if len(in.tokens) != 1 || in.tokens[0].Audience != "probe" {
		t.Errorf("projected tokens = %+v, want one for the audience probe", in.tokens)
	}
	in.apply(t, c)
	exe := in.executable(t, "probe")
	kubeconfig := serviceAccountKubeconfig(t, c, "probe", "probe")
	var addrs []string
	var outs []*syncBuffer
	for range 2 {
		r := in
		r.serveAddr = freeAddr(t)
		outs = append(outs, r.runInstalled(t, exe, kubeconfig))
		addrs = append(addrs, r.serveAddr)
	}

	ns := e2e.Namespace(t, c)
	if err := c.Create(t.Context(), client.Path("v1", "serviceaccounts", ns, ""), map[string]any{
		"apiVersion": "v1", "kind": "ServiceAccount", "metadata": map[string]any{"name": "ci"},
	}, nil); err != nil {
		t.Fatal(err)
	}
	token := func(audiences ...string) string {
		t.Helper()
		return serviceAccountToken(t, c, ns, "ci", audiences...)
	}
	type response struct {
		code  int
		body  string
		close bool
	}
	call := func(method, addr, path, token string) response {
		t.Helper()
		req, err := http.NewRequestWithContext(t.Context(), method, "http://"+addr+path, nil)
		if err != nil {
			t.Fatal(err)
		}
		req.Header.Set("Authorization", "Bearer "+token)
		resp, err := http.DefaultClient.Do(req)
		if err != nil {
			t.Fatal(err)
		}
		defer resp.Body.Close()
		b, _ := io.ReadAll(resp.Body)
		return response{resp.StatusCode, string(b), resp.Close}
	}

	t.Log("Every replica serves, and accepts only tokens for its audience.")
	ci := token("probe")
	for _, addr := range addrs {
		if r := call(http.MethodGet, addr, "/whoami", ci); r.code != http.StatusOK || r.body != "system:serviceaccount:"+ns+":ci\n" {
			t.Errorf("GET /whoami on %s = %+v", addr, r)
		}
	}
	for name, tok := range map[string]string{"another audience": token("other"), "the API server's audience": token()} {
		if r := call(http.MethodGet, addrs[0], "/whoami", tok); r.code != http.StatusUnauthorized {
			t.Errorf("GET /whoami with a token for %s = %+v, want 401", name, r)
		}
	}

	t.Log("A probe of the program's own API sends a token that the program requested.")
	probe := client.Path("examples.kube.imjasonh.github.io/v1", "probes", ns, "self")
	e2e.Eventually(t, time.Minute, func() error {
		// The replica that holds the lease creates the CRD.
		return c.Create(t.Context(), client.Path("examples.kube.imjasonh.github.io/v1", "probes", ns, ""), map[string]any{
			"apiVersion": "examples.kube.imjasonh.github.io/v1", "kind": "Probe",
			"metadata": map[string]any{"name": "self"},
			"spec":     map[string]any{"url": "http://" + addrs[0] + "/whoami"},
		}, nil)
	})
	var p struct {
		Status struct {
			Code      int       `json:"code"`
			Message   string    `json:"message"`
			CheckedAt time.Time `json:"checkedAt"`
		} `json:"status"`
	}
	e2e.Eventually(t, 30*time.Second, func() error {
		if err := e2e.Get(t.Context(), c, probe, &p); err != nil {
			return err
		}
		if p.Status.Code != http.StatusOK || p.Status.Message != "system:serviceaccount:probe:probe" {
			return fmt.Errorf("status = %+v", p.Status)
		}
		return nil
	})
	checked := p.Status.CheckedAt
	e2e.Never(t, 2*time.Second, func() error {
		if err := e2e.Get(t.Context(), c, probe, &p); err != nil {
			return err
		}
		if !p.Status.CheckedAt.Equal(checked) {
			return fmt.Errorf("the probe ran again at %v without a trigger", p.Status.CheckedAt)
		}
		return nil
	})

	t.Log("The replica that holds the lease triggers a check, and the other refuses.")
	var leader string
	e2e.Eventually(t, 30*time.Second, func() error {
		leader = ""
		var got []response
		for _, addr := range addrs {
			r := call(http.MethodPost, addr, "/probes/"+ns+"/self", ci)
			got = append(got, r)
			switch {
			case r.code == http.StatusAccepted && leader == "":
				leader = addr
			case r.code != http.StatusServiceUnavailable || !r.close:
				return fmt.Errorf("responses = %+v, want 202 from one replica and 503 with Connection: close from the other", got)
			}
		}
		if leader == "" {
			return fmt.Errorf("responses = %+v, want 202 from one replica", got)
		}
		return nil
	})
	e2e.Eventually(t, 30*time.Second, func() error {
		if err := e2e.Get(t.Context(), c, probe, &p); err != nil {
			return err
		}
		if !p.Status.CheckedAt.After(checked) {
			return fmt.Errorf("checkedAt = %v, want a check after %v", p.Status.CheckedAt, checked)
		}
		return nil
	})
	for _, addr := range addrs {
		if r := call(http.MethodPost, addr, "/probes/"+ns+"/missing", ci); r.code != http.StatusNotFound {
			t.Errorf("POST for a missing probe on %s = %+v, want 404", addr, r)
		}
	}
	if r := call(http.MethodPost, leader, "/probes/default/self", ci); r.code != http.StatusForbidden {
		t.Errorf("POST for a probe in another namespace = %+v, want 403", r)
	}
	for _, out := range outs {
		noPermissionErrors(t, out)
	}
}

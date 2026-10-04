package e2e_test

import (
	"context"
	"crypto/tls"
	"crypto/x509"
	"fmt"
	"io"
	"net/http"
	"net/http/httptest"
	"net/http/httputil"
	"net/url"
	"os"
	"path/filepath"
	"slices"
	"strconv"
	"strings"
	"sync"
	"testing"
	"time"

	"github.com/imjasonh/playground/kube"
	"github.com/imjasonh/playground/kube/internal/client"
	"github.com/imjasonh/playground/kube/internal/e2e"
	"github.com/imjasonh/playground/kube/internal/yaml"
	"github.com/imjasonh/playground/kube/k8s"
)

// stepper moves a Widget's status.size one step toward its spec.size in each
// reconcile, and records the size that each reconcile read. While a Widget
// has a size, it owns a ConfigMap.
type stepper struct {
	mu    sync.Mutex
	reads map[string][]int
}

func (s *stepper) Reconcile(ctx context.Context, w *Widget) error {
	key := w.Namespace + "/" + w.Name
	s.mu.Lock()
	if s.reads == nil {
		s.reads = map[string][]int{}
	}
	s.reads[key] = append(s.reads[key], w.Status.Size)
	s.mu.Unlock()
	if w.Spec.Size > 0 {
		kube.Own(ctx, &k8s.ConfigMap{Object: kube.Meta(w.Name, nil)})
	}
	switch {
	case w.Status.Size < w.Spec.Size:
		w.Status.Size++
	case w.Status.Size > w.Spec.Size:
		w.Status.Size--
	default:
		return nil
	}
	kube.RequeueAfter(ctx, time.Nanosecond)
	return nil
}

func (s *stepper) read(key string) []int {
	s.mu.Lock()
	defer s.mu.Unlock()
	return slices.Clone(s.reads[key])
}

// stepped reports whether reads go from one size to another one step at a
// time. Reconciles that change nothing can read the first or the last size
// more than once.
func stepped(reads []int, from, to int) bool {
	for len(reads) > 1 && reads[0] == from && reads[1] == from {
		reads = reads[1:]
	}
	for len(reads) > 1 && reads[len(reads)-1] == to && reads[len(reads)-2] == to {
		reads = reads[:len(reads)-1]
	}
	step := 1
	if to < from {
		step = -1
	}
	if len(reads) != (to-from)*step+1 {
		return false
	}
	for i, v := range reads {
		if v != from+i*step {
			return false
		}
	}
	return true
}

// runs describes reads as runs of one size, such as "0×3 1 2×2".
func runs(reads []int) string {
	var parts []string
	for len(reads) > 0 {
		n := 1
		for n < len(reads) && reads[n] == reads[0] {
			n++
		}
		part := strconv.Itoa(reads[0])
		if n > 1 {
			part += "×" + strconv.Itoa(n)
		}
		parts = append(parts, part)
		reads = reads[n:]
	}
	return strings.Join(parts, " ")
}

// laggingKubeconfig writes an administrator's kubeconfig for a proxy to the
// API server that holds back what watches send by at least lag.
func laggingKubeconfig(t *testing.T, lag time.Duration) string {
	t.Helper()
	admin, err := os.ReadFile(e2e.Env(t).Kubeconfig)
	if err != nil {
		t.Fatal(err)
	}
	var kc struct {
		Clusters []struct {
			Cluster struct {
				Server string `json:"server"`
				CA     []byte `json:"certificate-authority-data"`
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
	server, err := url.Parse(kc.Clusters[0].Cluster.Server)
	if err != nil {
		t.Fatal(err)
	}
	roots := x509.NewCertPool()
	roots.AppendCertsFromPEM(kc.Clusters[0].Cluster.CA)
	proxy := httputil.NewSingleHostReverseProxy(server)
	proxy.Transport = &http.Transport{TLSClientConfig: &tls.Config{RootCAs: roots, MinVersion: tls.VersionTLS12}}
	proxy.ModifyResponse = func(resp *http.Response) error {
		if resp.Request.URL.Query().Get("watch") == "1" {
			resp.Body = lagging{resp.Body, lag}
		}
		return nil
	}
	srv := httptest.NewServer(proxy)
	t.Cleanup(srv.Close)
	path := filepath.Join(t.TempDir(), "kubeconfig")
	body := fmt.Sprintf(`apiVersion: v1
kind: Config
current-context: lagging
clusters:
- name: lagging
  cluster:
    server: %s
contexts:
- name: lagging
  context:
    cluster: lagging
    user: admin
users:
- name: admin
  user:
    token: %s
`, srv.URL, kc.Users[0].User.Token)
	if err := os.WriteFile(path, []byte(body), 0o600); err != nil {
		t.Fatal(err)
	}
	return path
}

// lagging holds back each read of a response body by lag.
type lagging struct {
	io.ReadCloser
	lag time.Duration
}

func (l lagging) Read(p []byte) (int, error) {
	n, err := l.ReadCloser.Read(p)
	time.Sleep(l.lag)
	return n, err
}

// The controller watches through a proxy that holds back watch events, so
// each reconcile runs right after the previous one writes and before the
// watch delivers that write.
func TestReconcileSeesItsOwnWrites(t *testing.T) {
	c := e2e.Client(t)
	addr := freeAddr(t)
	ns := e2e.Namespace(t, c)
	r := &stepper{}
	m := &kube.Manager{Name: "writes-e2e", Kubeconfig: laggingKubeconfig(t, 200*time.Millisecond), Namespace: ns, Addr: addr}
	e2e.Run(t, m, kube.For[Widget](r, kube.Named("stepper")))
	const size = 10
	settle := func(want int) {
		t.Helper()
		e2e.Eventually(t, 20*time.Second, func() error {
			w, err := widget(t, c, ns, "w")
			if err != nil {
				return err
			}
			if w.Status.Size != want {
				return fmt.Errorf("status.size = %d, want %d", w.Status.Size, want)
			}
			return nil
		})
		time.Sleep(time.Second)
	}

	createWidget(t, c, ns, "w", size)
	settle(size)
	up := r.read(ns + "/w")
	if !stepped(up, 0, size) {
		t.Errorf("reconciles read sizes %s, want them to step from 0 to %d", runs(up), size)
	}

	t.Log("Shrinking the widget to 0 steps it back down, and deletes its ConfigMap once.")
	if err := c.Patch(t.Context(), client.Path(group+"/v1", "widgets", ns, "w"), client.MergePatch, nil, []byte(`{"spec":{"size":0}}`), nil); err != nil {
		t.Fatal(err)
	}
	settle(0)
	if down := r.read(ns + "/w")[len(up):]; !stepped(down, size, 0) {
		t.Errorf("reconciles read sizes %s, want them to step from %d to 0", runs(down), size)
	}
	for sample, want := range map[string]float64{
		`kube_status_writes_total{controller="stepper"}`:          2 * size,
		`kube_apply_total{controller="stepper",result="applied"}`: 1,
		`kube_delete_total{controller="stepper"}`:                 1,
	} {
		if got := scrape(t, addr, sample); got != want {
			t.Errorf("%s = %v, want %v", sample, got, want)
		}
	}
	if err := e2e.Gone(t.Context(), c, client.Path("v1", "configmaps", ns, "w")); err != nil {
		t.Error(err)
	}
}

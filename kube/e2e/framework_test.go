// Package e2e_test tests framework behavior against a real API server.
// The tests skip unless $KUBEBUILDER_ASSETS is set.
package e2e_test

import (
	"bufio"
	"context"
	"errors"
	"fmt"
	"net"
	"net/http"
	"strconv"
	"strings"
	"sync"
	"testing"
	"time"

	"github.com/imjasonh/playground/kube"
	"github.com/imjasonh/playground/kube/internal/client"
	"github.com/imjasonh/playground/kube/internal/e2e"
	"github.com/imjasonh/playground/kube/k8s"
)

func TestMain(m *testing.M) { e2e.Main(m) }

const group = "e2e.kube.imjasonh.github.io"

type Widget struct {
	kube.Object `kube:"group=e2e.kube.imjasonh.github.io"`
	Spec        struct {
		Size int `json:"size"`
	} `json:"spec"`
	Status struct {
		Size       int              `json:"size,omitempty"`
		Conditions []kube.Condition `json:"conditions,omitempty"`
	} `json:"status,omitzero"`
}

// counter reconciles Widgets into ConfigMaps and counts calls.
type counter struct {
	mu        sync.Mutex
	calls     map[string]int
	panicOn   string
	permanent string
}

func (c *counter) Reconcile(ctx context.Context, w *Widget) error {
	c.mu.Lock()
	if c.calls == nil {
		c.calls = map[string]int{}
	}
	c.calls[w.Namespace+"/"+w.Name]++
	c.mu.Unlock()
	switch w.Name {
	case c.panicOn:
		panic("widget exploded")
	case c.permanent:
		return kube.Permanent(errors.New("widgets can't be that size"))
	}
	kube.Own(ctx, &k8s.ConfigMap{Object: kube.Meta(w.Name, nil), Data: map[string]string{"size": strconv.Itoa(w.Spec.Size)}})
	w.Status.Size = w.Spec.Size
	return nil
}

func (c *counter) count(key string) int {
	c.mu.Lock()
	defer c.mu.Unlock()
	return c.calls[key]
}

func createWidget(t *testing.T, c *client.Client, ns, name string, size int) {
	t.Helper()
	e2e.Eventually(t, 30*time.Second, func() error {
		return c.Create(t.Context(), client.Path(group+"/v1", "widgets", ns, ""), map[string]any{
			"apiVersion": group + "/v1", "kind": "Widget", "metadata": map[string]any{"name": name}, "spec": map[string]any{"size": size},
		}, nil)
	})
}

func widget(t *testing.T, c *client.Client, ns, name string) (*Widget, error) {
	var w Widget
	return &w, e2e.Get(t.Context(), c, client.Path(group+"/v1", "widgets", ns, name), &w)
}

func freeAddr(t *testing.T) string {
	t.Helper()
	ln, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	defer ln.Close()
	return ln.Addr().String()
}

// scrape returns the value of one metric sample from /metrics, or 0.
func scrape(t *testing.T, addr, sample string) float64 {
	t.Helper()
	v, err := tryScrape(addr, sample)
	if err != nil {
		t.Fatal(err)
	}
	return v
}

func tryScrape(addr, sample string) (float64, error) {
	resp, err := http.Get("http://" + addr + "/metrics")
	if err != nil {
		return 0, err
	}
	defer resp.Body.Close()
	s := bufio.NewScanner(resp.Body)
	for s.Scan() {
		if v, ok := strings.CutPrefix(s.Text(), sample+" "); ok {
			f, _ := strconv.ParseFloat(v, 64)
			return f, nil
		}
	}
	return 0, nil
}

func TestSteadyStateMakesNoWrites(t *testing.T) {
	c := e2e.Client(t)
	addr := freeAddr(t)
	r := &counter{}
	e2e.Run(t, &kube.Manager{Name: "steady-e2e", Addr: addr}, kube.For[Widget](r, kube.Named("steady")))
	ns := e2e.Namespace(t, c)
	createWidget(t, c, ns, "w", 3)
	e2e.Eventually(t, 10*time.Second, func() error {
		w, err := widget(t, c, ns, "w")
		if err != nil {
			return err
		}
		if w.Status.Size != 3 {
			return fmt.Errorf("status.size = %d", w.Status.Size)
		}
		return e2e.Get(t.Context(), c, client.Path("v1", "configmaps", ns, "w"), &k8s.ConfigMap{})
	})
	applied := `kube_apply_total{controller="steady",result="applied"}`
	skipped := `kube_apply_total{controller="steady",result="skipped"}`
	statuses := `kube_status_writes_total{controller="steady"}`
	time.Sleep(time.Second)
	baseApplied, baseStatuses, baseCalls := scrape(t, addr, applied), scrape(t, addr, statuses), r.count(ns+"/w")
	if baseApplied != 1 {
		t.Errorf("applies to converge = %v, want 1", baseApplied)
	}
	if baseCalls > 3 {
		t.Errorf("reconciled %d times to converge; the controller's own writes shouldn't cause a loop", baseCalls)
	}

	t.Log("Each label change reconciles again, but finds nothing to write.")
	for i := range 5 {
		patch := fmt.Sprintf(`{"metadata":{"labels":{"touch":"%d"}}}`, i)
		if err := c.Patch(t.Context(), client.Path(group+"/v1", "widgets", ns, "w"), client.MergePatch, nil, []byte(patch), nil); err != nil {
			t.Fatal(err)
		}
		e2e.Eventually(t, 5*time.Second, func() error {
			if got := r.count(ns + "/w"); got < baseCalls+i+1 {
				return fmt.Errorf("reconciles = %d", got)
			}
			return nil
		})
	}
	time.Sleep(500 * time.Millisecond)
	if got := scrape(t, addr, applied); got != baseApplied {
		t.Errorf("applies = %v after no-op reconciles, want %v", got, baseApplied)
	}
	if got := scrape(t, addr, skipped); got < 5 {
		t.Errorf("skipped applies = %v, want at least 5", got)
	}
	if got := scrape(t, addr, statuses); got != baseStatuses {
		t.Errorf("status writes = %v after no-op reconciles, want %v", got, baseStatuses)
	}
	resp, err := http.Get("http://" + addr + "/readyz")
	if err != nil || resp.StatusCode != http.StatusOK {
		t.Errorf("/readyz = %v, %v", resp, err)
	}
}

func TestRestartMakesNoWrites(t *testing.T) {
	c := e2e.Client(t)
	env := e2e.Env(t)
	ns := e2e.Namespace(t, c)
	run := func(r *counter) (addr string, stop func()) {
		addr = freeAddr(t)
		ctx, cancel := context.WithCancelCause(t.Context())
		done := make(chan error, 1)
		m := &kube.Manager{Name: "restart-e2e", Kubeconfig: env.Kubeconfig, Namespace: ns, Addr: addr, Logger: e2e.Logger(t)}
		go func() { done <- m.Run(ctx, kube.For[Widget](r, kube.Named("restart"))) }()
		return addr, func() {
			// Like signal.NotifyContext, which kube.Main uses, stop with
			// a cause; stopping is still not a failure.
			cancel(errors.New("terminated signal received"))
			if err := <-done; err != nil {
				t.Errorf("manager: %v", err)
			}
		}
	}

	_, stop := run(&counter{})
	createWidget(t, c, ns, "w", 3)
	e2e.Eventually(t, 10*time.Second, func() error {
		w, err := widget(t, c, ns, "w")
		if err != nil {
			return err
		}
		if w.Status.Size != 3 {
			return fmt.Errorf("status.size = %d", w.Status.Size)
		}
		return e2e.Get(t.Context(), c, client.Path("v1", "configmaps", ns, "w"), &k8s.ConfigMap{})
	})
	stop()

	t.Log("A new manager finds the ConfigMap and status already right, and writes nothing.")
	r := &counter{}
	addr, stop := run(r)
	defer stop()
	e2e.Eventually(t, 10*time.Second, func() error {
		if r.count(ns+"/w") == 0 {
			return errors.New("the new manager hasn't reconciled the widget")
		}
		return nil
	})
	time.Sleep(500 * time.Millisecond)
	if got := scrape(t, addr, `kube_apply_total{controller="restart",result="applied"}`); got != 0 {
		t.Errorf("applies after restart = %v, want 0", got)
	}
	if got := scrape(t, addr, `kube_apply_total{controller="restart",result="skipped"}`); got < 1 {
		t.Errorf("skipped applies after restart = %v, want at least 1", got)
	}
	if got := scrape(t, addr, `kube_status_writes_total{controller="restart"}`); got != 0 {
		t.Errorf("status writes after restart = %v, want 0", got)
	}
}

func TestRestoresStatusThatSomeoneElseChanged(t *testing.T) {
	c := e2e.Client(t)
	r := &counter{}
	e2e.Run(t, &kube.Manager{Name: "status-e2e"}, kube.For[Widget](r, kube.Named("status")))
	ns := e2e.Namespace(t, c)
	createWidget(t, c, ns, "w", 3)
	size := func(want int) func() error {
		return func() error {
			w, err := widget(t, c, ns, "w")
			if err != nil {
				return err
			}
			if w.Status.Size != want {
				return fmt.Errorf("status.size = %d, want %d", w.Status.Size, want)
			}
			return nil
		}
	}
	e2e.Eventually(t, 10*time.Second, size(3))
	time.Sleep(500 * time.Millisecond)
	before := r.count(ns + "/w")

	t.Log("Another client overwrites the status, and the controller writes it back.")
	patch := []byte(`{"status":{"size":7}}`)
	if err := c.Patch(t.Context(), client.Path(group+"/v1", "widgets", ns, "w", "status"), client.MergePatch, map[string][]string{"fieldManager": {"someone-else"}}, patch, nil); err != nil {
		t.Fatal(err)
	}
	e2e.Eventually(t, 10*time.Second, size(3))
	time.Sleep(500 * time.Millisecond)
	// One reconcile for the other client's change. The controller's own
	// status write is ignored, unless its watch event arrives before the
	// write's response, which costs one more.
	if got := r.count(ns + "/w"); got-before > 2 {
		t.Errorf("reconciled %d times to restore the status, want at most 2", got-before)
	}
}

func TestPanicsAndPermanentErrorsAreContained(t *testing.T) {
	c := e2e.Client(t)
	r := &counter{panicOn: "explodes", permanent: "invalid"}
	e2e.Run(t, &kube.Manager{Name: "errors-e2e", DisableStreamingLists: true}, kube.For[Widget](r, kube.Named("errors")))
	ns := e2e.Namespace(t, c)
	createWidget(t, c, ns, "explodes", 1)
	createWidget(t, c, ns, "invalid", 1)
	createWidget(t, c, ns, "fine", 1)

	synced := func(name, status, reason, message string) error {
		w, err := widget(t, c, ns, name)
		if err != nil {
			return err
		}
		s := kube.FindCondition(w.Status.Conditions, "Synced")
		if s == nil || s.Status != status || s.Reason != reason || !strings.Contains(s.Message, message) {
			return fmt.Errorf("%s: Synced = %+v", name, s)
		}
		return nil
	}
	e2e.Eventually(t, 10*time.Second, func() error {
		if err := synced("explodes", kube.False, "ReconcileError", "panic: widget exploded"); err != nil {
			return err
		}
		if err := synced("invalid", kube.False, "PermanentError", "can't be that size"); err != nil {
			return err
		}
		return synced("fine", kube.True, "Reconciled", "")
	})

	t.Log("The panicking object is retried with backoff; the invalid one waits for a change.")
	time.Sleep(2 * time.Second)
	if n := r.count(ns + "/explodes"); n < 3 {
		t.Errorf("panicking widget reconciled %d times in 2s, want retries", n)
	}
	if n := r.count(ns + "/invalid"); n != 1 {
		t.Errorf("invalid widget reconciled %d times, want 1", n)
	}
	if err := c.Patch(t.Context(), client.Path(group+"/v1", "widgets", ns, "invalid"), client.MergePatch, nil, []byte(`{"spec":{"size":2}}`), nil); err != nil {
		t.Fatal(err)
	}
	e2e.Eventually(t, 5*time.Second, func() error {
		if n := r.count(ns + "/invalid"); n != 2 {
			return fmt.Errorf("invalid widget reconciled %d times after a change, want 2", n)
		}
		return nil
	})
}

func TestLeaderElectionFailover(t *testing.T) {
	c := e2e.Client(t)
	env := e2e.Env(t)
	ns := e2e.Namespace(t, c)
	type replica struct {
		r      *counter
		cancel context.CancelFunc
		done   chan error
	}
	start := func() *replica {
		rep := &replica{r: &counter{}, done: make(chan error, 1)}
		ctx, cancel := context.WithCancel(t.Context())
		rep.cancel = cancel
		m := &kube.Manager{Name: "leader-e2e", Kubeconfig: env.Kubeconfig, Namespace: ns, LeaderElection: true, LeaseNamespace: ns, Logger: e2e.Logger(t)}
		go func() { rep.done <- m.Run(ctx, kube.For[Widget](rep.r, kube.Named("leader"))) }()
		return rep
	}
	a, b := start(), start()
	defer func() {
		for _, rep := range []*replica{a, b} {
			rep.cancel()
			select {
			case <-rep.done:
			case <-time.After(30 * time.Second):
				t.Error("replica didn't stop")
			}
		}
	}()

	createWidget(t, c, ns, "first", 1)
	var leader, standby *replica
	e2e.Eventually(t, 20*time.Second, func() error {
		switch na, nb := a.r.count(ns+"/first"), b.r.count(ns+"/first"); {
		case na > 0 && nb == 0:
			leader, standby = a, b
		case nb > 0 && na == 0:
			leader, standby = b, a
		default:
			return fmt.Errorf("reconciles: a=%d b=%d, want exactly one replica", na, nb)
		}
		return nil
	})

	t.Log("When the leader stops, it releases the lease and the standby takes over.")
	stopped := time.Now()
	leader.cancel()
	if err := <-leader.done; err != nil {
		t.Errorf("leader stopped with %v", err)
	}
	leader.done <- nil
	createWidget(t, c, ns, "second", 1)
	e2e.Eventually(t, 20*time.Second, func() error {
		if n := standby.r.count(ns + "/second"); n == 0 {
			return errors.New("standby hasn't reconciled")
		}
		return nil
	})
	t.Logf("failover took %v", time.Since(stopped).Round(100*time.Millisecond))
	if leader.r.count(ns+"/second") != 0 {
		t.Error("stopped leader reconciled")
	}
}

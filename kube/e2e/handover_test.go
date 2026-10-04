package e2e_test

import (
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"net/http"
	"slices"
	"sync"
	"testing"
	"time"

	"github.com/imjasonh/playground/kube"
	"github.com/imjasonh/playground/kube/internal/client"
	"github.com/imjasonh/playground/kube/internal/e2e"
	"github.com/imjasonh/playground/kube/k8s"
)

// replica is one of the managers that reconcile Reports and serve the
// reports handler, with leader election or shards.
type replica struct {
	h    *reports
	m    *kube.Manager
	stop func()
}

func startReplica(t *testing.T, ns, kubeconfig string, shards int) *replica {
	t.Helper()
	h := &reports{wait: time.Minute, triggered: make(chan string, 64), pending: map[kube.Key][]string{}}
	mux := http.NewServeMux()
	mux.Handle("POST /reports/{namespace}/{name}", h)
	mux.HandleFunc("GET /reports/{namespace}/{name}", showResults)
	m := &kube.Manager{Name: "reports-handover-e2e", Kubeconfig: kubeconfig, Namespace: ns, LeaseNamespace: ns, Addr: freeAddr(t), ServeAddr: freeAddr(t), Logger: e2e.Logger(t)}
	if shards > 1 {
		m.Shards = shards
	} else {
		m.LeaderElection = true
	}
	ctx, cancel := context.WithCancel(t.Context())
	done := make(chan error, 1)
	go func() { done <- m.Run(ctx, kube.For[Report](h, kube.Named("reports")), kube.Serve(mux)) }()
	var once sync.Once
	stop := func() {
		once.Do(func() {
			cancel()
			select {
			case err := <-done:
				if err != nil {
					t.Errorf("manager: %v", err)
				}
			case <-time.After(30 * time.Second):
				t.Error("manager didn't stop within 30s")
			}
		})
	}
	t.Cleanup(stop)
	return &replica{h: h, m: m, stop: stop}
}

// showResults answers with the results of a Report as Get shows them.
func showResults(w http.ResponseWriter, r *http.Request) {
	rep := kube.Get[Report](r.Context(), r.PathValue("namespace"), r.PathValue("name"))
	if rep == nil {
		http.NotFound(w, r)
		return
	}
	_ = json.NewEncoder(w).Encode(rep.Status.Results)
}

// waitHeld waits until ok accepts the number of shards that each replica
// holds.
func waitHeld(t *testing.T, ok func(held []int) bool, replicas ...*replica) {
	t.Helper()
	e2e.Eventually(t, 60*time.Second, func() error {
		held := make([]int, len(replicas))
		for i, r := range replicas {
			n, err := tryScrape(r.m.Addr, "kube_shards_held")
			if err != nil {
				return err
			}
			held[i] = int(n)
		}
		if !ok(held) {
			return fmt.Errorf("the replicas hold %v shards", held)
		}
		return nil
	})
}

// trigger posts result until the handler triggers a reconcile with it,
// posting again after each 503.
func (p *posts) trigger(h *reports, addr, ns, name, result string) {
	p.t.Helper()
	deadline := time.After(30 * time.Second)
	for {
		p.send(addr, ns, name, result)
		select {
		case got := <-h.triggered:
			if got != result {
				p.t.Fatalf("the handler for %q triggered a reconcile, want %q", got, result)
			}
			return
		case code := <-p.codes[result]:
			if code != http.StatusServiceUnavailable {
				p.t.Fatalf("POST %s = %d before it triggered a reconcile", result, code)
			}
			time.Sleep(100 * time.Millisecond)
		case <-deadline:
			p.t.Fatalf("POST %s didn't trigger a reconcile within 30s", result)
		}
	}
}

// waitWriteTried waits until a replica has tried to write result: its
// reconcile read the result again after a failed write, or the API server
// stored it.
func waitWriteTried(t *testing.T, r *replica, versions *history, result string) {
	t.Helper()
	e2e.Eventually(t, 30*time.Second, func() error {
		if r.h.readCount(result) >= 2 || versions.holds(result) {
			return nil
		}
		return fmt.Errorf("the replica hasn't tried to write %q", result)
	})
}

// TestServeHandOverWithAStaleCache moves a Report's shard to a replica
// whose cache doesn't have the previous holder's last status write. The new
// holder's first status write requires the cached resource version, so it
// fails instead of replacing the results with a list that lacks a result
// that a client was told was saved, and succeeds once the cache catches up.
// The replica counts the failed reconcile as stale, not as an error.
func TestServeHandOverWithAStaleCache(t *testing.T) {
	c := e2e.Client(t)
	ns := e2e.Namespace(t, c)
	const shards = 32
	watches, kubeconfig := newWatchHold(t, "reports")
	a := startReplica(t, ns, e2e.Env(t).Kubeconfig, shards)
	waitHeld(t, func(n []int) bool { return n[0] == shards }, a)
	b := startReplica(t, ns, kubeconfig, shards)
	waitHeld(t, func(n []int) bool { return n[0] > 0 && n[1] > 0 && n[0]+n[1] == shards }, a, b)

	t.Log("Find a Report in a shard that the first replica holds.")
	p := &posts{t: t, codes: map[string]chan int{}}
	name, created := "", 0
	for ; name == "" && created < shards; created++ {
		n := fmt.Sprintf("r%d", created)
		createReport(t, c, ns, n)
		p.send(a.m.ServeAddr, ns, n, "probe-"+n)
		if p.answer("probe-"+n) == http.StatusOK {
			name = n
		}
	}
	if name == "" {
		t.Fatalf("the first replica holds the shard of none of %d Reports", created)
	}
	e2e.Eventually(t, 30*time.Second, func() error {
		n, err := tryScrape(b.m.Addr, `kube_cache_objects{type="Report.`+group+`/v1",namespace="`+ns+`",selector=""}`)
		if err != nil {
			return err
		}
		if int(n) != created {
			return fmt.Errorf("the second replica caches %v of %d Reports", n, created)
		}
		return nil
	})
	versions := watchHistory(t, c, ns, name)

	t.Log("The first replica saves a result that the second replica's cache doesn't see, and stops.")
	watches.hold()
	p.send(a.m.ServeAddr, ns, name, "a")
	if code := p.answer("a"); code != http.StatusOK {
		t.Fatalf("POST a = %d, want 200", code)
	}
	a.stop()
	waitHeld(t, func(n []int) bool { return n[0] == shards }, b)

	t.Log("The second replica gets a result before its cache catches up.")
	p.trigger(b.h, b.m.ServeAddr, ns, name, "b")
	waitWriteTried(t, b, versions, "b")
	watches.release()
	if code := p.answer("b"); code != http.StatusOK {
		t.Fatalf("POST b = %d, want 200", code)
	}
	got := versions.check()
	for _, result := range []string{"probe-" + name, "a", "b"} {
		if !slices.Contains(got, result) {
			t.Errorf("POST %s got 200, but the results are %q", result, got)
		}
	}
	if n := scrape(t, b.m.Addr, `kube_reconcile_total{controller="reports",result="stale"}`); n == 0 {
		t.Error("the second replica counted no stale reconciles")
	}
	if n := scrape(t, b.m.Addr, `kube_reconcile_total{controller="reports",result="error"}`); n != 0 {
		t.Errorf("the second replica counted %v reconcile errors, want 0", n)
	}
}

// TestServeTakeOverWithAStaleGetCache runs two replicas with leader
// election. A request to the standby starts the cache that Get reads there,
// and that cache then falls behind. The standby takes over with a new
// controller cache that is current, but its reconcile reads the stale cache
// with Get. The framework doesn't write the status until both caches have
// the same version, so the write keeps the result that the first leader
// saved.
func TestServeTakeOverWithAStaleGetCache(t *testing.T) {
	c := e2e.Client(t)
	ns := e2e.Namespace(t, c)
	watches, kubeconfig := newWatchHold(t, "reports")
	a := startReplica(t, ns, e2e.Env(t).Kubeconfig, 1)
	waitHeld(t, func(n []int) bool { return n[0] == 1 }, a)
	b := startReplica(t, ns, kubeconfig, 1)
	createReport(t, c, ns, "lead")

	t.Log("A request to the standby starts the cache that Get reads there.")
	e2e.Eventually(t, 30*time.Second, func() error {
		resp, err := http.Get("http://" + b.m.ServeAddr + "/reports/" + ns + "/lead")
		if err != nil {
			return err
		}
		resp.Body.Close()
		if resp.StatusCode != http.StatusOK {
			return fmt.Errorf("GET = %d", resp.StatusCode)
		}
		return nil
	})
	versions := watchHistory(t, c, ns, "lead")

	t.Log("The leader saves a result that the standby's cache doesn't see, and stops.")
	watches.hold()
	p := &posts{t: t, codes: map[string]chan int{}}
	p.send(a.m.ServeAddr, ns, "lead", "a")
	if code := p.answer("a"); code != http.StatusOK {
		t.Fatalf("POST a = %d, want 200", code)
	}
	a.stop()
	waitHeld(t, func(n []int) bool { return n[0] == 1 }, b)

	t.Log("The new leader gets a result before the cache that Get reads catches up.")
	p.trigger(b.h, b.m.ServeAddr, ns, "lead", "b")
	waitWriteTried(t, b, versions, "b")
	watches.release()
	if code := p.answer("b"); code != http.StatusOK {
		t.Fatalf("POST b = %d, want 200", code)
	}
	got := versions.check()
	for _, result := range []string{"a", "b"} {
		if !slices.Contains(got, result) {
			t.Errorf("POST %s got 200, but the results are %q", result, got)
		}
	}
}

// TestLeaderWritesStatusInAWatchedNamespace runs a leader-elected controller
// that watches Reports outside the manager's namespace, where the cache that
// Get reads can't hold them. The first reconcile's Get starts that cache,
// and the first status write of each later Report doesn't wait for it to
// hold the Report.
func TestLeaderWritesStatusInAWatchedNamespace(t *testing.T) {
	c := e2e.Client(t)
	ns, watched := e2e.Namespace(t, c), e2e.Namespace(t, c)
	h := &reports{pending: map[kube.Key][]string{}}
	m := &kube.Manager{Name: "reports-watched-e2e", Namespace: ns, LeaseNamespace: ns, LeaderElection: true}
	e2e.Run(t, m, kube.For[Report](h, kube.Named("reports"), kube.WatchNamespace(watched)))
	createReport(t, c, watched, "first")
	createReport(t, c, watched, "second")
}

// finalizedReports gets the framework's finalizer on every Report.
type finalizedReports struct{}

func (finalizedReports) Reconcile(context.Context, *Report) error { return nil }
func (finalizedReports) Finalize(context.Context, *Report) error  { return nil }

// childReports owns a ConfigMap in another namespace for each Report labeled
// child=true. Garbage collection can't delete it with the Report.
type childReports struct {
	namespace string
	// gate, if set, can stop reconciles before they declare the ConfigMap.
	gate *gate
}

func (r childReports) Reconcile(ctx context.Context, rep *Report) error {
	r.gate.wait(ctx)
	if rep.Labels["child"] == "true" {
		cm := &k8s.ConfigMap{Object: kube.Meta(rep.Name, nil), Data: map[string]string{"owner": rep.Namespace}}
		cm.Namespace = r.namespace
		kube.Own(ctx, cm)
	}
	return nil
}

// TestParentWritesBeforeTheFirstStatusWrite runs controllers with leader
// election, where each new object's first status write requires the
// resource version that its reconcile read. Adding or removing the
// finalizer changes that version before the status write, so the framework
// must send the version that the finalizer write returned. Otherwise every
// new object's first status write fails as stale.
func TestParentWritesBeforeTheFirstStatusWrite(t *testing.T) {
	const n = 5
	t.Run("Finalize", func(t *testing.T) {
		c := e2e.Client(t)
		ns := e2e.Namespace(t, c)
		m := startLeader(t, ns, kube.For[Report](finalizedReports{}, kube.Named("finalized")))
		for i := range n {
			createReport(t, c, ns, fmt.Sprintf("r%d", i))
		}
		noRetries(t, m, "finalized", n)
	})
	t.Run("child in another namespace", func(t *testing.T) {
		c := e2e.Client(t)
		ns, other := e2e.Namespace(t, c), e2e.Namespace(t, c)
		m := startLeader(t, ns, kube.For[Report](childReports{namespace: other}, kube.Named("parents")))

		t.Log("Reports with a child get the finalizer and the cleanup annotation first.")
		for i := range n {
			createReportWith(t, c, ns, map[string]any{"name": fmt.Sprintf("parent%d", i), "labels": map[string]string{"child": "true"}})
		}
		noRetries(t, m, "parents", n)
		var parent Report
		if err := e2e.Get(t.Context(), c, client.Path(group+"/v1", "reports", ns, "parent0"), &parent); err != nil {
			t.Fatal(err)
		}
		if len(parent.Finalizers) != 1 {
			t.Fatalf("finalizers = %q, want the framework's", parent.Finalizers)
		}

		t.Log("Reports that have the finalizer but no child get it removed first.")
		for i := range n {
			createReportWith(t, c, ns, map[string]any{"name": fmt.Sprintf("leftover%d", i), "finalizers": parent.Finalizers})
		}
		noRetries(t, m, "parents", 2*n)
		var leftover Report
		if err := e2e.Get(t.Context(), c, client.Path(group+"/v1", "reports", ns, "leftover0"), &leftover); err != nil {
			t.Fatal(err)
		}
		if len(leftover.Finalizers) != 0 {
			t.Errorf("finalizers = %q, want none", leftover.Finalizers)
		}
	})
}

// TestParentWriteFromAnOutOfDateObject stops a leader's first reconcile of
// a new Report after the framework read the object. Then a status write with
// the controller's field manager lands, as a previous holder's would. The
// finalizer write before the reconcile's status write must require the
// resource version that the framework read. Otherwise the status write
// carries the version that the finalizer write returned, and removes the
// result that the other write added.
func TestParentWriteFromAnOutOfDateObject(t *testing.T) {
	c := e2e.Client(t)
	ns, other := e2e.Namespace(t, c), e2e.Namespace(t, c)
	g := newGate()
	m := startLeader(t, ns, kube.For[Report](childReports{namespace: other, gate: g}, kube.Named("parents")))
	g.set(true)
	e2e.Eventually(t, 30*time.Second, func() error {
		return c.Create(t.Context(), client.Path(group+"/v1", "reports", ns, ""), map[string]any{
			"apiVersion": group + "/v1", "kind": "Report",
			"metadata": map[string]any{"name": "late", "labels": map[string]string{"child": "true"}},
		}, nil)
	})
	resume := g.next(t)

	t.Log("A status write from another replica lands while the reconcile waits.")
	path := client.Path(group+"/v1", "reports", ns, "late")
	err := c.Apply(t.Context(), path+"/status", "parents", true, map[string]any{
		"apiVersion": group + "/v1", "kind": "Report",
		"metadata": map[string]any{"name": "late", "namespace": ns},
		"status":   map[string]any{"results": []string{"a"}},
	}, nil)
	if err != nil {
		t.Fatal(err)
	}
	g.set(false)
	close(resume)

	var rep Report
	e2e.Eventually(t, 30*time.Second, func() error {
		if err := e2e.Get(t.Context(), c, path, &rep); err != nil {
			return err
		}
		if len(rep.Status.Conditions) == 0 {
			return errors.New("the controller hasn't written the status")
		}
		return nil
	})
	if !slices.Contains(rep.Status.Results, "a") {
		t.Errorf("results = %q, want the result that the other write added", rep.Status.Results)
	}
	if n := scrape(t, m.Addr, `kube_reconcile_total{controller="parents",result="stale"}`); n == 0 {
		t.Error("no reconcile failed as stale")
	}
}

// startLeader runs controllers with leader election and waits until the
// manager leads.
func startLeader(t *testing.T, ns string, controllers ...kube.Controller) *kube.Manager {
	t.Helper()
	m := &kube.Manager{Name: "parent-writes-e2e", Namespace: ns, LeaseNamespace: ns, LeaderElection: true, Addr: freeAddr(t)}
	e2e.Run(t, m, controllers...)
	waitHeld(t, func(n []int) bool { return n[0] == 1 }, &replica{m: m})
	return m
}

// noRetries checks that at least want reconciles of the controller
// succeeded and that none was retried.
func noRetries(t *testing.T, m *kube.Manager, controller string, want int) {
	t.Helper()
	sample := `kube_reconcile_total{controller="` + controller + `",result=`
	if n := scrape(t, m.Addr, sample+`"success"}`); n < float64(want) {
		t.Errorf("%v reconciles of %s succeeded, want at least %d", n, controller, want)
	}
	for _, result := range []string{"stale", "error"} {
		if n := scrape(t, m.Addr, sample+`"`+result+`"}`); n != 0 {
			t.Errorf("%v reconciles of %s ended with result=%q, want 0", n, controller, result)
		}
	}
}

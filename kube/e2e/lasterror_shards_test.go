package e2e_test

import (
	"context"
	"fmt"
	"hash/fnv"
	"strings"
	"sync"
	"testing"
	"time"

	"github.com/imjasonh/playground/kube"
	"github.com/imjasonh/playground/kube/internal/client"
	"github.com/imjasonh/playground/kube/internal/e2e"
	"github.com/imjasonh/playground/kube/k8s"
)

// roundTripLog records which replica reconciled each Widget, at which size,
// and what kube.LastError returned.
type roundTripLog struct {
	mu   sync.Mutex
	seen map[string][]roundTripAttempt
}

type roundTripAttempt struct {
	replica string
	size    int
	err     error
}

// roundTripReconciler reconciles each Widget into a ConfigMap whose label
// value is as long as the widget's size, so the API server rejects sizes
// over 63, as lastErrors does.
type roundTripReconciler struct {
	replica string
	log     *roundTripLog
}

func (r roundTripReconciler) Reconcile(ctx context.Context, w *Widget) error {
	key := w.Namespace + "/" + w.Name
	r.log.mu.Lock()
	r.log.seen[key] = append(r.log.seen[key], roundTripAttempt{r.replica, w.Spec.Size, kube.LastError(ctx)})
	r.log.mu.Unlock()
	kube.Own(ctx, &k8s.ConfigMap{Object: kube.Meta(w.Name, map[string]string{"size": strings.Repeat("x", w.Spec.Size)})})
	return nil
}

func (l *roundTripLog) has(key, replica string, size int, failed bool) (roundTripAttempt, bool) {
	l.mu.Lock()
	defer l.mu.Unlock()
	for _, a := range l.seen[key] {
		if a.replica == replica && a.size == size && (!failed || a.err != nil) {
			return a, true
		}
	}
	return roundTripAttempt{}, false
}

// TestLastErrorAfterShardRoundTrip deletes Widgets while another replica
// holds their shard, gives the shard back, and recreates the Widgets under
// the same names. The new Widgets' first reconciles must not see the old
// Widgets' errors.
func TestLastErrorAfterShardRoundTrip(t *testing.T) {
	c := e2e.Client(t)
	env := e2e.Env(t)
	ns := e2e.Namespace(t, c)
	const shards = 16
	log := &roundTripLog{seen: map[string][]roundTripAttempt{}}
	type replica struct {
		addr   string
		cancel context.CancelFunc
		done   chan error
	}
	replicas := map[string]*replica{}
	start := func(name string) {
		rep := &replica{addr: freeAddr(t), done: make(chan error, 1)}
		ctx, cancel := context.WithCancel(t.Context())
		rep.cancel = cancel
		m := &kube.Manager{Name: "lasterror-shards-e2e", Kubeconfig: env.Kubeconfig, Namespace: ns, LeaseNamespace: ns, Shards: shards, Addr: rep.addr, Logger: e2e.Logger(t)}
		go func() {
			rep.done <- m.Run(ctx, kube.For[Widget](roundTripReconciler{replica: name, log: log}, kube.Named("lasterror-shards")))
		}()
		replicas[name] = rep
	}
	stop := func(name string) {
		rep := replicas[name]
		rep.cancel()
		select {
		case err := <-rep.done:
			if err != nil {
				t.Errorf("replica %s: %v", name, err)
			}
		case <-time.After(30 * time.Second):
			t.Errorf("replica %s didn't stop", name)
		}
		delete(replicas, name)
	}
	defer func() {
		for name := range replicas {
			stop(name)
		}
	}()
	balanced := func() {
		t.Helper()
		e2e.Eventually(t, 60*time.Second, func() error {
			total := 0
			for name, rep := range replicas {
				held, err := tryScrape(rep.addr, "kube_shards_held")
				if err != nil {
					return err
				}
				if held == 0 {
					return fmt.Errorf("replica %s holds no shards", name)
				}
				total += int(held)
			}
			if total != shards {
				return fmt.Errorf("replicas hold %d of %d shards", total, shards)
			}
			return nil
		})
	}
	shardOf := func(name string) int {
		h := fnv.New32a()
		h.Write([]byte(ns + "/" + name))
		return int(h.Sum32() % shards)
	}
	// One Widget in each shard, so some move to b and some stay on a.
	var names []string
	taken := map[int]bool{}
	for i := 0; len(names) < shards; i++ {
		n := fmt.Sprintf("w-%d", i)
		if s := shardOf(n); !taken[s] {
			taken[s] = true
			names = append(names, n)
		}
	}

	t.Log("Replica a alone fails to reconcile every Widget and retries with the error.")
	start("a")
	balanced()
	for _, n := range names {
		createWidget(t, c, ns, n, 64)
	}
	e2e.Eventually(t, 30*time.Second, func() error {
		for _, n := range names {
			if _, ok := log.has(ns+"/"+n, "a", 64, true); !ok {
				return fmt.Errorf("%s: no retry on a has seen an error yet", n)
			}
		}
		return nil
	})

	t.Log("Replica b takes some of the shards.")
	start("b")
	balanced()
	// b reconciles the Widgets in its shards when its informer first lists
	// them.
	time.Sleep(3 * time.Second)
	isMoved := map[string]bool{}
	moved := 0
	for _, n := range names {
		if _, ok := log.has(ns+"/"+n, "b", 64, false); ok {
			isMoved[n] = true
			moved++
		}
	}
	if moved == 0 || moved == len(names) {
		t.Fatalf("%d of %d Widgets moved to b; want some to move and some to stay", moved, len(names))
	}
	e2e.Eventually(t, 30*time.Second, func() error {
		for _, n := range names {
			if _, ok := log.has(ns+"/"+n, "b", 64, true); isMoved[n] && !ok {
				return fmt.Errorf("%s: no retry on b has seen an error yet", n)
			}
		}
		return nil
	})
	t.Logf("moved to b: %v", isMoved)

	t.Log("Every Widget is deleted while b holds the moved shard.")
	for _, n := range names {
		if err := c.Delete(t.Context(), client.Path(group+"/v1", "widgets", ns, n), client.DeleteOptions{}); err != nil {
			t.Fatal(err)
		}
	}
	e2e.Eventually(t, 30*time.Second, func() error {
		for _, n := range names {
			if _, err := widget(t, c, ns, n); err == nil {
				return fmt.Errorf("%s still exists", n)
			}
		}
		return nil
	})
	time.Sleep(2 * time.Second)

	t.Log("Replica b stops, so a takes back the shard while the Widgets don't exist.")
	stop("b")
	balanced()

	t.Log("The Widgets come back under the same names with a size that works.")
	for _, n := range names {
		createWidget(t, c, ns, n, 3)
	}
	e2e.Eventually(t, 30*time.Second, func() error {
		for _, n := range names {
			if _, ok := log.has(ns+"/"+n, "a", 3, false); !ok {
				return fmt.Errorf("%s: a hasn't reconciled the new Widget yet", n)
			}
		}
		return nil
	})
	for _, n := range names {
		a, _ := log.has(ns+"/"+n, "a", 3, false)
		if a.err != nil {
			t.Errorf("%s (moved to b and back: %v): the new Widget's first reconcile saw LastError = %v, want nil", n, isMoved[n], a.err)
		} else {
			t.Logf("%s (moved to b and back: %v): the new Widget's first reconcile saw LastError = nil", n, isMoved[n])
		}
	}
}

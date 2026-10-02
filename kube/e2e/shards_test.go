package e2e_test

import (
	"context"
	"fmt"
	"sync"
	"testing"
	"time"

	"github.com/imjasonh/playground/kube"
	"github.com/imjasonh/playground/kube/internal/client"
	"github.com/imjasonh/playground/kube/internal/e2e"
)

// shardLog records which replica reconciles which Widget, and any time two
// replicas reconcile one Widget at the same time.
type shardLog struct {
	mu       sync.Mutex
	active   map[string]string
	overlaps []string
	by       map[string]map[string]int // replica -> key -> reconciles
}

type shardReconciler struct {
	replica string
	log     *shardLog
}

func (r shardReconciler) Reconcile(_ context.Context, w *Widget) error {
	key := w.Namespace + "/" + w.Name
	l := r.log
	l.mu.Lock()
	if other, ok := l.active[key]; ok {
		l.overlaps = append(l.overlaps, fmt.Sprintf("%s: %s and %s", key, other, r.replica))
	}
	l.active[key] = r.replica
	if l.by[r.replica] == nil {
		l.by[r.replica] = map[string]int{}
	}
	l.by[r.replica][key]++
	l.mu.Unlock()
	time.Sleep(20 * time.Millisecond)
	l.mu.Lock()
	if l.active[key] == r.replica {
		delete(l.active, key)
	}
	l.mu.Unlock()
	w.Status.Size = w.Spec.Size
	return nil
}

// reconciled returns the replicas that reconciled each of keys.
func (l *shardLog) reconciled(keys []string) map[string][]string {
	l.mu.Lock()
	defer l.mu.Unlock()
	out := map[string][]string{}
	for _, k := range keys {
		for replica, counts := range l.by {
			if counts[k] > 0 {
				out[k] = append(out[k], replica)
			}
		}
	}
	return out
}

func TestShardsSplitWorkAcrossReplicas(t *testing.T) {
	c := e2e.Client(t)
	env := e2e.Env(t)
	ns := e2e.Namespace(t, c)
	const shards = 32
	log := &shardLog{active: map[string]string{}, by: map[string]map[string]int{}}
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
		m := &kube.Manager{Name: "shards-e2e", Kubeconfig: env.Kubeconfig, Namespace: ns, LeaseNamespace: ns, Shards: shards, Addr: rep.addr, Logger: e2e.Logger(t)}
		go func() {
			rep.done <- m.Run(ctx, kube.For[Widget](shardReconciler{replica: name, log: log}, kube.Named("shards")))
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
	// balanced waits until every running replica holds some shards and
	// together they hold all of them.
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
	batch := 0
	// create makes n Widgets and waits until each is reconciled, returning
	// the replicas that reconciled each.
	create := func(n int) map[string][]string {
		t.Helper()
		batch++
		var keys []string
		for i := range n {
			name := fmt.Sprintf("w%d-%02d", batch, i)
			createWidget(t, c, ns, name, i)
			keys = append(keys, ns+"/"+name)
		}
		var got map[string][]string
		e2e.Eventually(t, 30*time.Second, func() error {
			got = log.reconciled(keys)
			if len(got) != len(keys) {
				return fmt.Errorf("%d of %d Widgets reconciled", len(got), len(keys))
			}
			return nil
		})
		return got
	}
	byReplica := func(got map[string][]string) map[string]int {
		out := map[string]int{}
		for _, reps := range got {
			for _, r := range reps {
				out[r]++
			}
		}
		return out
	}

	t.Log("Three replicas split the shards and the Widgets between them.")
	start("a")
	start("b")
	start("c")
	balanced()
	counts := byReplica(create(30))
	for _, name := range []string{"a", "b", "c"} {
		if counts[name] == 0 {
			t.Errorf("replica %s reconciled none of 30 Widgets: %v", name, counts)
		}
	}

	t.Log("When a replica stops, the others take over its shards.")
	stop("a")
	balanced()
	if counts := byReplica(create(20)); counts["a"] != 0 || counts["b"] == 0 || counts["c"] == 0 {
		t.Errorf("after a stopped, reconciles by replica = %v", counts)
	}

	t.Log("A new replica gets its share of the shards.")
	start("d")
	balanced()
	if counts := byReplica(create(30)); counts["d"] == 0 {
		t.Errorf("the new replica reconciled none of 30 Widgets: %v", counts)
	}

	log.mu.Lock()
	defer log.mu.Unlock()
	if len(log.overlaps) > 0 {
		t.Errorf("replicas reconciled a Widget at the same time: %v", log.overlaps)
	}
	var leases struct {
		Items []struct {
			Metadata struct {
				Name string `json:"name"`
			} `json:"metadata"`
		} `json:"items"`
	}
	if err := c.Get(t.Context(), client.Path("coordination.k8s.io/v1", "leases", ns, ""), &leases); err != nil {
		t.Fatal(err)
	}
	if want := shards + 3; len(leases.Items) != want {
		t.Errorf("%d Leases, want %d shards and 3 live replicas' memberships", len(leases.Items), want)
	}
}

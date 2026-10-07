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

// Reminder has a time, which the API server accepts in spellings that Go
// doesn't parse.
type Reminder struct {
	kube.Object `kube:"group=e2e.kube.imjasonh.github.io"`
	Spec        struct {
		At time.Time `json:"at"`
	} `json:"spec"`
}

// reminders counts reconciles by name.
type reminders struct {
	mu    sync.Mutex
	calls map[string]int
}

func (r *reminders) Reconcile(_ context.Context, o *Reminder) error {
	r.mu.Lock()
	defer r.mu.Unlock()
	if r.calls == nil {
		r.calls = map[string]int{}
	}
	r.calls[o.Name]++
	return nil
}

func (r *reminders) reconciled(names ...string) error {
	r.mu.Lock()
	defer r.mu.Unlock()
	for _, n := range names {
		if r.calls[n] == 0 {
			return fmt.Errorf("%s isn't reconciled; reconciles = %v", n, r.calls)
		}
	}
	return nil
}

func TestObjectsThatDontDecodeAreSkipped(t *testing.T) {
	c := e2e.Client(t)
	ns := e2e.Namespace(t, c)
	create := func(name, at string) error {
		return c.Create(t.Context(), client.Path(group+"/v1", "reminders", ns, ""), map[string]any{
			"apiVersion": group + "/v1", "kind": "Reminder", "metadata": map[string]any{"name": name}, "spec": map[string]any{"at": at},
		}, nil)
	}
	skipped := `kube_cache_undecodable_objects{type="Reminder.` + group + `/v1",namespace="` + ns + `",selector=""}`
	gauge := func(addr string, want float64) error {
		if n := scrape(t, addr, skipped); n != want {
			return fmt.Errorf("%s = %v, want %v", skipped, n, want)
		}
		return nil
	}

	watcher, watched := freeAddr(t), &reminders{}
	e2e.Run(t, &kube.Manager{Name: "undecodable-e2e", Namespace: ns, Addr: watcher}, kube.For[Reminder](watched))
	e2e.Eventually(t, 30*time.Second, func() error { return create("before", "2024-01-01T10:00:00Z") })
	e2e.Eventually(t, 10*time.Second, func() error { return watched.reconciled("before") })

	t.Log("The API server accepts a time that Go can't parse. The watch skips the object and goes on.")
	if err := create("bad", "2024-01-01t10:00:00z"); err != nil {
		t.Fatalf("creating a Reminder with a lowercase time: %v", err)
	}
	if err := create("after", "2024-01-02T10:00:00Z"); err != nil {
		t.Fatal(err)
	}
	e2e.Eventually(t, 10*time.Second, func() error {
		if err := watched.reconciled("after"); err != nil {
			return err
		}
		return gauge(watcher, 1)
	})

	t.Log("A paginated list skips the object too.")
	lister, listed := freeAddr(t), &reminders{}
	e2e.Run(t, &kube.Manager{Name: "undecodable-e2e", Namespace: ns, Addr: lister, DisableStreamingLists: true}, kube.For[Reminder](listed))
	e2e.Eventually(t, 10*time.Second, func() error {
		if err := listed.reconciled("before", "after"); err != nil {
			return err
		}
		return gauge(lister, 1)
	})

	t.Log("Fixing the object reconciles it.")
	fix := []byte(`{"spec":{"at":"2024-01-01T10:00:00Z"}}`)
	if err := c.Patch(t.Context(), client.Path(group+"/v1", "reminders", ns, "bad"), client.MergePatch, nil, fix, nil); err != nil {
		t.Fatal(err)
	}
	e2e.Eventually(t, 10*time.Second, func() error {
		for _, r := range []*reminders{watched, listed} {
			if err := r.reconciled("bad"); err != nil {
				return err
			}
		}
		if err := gauge(watcher, 0); err != nil {
			return err
		}
		return gauge(lister, 0)
	})
}

package e2e_test

import (
	"context"
	"errors"
	"fmt"
	"os"
	"sync"
	"sync/atomic"
	"testing"
	"time"

	"github.com/imjasonh/playground/kube"
	"github.com/imjasonh/playground/kube/internal/client"
	"github.com/imjasonh/playground/kube/internal/e2e"
	"github.com/imjasonh/playground/kube/k8s"
)

// Whatsit is reconciled only by TestEvents, which leaves Whatsits behind. Other
// tests reconcile Widgets in every namespace and count their writes.
type Whatsit struct {
	kube.Object `kube:"group=e2e.kube.imjasonh.github.io"`
	Spec        struct {
		Size int `json:"size"`
	} `json:"spec"`
	Status struct {
		Conditions []kube.Condition `json:"conditions,omitempty"`
	} `json:"status,omitzero"`
}

// eventer records an event each time it reconciles or finalizes a Whatsit.
// It fails to reconcile a Whatsit named failing, which the framework retries.
type eventer struct{ failures atomic.Int64 }

func (r *eventer) Reconcile(ctx context.Context, d *Whatsit) error {
	if d.Name == "failing" {
		r.failures.Add(1)
		kube.Eventf(ctx, kube.Warning, "TooBig", "size %d is too big", d.Spec.Size)
		return errors.New("too big")
	}
	kube.Eventf(ctx, kube.Normal, "Sized", "size is %d", d.Spec.Size)
	return nil
}

func (r *eventer) Finalize(ctx context.Context, d *Whatsit) error {
	kube.Eventf(ctx, kube.Normal, "Finalized", "cleaned up after size %d", d.Spec.Size)
	return nil
}

type namespaceEventer struct{}

func (namespaceEventer) Reconcile(ctx context.Context, ns *k8s.Namespace) error {
	kube.Eventf(ctx, kube.Normal, "Seen", "saw namespace %s", ns.Name)
	return nil
}

type event struct {
	Type                string `json:"type"`
	Reason              string `json:"reason"`
	Action              string `json:"action"`
	Note                string `json:"note"`
	ReportingController string `json:"reportingController"`
	ReportingInstance   string `json:"reportingInstance"`
	Regarding           struct {
		APIVersion string `json:"apiVersion"`
		Kind       string `json:"kind"`
		Namespace  string `json:"namespace"`
		Name       string `json:"name"`
		UID        string `json:"uid"`
	} `json:"regarding"`
	Series *struct {
		Count int `json:"count"`
	} `json:"series"`
}

// events returns the Events in ns with reason about objects named name.
func events(t *testing.T, c *client.Client, ns, name, reason string) ([]event, error) {
	var list struct {
		Items []event `json:"items"`
	}
	if err := e2e.Get(t.Context(), c, client.Path("events.k8s.io/v1", "events", ns, ""), &list); err != nil {
		return nil, err
	}
	var out []event
	for _, e := range list.Items {
		if e.Regarding.Name == name && e.Reason == reason {
			out = append(out, e)
		}
	}
	return out, nil
}

// oneEvent returns the one Event in ns with reason about objects named name.
func oneEvent(t *testing.T, c *client.Client, ns, name, reason string) (event, error) {
	es, err := events(t, c, ns, name, reason)
	if err != nil {
		return event{}, err
	}
	if len(es) != 1 {
		return event{}, fmt.Errorf("%d %s Events about %s in %s, want 1: %+v", len(es), reason, name, ns, es)
	}
	return es[0], nil
}

func TestEvents(t *testing.T) {
	c := e2e.Client(t)
	env := e2e.Env(t)
	ns := e2e.Namespace(t, c)
	label := fmt.Sprintf(`{"metadata":{"labels":{"events-e2e":%q}}}`, ns)
	if err := c.Patch(t.Context(), client.Path("v1", "namespaces", "", ns), client.MergePatch, nil, []byte(label), nil); err != nil {
		t.Fatal(err)
	}
	host, _ := os.Hostname()
	addr := freeAddr(t)
	r := &eventer{}
	ctx, cancel := context.WithCancel(t.Context())
	done := make(chan error, 1)
	m := &kube.Manager{Name: "events-e2e", Kubeconfig: env.Kubeconfig, Addr: addr, Logger: e2e.Logger(t)}
	go func() {
		done <- m.Run(ctx,
			kube.For[Whatsit](r, kube.Named("events"), kube.WatchNamespace(ns)),
			kube.For[k8s.Namespace](namespaceEventer{}, kube.Named("namespaces"), kube.WatchSelector("events-e2e="+ns)))
	}()
	stop := sync.OnceFunc(func() {
		cancel()
		if err := <-done; err != nil {
			t.Errorf("manager: %v", err)
		}
	})
	defer stop()
	whatsitPath := func(name string) string { return client.Path(group+"/v1", "whatsits", ns, name) }
	create := func(name string, size int) {
		e2e.Eventually(t, 30*time.Second, func() error {
			return c.Create(t.Context(), whatsitPath(""), map[string]any{
				"apiVersion": group + "/v1", "kind": "Whatsit", "metadata": map[string]any{"name": name}, "spec": map[string]any{"size": size},
			}, nil)
		})
	}

	t.Log("A reconcile's event becomes an events.k8s.io/v1 Event about the Whatsit.")
	create("fine", 3)
	e2e.Eventually(t, 10*time.Second, func() error {
		var d Whatsit
		if err := e2e.Get(t.Context(), c, whatsitPath("fine"), &d); err != nil {
			return err
		}
		e, err := oneEvent(t, c, ns, "fine", "Sized")
		if err != nil {
			return err
		}
		if e.Type != kube.Normal || e.Action != "Reconcile" || e.Note != "size is 3" || e.ReportingController != "events" || e.ReportingInstance != "events-"+host ||
			e.Regarding.APIVersion != group+"/v1" || e.Regarding.Kind != "Whatsit" || e.Regarding.Namespace != ns || e.Regarding.UID != d.UID {
			return fmt.Errorf("Event = %+v", e)
		}
		return nil
	})

	t.Log("kubectl describe reads the same Event through the core v1 API.")
	var coreEvents struct {
		Items []struct {
			InvolvedObject struct {
				Kind string `json:"kind"`
				Name string `json:"name"`
			} `json:"involvedObject"`
			Reason             string `json:"reason"`
			Message            string `json:"message"`
			ReportingComponent string `json:"reportingComponent"`
		} `json:"items"`
	}
	if err := e2e.Get(t.Context(), c, client.Path("v1", "events", ns, ""), &coreEvents); err != nil {
		t.Fatal(err)
	}
	found := false
	for _, e := range coreEvents.Items {
		found = found || e.InvolvedObject.Kind == "Whatsit" && e.InvolvedObject.Name == "fine" && e.Reason == "Sized" && e.Message == "size is 3" && e.ReportingComponent == "events"
	}
	if !found {
		t.Errorf("core v1 Events = %+v", coreEvents.Items)
	}

	t.Log("A failing reconcile's retries add to one Event, though the first failure's status write changed the Whatsit.")
	create("failing", 9)
	e2e.Eventually(t, 10*time.Second, func() error {
		var d Whatsit
		if err := e2e.Get(t.Context(), c, whatsitPath("failing"), &d); err != nil {
			return err
		}
		if cond := kube.FindCondition(d.Status.Conditions, "Synced"); cond == nil || cond.Status != kube.False {
			return fmt.Errorf("Synced condition = %+v", cond)
		}
		e, err := oneEvent(t, c, ns, "failing", "TooBig")
		if err != nil {
			return err
		}
		if e.Type != kube.Warning || e.Note != "size 9 is too big" || e.Series == nil || e.Series.Count != 2 {
			return fmt.Errorf("Event = %+v", e)
		}
		return nil
	})
	e2e.Eventually(t, 10*time.Second, func() error {
		if n := r.failures.Load(); n < 4 {
			return fmt.Errorf("the failing Whatsit was reconciled %d times", n)
		}
		return nil
	})
	if es, err := events(t, c, ns, "failing", "TooBig"); err != nil || len(es) != 1 || es[0].Series == nil || es[0].Series.Count != 2 {
		t.Errorf("after more retries, Events = %+v, %v, want one with a count of 2 until the next flush", es, err)
	}

	t.Log("An event about a cluster-scoped object goes in the default namespace.")
	e2e.Eventually(t, 10*time.Second, func() error {
		e, err := oneEvent(t, c, "default", ns, "Seen")
		if err != nil {
			return err
		}
		if e.Regarding.Kind != "Namespace" || e.Regarding.Namespace != "" || e.ReportingController != "namespaces" || e.Note != "saw namespace "+ns {
			return fmt.Errorf("Event = %+v", e)
		}
		return nil
	})

	t.Log("The metrics count the Events that the manager created and updated.")
	if got := scrape(t, addr, `kube_events_total{controller="events",result="created"}`); got != 2 {
		t.Errorf("created Events = %v, want 2", got)
	}
	if got := scrape(t, addr, `kube_events_total{controller="events",result="updated"}`); got < 1 {
		t.Errorf("updated Events = %v, want at least 1", got)
	}

	t.Log("Finalize records events too.")
	if err := c.Delete(t.Context(), whatsitPath("fine"), client.DeleteOptions{}); err != nil {
		t.Fatal(err)
	}
	e2e.Eventually(t, 10*time.Second, func() error {
		e, err := oneEvent(t, c, ns, "fine", "Finalized")
		if err != nil {
			return err
		}
		if e.Action != "Finalize" || e.Note != "cleaned up after size 3" {
			return fmt.Errorf("Event = %+v", e)
		}
		return nil
	})

	t.Log("When the manager stops, it writes the count of every repeat.")
	stop()
	e, err := oneEvent(t, c, ns, "failing", "TooBig")
	if err != nil {
		t.Fatal(err)
	}
	if want := int(r.failures.Load()); e.Series == nil || e.Series.Count != want {
		t.Errorf("after the manager stopped, Event = %+v, want a count of %d", e, want)
	}
}

package e2e_test

import (
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"maps"
	"strconv"
	"strings"
	"sync/atomic"
	"testing"
	"time"

	"github.com/imjasonh/playground/kube"
	"github.com/imjasonh/playground/kube/internal/client"
	"github.com/imjasonh/playground/kube/internal/e2e"
)

// Ballot is one vote in a Poll. Its voter applies the vote to the poll's
// status.votes, and a ballot with no votes abstains.
type Ballot struct {
	kube.Object `kube:"group=e2e.kube.imjasonh.github.io"`
	Spec        struct {
		Poll  string `json:"poll"`
		Votes int    `json:"votes,omitempty"`
	} `json:"spec"`
}

// pollVotes declares only the votes in a Poll's status.
type pollVotes struct {
	kube.Object `kube:"group=e2e.kube.imjasonh.github.io,kind=Poll"`
	Status      struct {
		Votes map[string]int `json:"votes,omitempty"`
	} `json:"status,omitzero"`
}

// remove deletes the objects at paths when the test ends. Namespaces outlive
// their tests, and later tests count the objects that they reconcile in every
// namespace.
func remove(t *testing.T, c *client.Client, paths ...string) {
	t.Cleanup(func() {
		// t.Context is canceled before cleanups run.
		ctx := context.WithoutCancel(t.Context())
		for _, p := range paths {
			if err := c.Delete(ctx, p, client.DeleteOptions{}); err != nil && !client.IsNotFound(err) {
				t.Errorf("deleting %s: %v", p, err)
			}
		}
	})
}

type voter struct{ calls atomic.Int64 }

func (r *voter) Reconcile(ctx context.Context, b *Ballot) error {
	r.calls.Add(1)
	if kube.Get[pollVotes](ctx, b.Namespace, b.Spec.Poll) == nil {
		return nil
	}
	p := &pollVotes{Object: kube.Meta(b.Spec.Poll, nil)}
	if b.Spec.Votes != 0 {
		p.Status.Votes = map[string]int{b.Name: b.Spec.Votes}
	}
	kube.Apply(ctx, p)
	return nil
}

func TestApplyWritesStatus(t *testing.T) {
	c := e2e.Client(t)
	addr := freeAddr(t)
	v := &voter{}
	e2e.Run(t, &kube.Manager{Name: "ballot-e2e", Addr: addr}, kube.For[Poll](&tally{}, kube.Named("ballot-tally")), kube.For[Ballot](v, kube.Named("voter")))
	ns := e2e.Namespace(t, c)
	remove(t, c, client.Path(group+"/v1", "polls", ns, "p"), client.Path(group+"/v1", "ballots", ns, "alice"), client.Path(group+"/v1", "ballots", ns, "bob"))
	e2e.Eventually(t, 30*time.Second, func() error {
		return c.Create(t.Context(), client.Path(group+"/v1", "polls", ns, ""), map[string]any{
			"apiVersion": group + "/v1", "kind": "Poll", "metadata": map[string]any{"name": "p"}, "spec": map[string]any{"question": "Tabs?"},
		}, nil)
	})
	cast := func(name string, votes int) {
		t.Helper()
		e2e.Eventually(t, 30*time.Second, func() error {
			return c.Apply(t.Context(), client.Path(group+"/v1", "ballots", ns, name), "e2e", true, map[string]any{
				"apiVersion": group + "/v1", "kind": "Ballot", "metadata": map[string]any{"name": name, "namespace": ns},
				"spec": map[string]any{"poll": "p", "votes": votes},
			}, nil)
		})
	}
	type managedFields struct {
		Manager     string         `json:"manager"`
		Operation   string         `json:"operation"`
		Subresource string         `json:"subresource"`
		FieldsV1    map[string]any `json:"fieldsV1"`
	}
	type poll struct {
		Metadata struct {
			ManagedFields []managedFields `json:"managedFields"`
		} `json:"metadata"`
		Status struct {
			Total int            `json:"total"`
			Votes map[string]int `json:"votes"`
		} `json:"status"`
	}
	var last poll
	tallied := func(total int, votes map[string]int) func() error {
		return func() error {
			var p poll
			if err := e2e.Get(t.Context(), c, client.Path(group+"/v1", "polls", ns, "p"), &p); err != nil {
				return err
			}
			last = p
			if p.Status.Total != total || !maps.Equal(p.Status.Votes, votes) {
				return fmt.Errorf("status = %+v, want total %d and votes %v", p.Status, total, votes)
			}
			return nil
		}
	}
	// owned returns the status fields that manager owns, as JSON.
	owned := func(manager string) string {
		for _, mf := range last.Metadata.ManagedFields {
			if mf.Manager == manager && mf.Subresource == "status" {
				if mf.Operation != "Apply" {
					t.Errorf("%s's status entry has operation %q, want Apply", manager, mf.Operation)
				}
				b, _ := json.Marshal(mf.FieldsV1)
				return string(b)
			}
		}
		return ""
	}

	cast("alice", 1)
	cast("bob", 2)
	e2e.Eventually(t, 10*time.Second, tallied(3, map[string]int{"alice": 1, "bob": 2}))
	alice, bob := "voter/"+ns+"/alice", "voter/"+ns+"/bob"
	if got := owned(alice); !strings.Contains(got, `"f:alice"`) || strings.Contains(got, `"f:bob"`) {
		t.Errorf("%s owns %s, want only alice's vote", alice, got)
	}
	if got := owned("ballot-tally"); strings.Contains(got, "f:votes") {
		t.Errorf("the tally owns %s, want no votes", got)
	}

	t.Log("Each label change reconciles a ballot again, but finds nothing to write.")
	applied := `kube_apply_total{controller="voter",result="applied"}`
	skipped := `kube_apply_total{controller="voter",result="skipped"}`
	time.Sleep(500 * time.Millisecond)
	baseApplied, baseSkipped := scrape(t, addr, applied), scrape(t, addr, skipped)
	for i := range 3 {
		before := v.calls.Load()
		patch := fmt.Sprintf(`{"metadata":{"labels":{"touch":"%d"}}}`, i)
		if err := c.Patch(t.Context(), client.Path(group+"/v1", "ballots", ns, "alice"), client.MergePatch, nil, []byte(patch), nil); err != nil {
			t.Fatal(err)
		}
		e2e.Eventually(t, 5*time.Second, func() error {
			if v.calls.Load() == before {
				return errors.New("the label change hasn't been reconciled")
			}
			return nil
		})
	}
	time.Sleep(500 * time.Millisecond)
	if got := scrape(t, addr, applied); got != baseApplied {
		t.Errorf("applies = %v after no-op reconciles, want %v", got, baseApplied)
	}
	// Each reconcile skips the Poll and its status.
	if got := scrape(t, addr, skipped); got < baseSkipped+6 {
		t.Errorf("skipped applies = %v after no-op reconciles, want at least %v", got, baseSkipped+6)
	}

	t.Log("A voter that abstains gives up its vote; the other vote stays.")
	cast("alice", 0)
	e2e.Eventually(t, 10*time.Second, tallied(2, map[string]int{"bob": 2}))
	if got := owned(alice); strings.Contains(got, `"f:alice"`) {
		t.Errorf("%s still owns %s after abstaining", alice, got)
	}
	if got := owned(bob); !strings.Contains(got, `"f:bob"`) {
		t.Errorf("%s owns %s, want bob's vote", bob, got)
	}

	t.Log("A changed vote replaces the voter's earlier one.")
	cast("bob", 5)
	e2e.Eventually(t, 10*time.Second, tallied(5, map[string]int{"bob": 5}))
}

// noteMap is a ConfigMap type with a status, which ConfigMaps don't serve.
type noteMap struct {
	kube.Object `kube:"apiVersion=v1,kind=ConfigMap,plural=configmaps,scope=Namespaced"`
	Data        map[string]string `json:"data,omitempty"`
	Status      struct {
		Note string `json:"note,omitempty"`
	} `json:"status,omitzero"`
}

// noter applies a ConfigMap for each Widget, with a note in its status for
// a big widget.
type noter struct{}

func (noter) Reconcile(ctx context.Context, w *Widget) error {
	cm := &noteMap{Object: kube.Meta(w.Name+"-notes", nil), Data: map[string]string{"size": strconv.Itoa(w.Spec.Size)}}
	if w.Spec.Size > 5 {
		cm.Status.Note = "big"
	}
	kube.Apply(ctx, cm)
	return nil
}

func TestApplyStatusWithoutSubresource(t *testing.T) {
	c := e2e.Client(t)
	e2e.Run(t, &kube.Manager{Name: "noter-e2e"}, kube.For[Widget](noter{}, kube.Named("noter")))
	ns := e2e.Namespace(t, c)
	remove(t, c, client.Path(group+"/v1", "widgets", ns, "w"))
	createWidget(t, c, ns, "w", 1)
	state := func(size, status, message string) func() error {
		return func() error {
			var cm noteMap
			if err := e2e.Get(t.Context(), c, client.Path("v1", "configmaps", ns, "w-notes"), &cm); err != nil {
				return err
			}
			if cm.Data["size"] != size {
				return fmt.Errorf("data.size = %q, want %q", cm.Data["size"], size)
			}
			w, err := widget(t, c, ns, "w")
			if err != nil {
				return err
			}
			s := kube.FindCondition(w.Status.Conditions, "Synced")
			if s == nil || s.Status != status || !strings.Contains(s.Message, message) {
				return fmt.Errorf("Synced = %+v", s)
			}
			return nil
		}
	}

	t.Log("An empty status needs no status subresource.")
	e2e.Eventually(t, 10*time.Second, state("1", kube.True, ""))

	t.Log("Any other status fails the reconcile, after the rest of the ConfigMap is applied.")
	if err := c.Patch(t.Context(), client.Path(group+"/v1", "widgets", ns, "w"), client.MergePatch, nil, []byte(`{"spec":{"size":9}}`), nil); err != nil {
		t.Fatal(err)
	}
	e2e.Eventually(t, 10*time.Second, state("9", kube.False, "doesn't serve configmaps/status"))
}

// noteLabels declares only a ConfigMap's labels.
type noteLabels struct {
	kube.Object `kube:"apiVersion=v1,kind=ConfigMap,plural=configmaps,scope=Namespaced"`
}

// twoTypes applies a label and the data of one ConfigMap through two types.
type twoTypes struct{}

func (twoTypes) Reconcile(ctx context.Context, w *Widget) error {
	size := strconv.Itoa(w.Spec.Size)
	kube.Apply(ctx, &noteLabels{Object: kube.Meta(w.Name+"-notes", map[string]string{"size": size})})
	kube.Apply(ctx, &noteMap{Object: kube.Meta(w.Name+"-notes", nil), Data: map[string]string{"size": size}})
	return nil
}

func TestApplyOneObjectThroughTwoTypes(t *testing.T) {
	c := e2e.Client(t)
	ns := e2e.Namespace(t, c)
	e2e.Run(t, &kube.Manager{Name: "two-types-e2e", Namespace: ns}, kube.For[Widget](twoTypes{}, kube.Named("two-types")))
	remove(t, c, client.Path(group+"/v1", "widgets", ns, "w"))
	createWidget(t, c, ns, "w", 1)
	e2e.Eventually(t, 10*time.Second, func() error {
		w, err := widget(t, c, ns, "w")
		if err != nil {
			return err
		}
		if s := kube.FindCondition(w.Status.Conditions, "Synced"); s == nil || s.Status != kube.False || !strings.Contains(s.Message, "declare it with one type") {
			return fmt.Errorf("Synced = %+v", s)
		}
		return nil
	})
	if err := e2e.Gone(t.Context(), c, client.Path("v1", "configmaps", ns, "w-notes")); err != nil {
		t.Errorf("the failed reconcile wrote the ConfigMap: %v", err)
	}
}

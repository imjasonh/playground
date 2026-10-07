package e2e_test

import (
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"maps"
	"slices"
	"strconv"
	"strings"
	"sync/atomic"
	"testing"
	"time"

	"github.com/imjasonh/playground/kube"
	"github.com/imjasonh/playground/kube/internal/client"
	"github.com/imjasonh/playground/kube/internal/e2e"
	"github.com/imjasonh/playground/kube/k8s"
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
	if err := c.Create(t.Context(), client.Path("v1", "configmaps", ns, ""), map[string]any{
		"apiVersion": "v1", "kind": "ConfigMap", "metadata": map[string]any{"name": "w-notes"},
	}, nil); err != nil {
		t.Fatal(err)
	}
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

// labeler labels the Deployment named after each Widget with the widget's
// size, through k8s.Deployment, which has a status.
type labeler struct{}

func (labeler) Reconcile(ctx context.Context, w *Widget) error {
	if kube.Get[k8s.Deployment](ctx, w.Namespace, w.Name) == nil {
		return nil
	}
	kube.Apply(ctx, &k8s.Deployment{Object: kube.Meta(w.Name, map[string]string{"size": strconv.Itoa(w.Spec.Size)})})
	return nil
}

func TestApplyWithoutStatusPermission(t *testing.T) {
	c := e2e.Client(t)
	ns := e2e.Namespace(t, c)
	const rbac = "rbac.authorization.k8s.io/v1"
	role := ns + "-labeler"
	remove(t, c, client.Path(group+"/v1", "widgets", ns, "w"), client.Path("apps/v1", "deployments", ns, "w"),
		client.Path(rbac, "clusterrolebindings", "", role), client.Path(rbac, "clusterroles", "", role))
	app := map[string]string{"app": "w"}
	for _, o := range []struct {
		path string
		obj  map[string]any
	}{
		{client.Path("v1", "serviceaccounts", ns, ""), map[string]any{"apiVersion": "v1", "kind": "ServiceAccount", "metadata": map[string]any{"name": "labeler"}}},
		{client.Path(rbac, "clusterroles", "", ""), map[string]any{"apiVersion": rbac, "kind": "ClusterRole", "metadata": map[string]any{"name": role}, "rules": []any{
			map[string]any{"apiGroups": []string{"apiextensions.k8s.io", group}, "resources": []string{"*"}, "verbs": []string{"*"}},
			map[string]any{"apiGroups": []string{"apps"}, "resources": []string{"deployments"}, "verbs": []string{"*"}},
		}}},
		{client.Path(rbac, "clusterrolebindings", "", ""), map[string]any{"apiVersion": rbac, "kind": "ClusterRoleBinding", "metadata": map[string]any{"name": role},
			"roleRef":  map[string]any{"apiGroup": "rbac.authorization.k8s.io", "kind": "ClusterRole", "name": role},
			"subjects": []any{map[string]any{"kind": "ServiceAccount", "name": "labeler", "namespace": ns}},
		}},
		{client.Path("apps/v1", "deployments", ns, ""), map[string]any{"apiVersion": "apps/v1", "kind": "Deployment", "metadata": map[string]any{"name": "w"}, "spec": map[string]any{
			"selector": map[string]any{"matchLabels": app},
			"template": map[string]any{"metadata": map[string]any{"labels": app}, "spec": map[string]any{"containers": []any{map[string]any{"name": "app", "image": "nginx"}}}},
		}}},
	} {
		if err := c.Create(t.Context(), o.path, o.obj, nil); err != nil {
			t.Fatal(err)
		}
	}
	kubeconfig := serviceAccountKubeconfig(t, c, ns, "labeler")
	cfg, err := client.LoadKubeconfig([]string{kubeconfig}, "")
	if err != nil {
		t.Fatal(err)
	}
	sa, err := client.New(cfg, "e2e")
	if err != nil {
		t.Fatal(err)
	}
	// The API server's authorizer sees a new binding a moment after it's
	// created.
	e2e.Eventually(t, 30*time.Second, func() error {
		return sa.Get(t.Context(), client.Path("apps/v1", "deployments", ns, "w"), &map[string]any{})
	})

	e2e.Run(t, &kube.Manager{Name: "labeler-e2e", Namespace: ns, Kubeconfig: kubeconfig}, kube.For[Widget](labeler{}, kube.Named("labeler")))
	createWidget(t, c, ns, "w", 3)
	e2e.Eventually(t, 10*time.Second, func() error {
		var d k8s.Deployment
		if err := e2e.Get(t.Context(), c, client.Path("apps/v1", "deployments", ns, "w"), &d); err != nil {
			return err
		}
		if d.Labels["size"] != "3" {
			return fmt.Errorf("labels = %v", d.Labels)
		}
		w, err := widget(t, c, ns, "w")
		if err != nil {
			return err
		}
		if s := kube.FindCondition(w.Status.Conditions, "Synced"); s == nil || s.Status != kube.True {
			return fmt.Errorf("Synced = %+v", s)
		}
		return nil
	})
}

// pollVoter applies the size of each Widget as the widget's vote in the Poll
// named p, and abstains for a widget of size 0.
type pollVoter struct{}

func (pollVoter) Reconcile(ctx context.Context, w *Widget) error {
	if kube.Get[pollVotes](ctx, w.Namespace, "p") == nil {
		return nil
	}
	p := &pollVotes{Object: kube.Meta("p", nil)}
	if w.Spec.Size != 0 {
		p.Status.Votes = map[string]int{w.Name: w.Spec.Size}
	}
	kube.Apply(ctx, p)
	return nil
}

func TestApplyGivesUpStatusAfterRestart(t *testing.T) {
	c := e2e.Client(t)
	ns := e2e.Namespace(t, c)
	const rbac = "rbac.authorization.k8s.io/v1"
	role := ns + "-poll-voter"
	poll := client.Path(group+"/v1", "polls", ns, "p")
	remove(t, c, client.Path(group+"/v1", "widgets", ns, "w"), poll,
		client.Path(rbac, "clusterrolebindings", "", role), client.Path(rbac, "clusterroles", "", role))
	// grant lets the service account poll-voter manage CRDs and the given
	// resources in the e2e group.
	grant := func(resources ...string) {
		t.Helper()
		if err := c.Apply(t.Context(), client.Path(rbac, "clusterroles", "", role), "e2e", true, map[string]any{
			"apiVersion": rbac, "kind": "ClusterRole", "metadata": map[string]any{"name": role}, "rules": []any{
				map[string]any{"apiGroups": []string{"apiextensions.k8s.io"}, "resources": []string{"*"}, "verbs": []string{"*"}},
				map[string]any{"apiGroups": []string{group}, "resources": resources, "verbs": []string{"*"}},
			},
		}, nil); err != nil {
			t.Fatal(err)
		}
	}
	grant("widgets", "widgets/status", "polls")
	for _, o := range []struct {
		path string
		obj  map[string]any
	}{
		{client.Path("v1", "serviceaccounts", ns, ""), map[string]any{"apiVersion": "v1", "kind": "ServiceAccount", "metadata": map[string]any{"name": "poll-voter"}}},
		{client.Path(rbac, "clusterrolebindings", "", ""), map[string]any{"apiVersion": rbac, "kind": "ClusterRoleBinding", "metadata": map[string]any{"name": role},
			"roleRef":  map[string]any{"apiGroup": "rbac.authorization.k8s.io", "kind": "ClusterRole", "name": role},
			"subjects": []any{map[string]any{"kind": "ServiceAccount", "name": "poll-voter", "namespace": ns}},
		}},
	} {
		if err := c.Create(t.Context(), o.path, o.obj, nil); err != nil {
			t.Fatal(err)
		}
	}
	kubeconfig := serviceAccountKubeconfig(t, c, ns, "poll-voter")

	type managedFields struct {
		Manager     string `json:"manager"`
		Subresource string `json:"subresource"`
	}
	type pollState struct {
		Metadata struct {
			ManagedFields []managedFields `json:"managedFields"`
		} `json:"metadata"`
		Status struct {
			Votes map[string]int `json:"votes"`
		} `json:"status"`
	}
	manager := "poll-voter/" + ns + "/w"
	// state checks the poll's votes, whether the voter owns status fields,
	// and the widget's Synced condition.
	state := func(votes map[string]int, owns bool, synced, message string) func() error {
		return func() error {
			var p pollState
			if err := e2e.Get(t.Context(), c, poll, &p); err != nil {
				return err
			}
			if !maps.Equal(p.Status.Votes, votes) {
				return fmt.Errorf("votes = %v, want %v", p.Status.Votes, votes)
			}
			if got := slices.ContainsFunc(p.Metadata.ManagedFields, func(e managedFields) bool {
				return e.Manager == manager && e.Subresource == "status"
			}); got != owns {
				return fmt.Errorf("%s owns status fields: %v, want %v", manager, got, owns)
			}
			w, err := widget(t, c, ns, "w")
			if err != nil {
				return err
			}
			if s := kube.FindCondition(w.Status.Conditions, "Synced"); s == nil || s.Status != synced || !strings.Contains(s.Message, message) {
				return fmt.Errorf("Synced = %+v", s)
			}
			return nil
		}
	}

	t.Log("A voter with every permission votes.")
	stop := release(t, &kube.Manager{Name: "poll-voter-e2e", Namespace: ns}, kube.For[Poll](&tally{}, kube.Named("poll-tally")), kube.For[Widget](pollVoter{}, kube.Named("poll-voter")))
	e2e.Eventually(t, 30*time.Second, func() error {
		return c.Create(t.Context(), client.Path(group+"/v1", "polls", ns, ""), map[string]any{
			"apiVersion": group + "/v1", "kind": "Poll", "metadata": map[string]any{"name": "p"}, "spec": map[string]any{"question": "Tabs?"},
		}, nil)
	})
	createWidget(t, c, ns, "w", 3)
	e2e.Eventually(t, 10*time.Second, state(map[string]int{"w": 3}, true, kube.True, ""))
	if err := stop(); err != nil {
		t.Fatal(err)
	}

	t.Log("Restarted without permission to patch the status, the voter fails to withdraw its vote.")
	if err := c.Patch(t.Context(), client.Path(group+"/v1", "widgets", ns, "w"), client.MergePatch, nil, []byte(`{"spec":{"size":0}}`), nil); err != nil {
		t.Fatal(err)
	}
	cfg, err := client.LoadKubeconfig([]string{kubeconfig}, "")
	if err != nil {
		t.Fatal(err)
	}
	sa, err := client.New(cfg, "e2e")
	if err != nil {
		t.Fatal(err)
	}
	// The API server's authorizer sees a new binding a moment after it's
	// created.
	e2e.Eventually(t, 30*time.Second, func() error {
		return sa.Get(t.Context(), poll, &map[string]any{})
	})
	e2e.Run(t, &kube.Manager{Name: "poll-voter-e2e", Namespace: ns, Kubeconfig: kubeconfig}, kube.For[Widget](pollVoter{}, kube.Named("poll-voter")))
	e2e.Eventually(t, 10*time.Second, state(map[string]int{"w": 3}, true, kube.False, `cannot patch resource "polls/status"`))

	t.Log("Once allowed to patch the status, the voter withdraws its vote and owns no status fields.")
	grant("widgets", "widgets/status", "polls", "polls/status")
	e2e.Eventually(t, 30*time.Second, state(nil, false, kube.True, ""))
}

// failingVoter votes like pollVoter, and labels the ConfigMap named target
// with the widget's name and vote. The name label shows that a reconcile
// applied both objects, even one that abstains. For a widget with the
// annotation fail, it then applies a ConfigMap with an invalid label, so the
// reconcile fails after the vote and the labels are applied.
type failingVoter struct{}

func (failingVoter) Reconcile(ctx context.Context, w *Widget) error {
	if kube.Get[pollVotes](ctx, w.Namespace, "p") == nil || kube.Get[k8s.ConfigMap](ctx, w.Namespace, "target") == nil {
		return nil
	}
	p := &pollVotes{Object: kube.Meta("p", nil)}
	labels := map[string]string{"voter": w.Name}
	if w.Spec.Size != 0 {
		p.Status.Votes = map[string]int{w.Name: w.Spec.Size}
		labels["vote"] = strconv.Itoa(w.Spec.Size)
	}
	kube.Apply(ctx, p)
	kube.Apply(ctx, &k8s.ConfigMap{Object: kube.Meta("target", labels)})
	if w.Annotations["fail"] != "" {
		kube.Apply(ctx, &k8s.ConfigMap{Object: kube.Meta(w.Name+"-bad", map[string]string{"bad": "not valid!"})})
	}
	return nil
}

func TestApplyGivesUpWhatAFailedReconcileApplied(t *testing.T) {
	c := e2e.Client(t)
	ns := e2e.Namespace(t, c)
	poll := client.Path(group+"/v1", "polls", ns, "p")
	target := client.Path("v1", "configmaps", ns, "target")
	remove(t, c, client.Path(group+"/v1", "widgets", ns, "w"), poll, target)
	for _, name := range []string{"target", "w-bad"} {
		if err := c.Create(t.Context(), client.Path("v1", "configmaps", ns, ""), map[string]any{
			"apiVersion": "v1", "kind": "ConfigMap", "metadata": map[string]any{"name": name},
		}, nil); err != nil {
			t.Fatal(err)
		}
	}
	e2e.Run(t, &kube.Manager{Name: "failing-voter-e2e", Namespace: ns}, kube.For[Poll](&tally{}, kube.Named("failing-tally")), kube.For[Widget](failingVoter{}, kube.Named("failing-voter")))
	e2e.Eventually(t, 30*time.Second, func() error {
		return c.Create(t.Context(), client.Path(group+"/v1", "polls", ns, ""), map[string]any{
			"apiVersion": group + "/v1", "kind": "Poll", "metadata": map[string]any{"name": "p"}, "spec": map[string]any{"question": "Tabs?"},
		}, nil)
	})
	patch := func(body string) {
		t.Helper()
		if err := c.Patch(t.Context(), client.Path(group+"/v1", "widgets", ns, "w"), client.MergePatch, nil, []byte(body), nil); err != nil {
			t.Fatal(err)
		}
	}
	// state checks the poll's votes, target's labels, and the widget's
	// Synced condition for its current generation.
	state := func(vote int, synced, message string) func() error {
		return func() error {
			var p pollVotes
			if err := e2e.Get(t.Context(), c, poll, &p); err != nil {
				return err
			}
			var cm k8s.ConfigMap
			if err := e2e.Get(t.Context(), c, target, &cm); err != nil {
				return err
			}
			votes, label := map[string]int{}, ""
			if vote != 0 {
				votes, label = map[string]int{"w": vote}, strconv.Itoa(vote)
			}
			if !maps.Equal(p.Status.Votes, votes) || cm.Labels["voter"] != "w" || cm.Labels["vote"] != label {
				return fmt.Errorf("votes = %v and labels = %v, want votes %v and vote label %q", p.Status.Votes, cm.Labels, votes, label)
			}
			w, err := widget(t, c, ns, "w")
			if err != nil {
				return err
			}
			if s := kube.FindCondition(w.Status.Conditions, "Synced"); s == nil || s.Status != synced || s.ObservedGeneration != w.Generation || !strings.Contains(s.Message, message) {
				return fmt.Errorf("Synced = %+v at generation %d", s, w.Generation)
			}
			return nil
		}
	}

	t.Log("A widget of size 0 abstains.")
	createWidget(t, c, ns, "w", 0)
	e2e.Eventually(t, 30*time.Second, state(0, kube.True, ""))

	t.Log("A reconcile that votes and labels, then fails, leaves the vote and the label.")
	patch(`{"metadata":{"annotations":{"fail":"yes"}},"spec":{"size":3}}`)
	e2e.Eventually(t, 10*time.Second, state(3, kube.False, "w-bad"))

	t.Log("The next reconcile abstains, so it withdraws the vote and removes the label.")
	patch(`{"metadata":{"annotations":{"fail":null}},"spec":{"size":0}}`)
	e2e.Eventually(t, 10*time.Second, state(0, kube.True, ""))
}

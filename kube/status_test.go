package kube

import (
	"encoding/json"
	"fmt"
	"log/slog"
	"maps"
	"net/http"
	"net/http/httptest"
	"net/url"
	"slices"
	"strings"
	"sync"
	"testing"

	"github.com/imjasonh/playground/kube/internal/client"
)

// deploymentStatus declares only a Deployment's conditions.
type deploymentStatus struct {
	Object `kube:"apiVersion=apps/v1,kind=Deployment"`
	Status struct {
		Conditions []Condition `json:"conditions,omitempty"`
	} `json:"status,omitzero"`
}

// noteMap is a ConfigMap type with a status, which ConfigMaps don't serve.
type noteMap struct {
	Object `kube:"apiVersion=v1,kind=ConfigMap,plural=configmaps,scope=Namespaced"`
	Status struct {
		Note string `json:"note,omitempty"`
	} `json:"status,omitzero"`
}

func checked() []Condition {
	var conds []Condition
	SetCondition(&conds, Condition{Type: "Checked", Status: True, Reason: "Passed"})
	return conds
}

func TestFakeAppliesStatus(t *testing.T) {
	parent := &widget{}
	parent.Namespace, parent.Name = "shop", "w1"
	ctx, rec := Fake(t.Context(), parent)
	d := &deploymentStatus{Object: Meta("web", nil)}
	d.Status.Conditions = checked()
	Apply(ctx, d)
	Apply(ctx, &deploymentProjection{Object: Meta("api", nil)})
	other := &widget{Object: Meta("w2", nil)}
	other.Status.Conditions = checked()
	Apply(ctx, other)
	Apply(ctx, &widget{Object: Meta("w1", nil)})
	if err := rec.Err(); err != nil {
		t.Fatalf("Err = %v", err)
	}
	if got := Applied[deploymentStatus](rec); len(got) != 1 || FindCondition(got[0].Status.Conditions, "Checked") == nil {
		t.Errorf("Applied = %+v, want the Deployment with its status", got)
	}
	statuses := map[string]bool{}
	for _, in := range rec.s.intents {
		statuses[metaOfAny(in.obj).Name] = in.status
	}
	// The framework writes the status of w1, the object being reconciled.
	if want := map[string]bool{"web": true, "api": false, "w2": true, "w1": false}; !maps.Equal(statuses, want) {
		t.Errorf("applies status = %v, want %v", statuses, want)
	}

	ctx, rec = Fake(t.Context(), parent)
	self := &widget{Object: Meta("w1", nil)}
	self.Status.Conditions = checked()
	Apply(ctx, self)
	if err := rec.Err(); err == nil || !strings.Contains(err.Error(), "is the object being reconciled") {
		t.Errorf("Err = %v, want an error for a status applied to the object being reconciled", err)
	}
	if got := Applied[widget](rec); len(got) != 0 {
		t.Errorf("Applied = %+v, want none", got)
	}

	view := &deploymentProjection{Object: Meta("web", nil)}
	view.Namespace = "shop"
	ctx, rec = Fake(t.Context(), view)
	d = &deploymentStatus{Object: Meta("web", nil)}
	d.Status.Conditions = checked()
	Apply(ctx, d)
	if err := rec.Err(); err != nil || len(rec.s.intents) != 1 || !rec.s.intents[0].status {
		t.Errorf("Err = %v, intents = %+v; a reconciled type without a status should apply the status of its object", err, rec.s.intents)
	}
}

func TestStatusBody(t *testing.T) {
	ti, _ := typeInfoFor[deploymentStatus, *deploymentStatus]()
	target := &deploymentStatus{Object: Meta("web", map[string]string{"app": "web"})}
	target.Namespace = "shop"
	target.Status.Conditions = checked()
	observed := &deploymentStatus{Object: Meta("web", nil)}
	observed.UID = "target-uid"
	body, empty, err := statusBody(intent{kind: intentApply, ti: ti, obj: target, observed: observed})
	if err != nil {
		t.Fatal(err)
	}
	if empty || body["apiVersion"] != "apps/v1" || body["kind"] != "Deployment" {
		t.Errorf("body = %v, empty = %v", body, empty)
	}
	if meta, want := body["metadata"].(map[string]any), map[string]any{"name": "web", "namespace": "shop", "uid": "target-uid"}; !maps.Equal(meta, want) {
		t.Errorf("metadata = %v, want %v", meta, want)
	}
	if conds, _ := body["status"].(map[string]any)["conditions"].([]any); len(conds) != 1 || conds[0].(map[string]any)["type"] != "Checked" {
		t.Errorf("status = %v", body["status"])
	}

	target.Status.Conditions = nil
	target.UID = "own-uid"
	body, empty, _ = statusBody(intent{kind: intentApply, ti: ti, obj: target, observed: observed})
	if _, ok := body["status"]; ok || !empty {
		t.Errorf("body = %v, empty = %v, want no status", body, empty)
	}
	if uid := body["metadata"].(map[string]any)["uid"]; uid != "own-uid" {
		t.Errorf("uid = %v, want the desired object's", uid)
	}
}

// statusAPI serves discovery for Deployments, which have a status
// subresource, and ConfigMaps, which don't, and records patches.
type statusAPI struct {
	mu        sync.Mutex
	discovery int
	patches   []statusPatch
}

type statusPatch struct {
	path  string
	query url.Values
	body  map[string]any
}

func (a *statusAPI) ServeHTTP(w http.ResponseWriter, r *http.Request) {
	a.mu.Lock()
	defer a.mu.Unlock()
	switch {
	case r.URL.Path == "/apis/apps/v1":
		a.discovery++
		fmt.Fprint(w, `{"resources":[{"name":"deployments","namespaced":true,"kind":"Deployment"},{"name":"deployments/status","namespaced":true,"kind":"Deployment"}]}`)
	case r.URL.Path == "/api/v1":
		a.discovery++
		fmt.Fprint(w, `{"resources":[{"name":"configmaps","namespaced":true,"kind":"ConfigMap"}]}`)
	case r.Method == http.MethodPatch:
		var body map[string]any
		if err := json.NewDecoder(r.Body).Decode(&body); err != nil {
			http.Error(w, err.Error(), http.StatusBadRequest)
			return
		}
		a.patches = append(a.patches, statusPatch{path: r.URL.Path, query: r.URL.Query(), body: body})
		fmt.Fprint(w, "{}")
	default:
		http.NotFound(w, r)
	}
}

func (a *statusAPI) sent() []statusPatch {
	a.mu.Lock()
	defer a.mu.Unlock()
	return slices.Clone(a.patches)
}

func (a *statusAPI) discoveries() int {
	a.mu.Lock()
	defer a.mu.Unlock()
	return a.discovery
}

func TestApplyStatus(t *testing.T) {
	api := &statusAPI{}
	srv := httptest.NewServer(api)
	t.Cleanup(srv.Close)
	cl, err := client.New(&client.Config{Host: srv.URL}, "test")
	if err != nil {
		t.Fatal(err)
	}
	m := &Manager{client: cl, log: slog.New(slog.DiscardHandler), metrics: newMetrics()}
	c := &controller[widget, *widget]{core: core{name: "checks", log: m.log}, m: m}
	parent := Key{Namespace: "shop", Name: "w1"}
	const manager = "checks/shop/w1"
	// reconcile applies the status of one Apply intent, the way execute does.
	reconcile := func(in intent) error {
		t.Helper()
		applied := map[appliedKey]uint64{}
		if err := c.applyStatus(t.Context(), parent, in, manager, applied); err != nil {
			return err
		}
		c.setApplied(parent, applied)
		return nil
	}
	dti, _ := typeInfoFor[deploymentStatus, *deploymentStatus]()
	deployments := resolved{apiVersion: "apps/v1", plural: "deployments", namespaced: true}
	desired := &deploymentStatus{Object: Meta("web", nil)}
	desired.Namespace = "shop"
	desired.Status.Conditions = checked()
	observed := &deploymentStatus{Object: Meta("web", nil)}
	observed.Namespace, observed.UID, observed.APIVersion, observed.Kind = "shop", "target-uid", "apps/v1", "Deployment"
	in := intent{kind: intentApply, ti: dti, res: deployments, obj: desired, observed: observed, status: true}
	sends := func(want int) {
		t.Helper()
		if got := len(api.sent()); got != want {
			t.Fatalf("sent %d status applies, want %d", got, want)
		}
	}

	if err := reconcile(in); err != nil {
		t.Fatal(err)
	}
	sends(1)
	p := api.sent()[0]
	if p.path != "/apis/apps/v1/namespaces/shop/deployments/web/status" || p.query.Get("fieldManager") != manager || p.query.Get("force") != "true" {
		t.Errorf("sent %s?%s", p.path, p.query.Encode())
	}
	if conds, _ := p.body["status"].(map[string]any)["conditions"].([]any); len(conds) != 1 || p.body["metadata"].(map[string]any)["uid"] != "target-uid" {
		t.Errorf("sent %v", p.body)
	}

	t.Log("Once the cache has the status, the same status needs no request.")
	observed.Status.Conditions = desired.Status.Conditions
	if err := reconcile(in); err != nil {
		t.Fatal(err)
	}
	sends(1)

	t.Log("A status that someone else changed is applied again.")
	observed.Status.Conditions = nil
	if err := reconcile(in); err != nil {
		t.Fatal(err)
	}
	sends(2)

	t.Log("An empty status gives up the manager's status fields, once.")
	desired.Status.Conditions = nil
	observed.Status.Conditions = checked()
	for range 2 {
		if err := reconcile(in); err != nil {
			t.Fatal(err)
		}
	}
	sends(3)
	if _, ok := api.sent()[2].body["status"]; ok {
		t.Errorf("sent %v, want no status", api.sent()[2].body)
	}
	applies := func(wantApplied, wantSkipped float64) {
		t.Helper()
		counts := m.metrics.counters["kube_apply_total"]
		if applied, skipped := counts[`controller="checks",result="applied"`], counts[`controller="checks",result="skipped"`]; applied != wantApplied || skipped != wantSkipped {
			t.Errorf("kube_apply_total: applied = %v, skipped = %v, want %v and %v", applied, skipped, wantApplied, wantSkipped)
		}
	}
	applies(3, 2)

	t.Log("A type whose resource has no status subresource skips an empty status and fails for any other.")
	nti, _ := typeInfoFor[noteMap, *noteMap]()
	configMaps := resolved{apiVersion: "v1", plural: "configmaps", namespaced: true}
	note := &noteMap{Object: Meta("settings", nil)}
	note.Namespace = "shop"
	in = intent{kind: intentApply, ti: nti, res: configMaps, obj: note, status: true}
	if err := reconcile(in); err != nil {
		t.Fatal(err)
	}
	before := api.discoveries()
	if err := reconcile(in); err != nil {
		t.Fatal(err)
	}
	if got := api.discoveries() - before; got != 0 {
		t.Errorf("an empty status that was already skipped made %d discovery requests", got)
	}
	applies(3, 4)
	note.Status.Note = "hello"
	if err := reconcile(in); err == nil || !strings.Contains(err.Error(), "doesn't serve configmaps/status") {
		t.Errorf("err = %v, want an error that names the missing subresource", err)
	}
	sends(3)

	t.Log("An intent without a status sends nothing.")
	in.status = false
	if err := reconcile(in); err != nil {
		t.Fatal(err)
	}
	sends(3)
}

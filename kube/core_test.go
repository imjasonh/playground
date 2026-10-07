package kube

import (
	"context"
	"errors"
	"reflect"
	"slices"
	"strings"
	"testing"
	"time"
	"unsafe"

	"github.com/imjasonh/playground/kube/internal/queue"
)

func TestSelectors(t *testing.T) {
	labels := map[string]string{"app": "web", "tier": "frontend", "env": "prod"}
	for _, tc := range []struct {
		sel  string
		want bool
	}{
		{"", true},
		{"app=web", true},
		{"app==web,tier=frontend", true},
		{"app=api", false},
		{"app!=api", true},
		{"missing!=x", true},
		{"env in (prod, staging)", true},
		{"env notin (prod)", false},
		{"env in (dev),app=web", false},
		{"app", true},
		{"!app", false},
		{"!canary", true},
	} {
		s, err := parseSelector(tc.sel)
		if err != nil {
			t.Fatalf("parseSelector(%q): %v", tc.sel, err)
		}
		if got := s.matches(labels); got != tc.want {
			t.Errorf("%q matches = %v, want %v", tc.sel, got, tc.want)
		}
	}
	s, _ := parseSelector("tier in (b,a), app=web , !x")
	if got := s.String(); got != "!x,app=web,tier in (a,b)" {
		t.Errorf("canonical form = %q", got)
	}
	if got := selectorFromMap(map[string]string{"b": "2", "a": "1"}).String(); got != "a=1,b=2" {
		t.Errorf("selectorFromMap = %q", got)
	}
	for _, bad := range []string{"a b=c", "=x", "(a)"} {
		if _, err := parseSelector(bad); err == nil {
			t.Errorf("parseSelector(%q) succeeded", bad)
		}
	}
}

type widget struct {
	Object `kube:"group=example.dev,shortName=w,category=all"`
	Spec   struct {
		Size int `json:"size"`
	} `json:"spec"`
	Status struct {
		ObservedGeneration int64       `json:"observedGeneration,omitempty"`
		Conditions         []Condition `json:"conditions,omitempty"`
	} `json:"status,omitzero"`
}

type policy struct {
	Object `kube:"group=example.dev,kind=NetworkPolicy,scope=Cluster"`
}

type podMeta struct {
	Object `kube:"apiVersion=v1,kind=Pod"`
}

type deploymentProjection struct {
	Object `kube:"apiVersion=apps/v1,kind=Deployment"`
	Spec   struct {
		Replicas *int32 `json:"replicas,omitempty"`
	} `json:"spec"`
}

type localConfigMap struct {
	Object `kube:"apiVersion=v1,kind=ConfigMap,local"`
	Data   map[string]string `json:"data,omitempty"`
}

func TestTypeInfo(t *testing.T) {
	ti, err := typeInfoFor[widget, *widget]()
	if err != nil {
		t.Fatal(err)
	}
	if ti.apiVersion != "example.dev/v1" || ti.kind != "widget" || ti.plural != "widgets" || ti.scope != "Namespaced" || !ti.custom {
		t.Errorf("widget = %+v", ti)
	}
	if !slices.Equal(ti.shortNames, []string{"w"}) || !slices.Equal(ti.categories, []string{"all"}) {
		t.Errorf("names = %v %v", ti.shortNames, ti.categories)
	}
	if ti.status == nil || ti.conditions == nil || ti.observedGeneration == nil || ti.metadataOnly {
		t.Errorf("status fields = %+v", ti)
	}
	if ti, _ := typeInfoFor[policy, *policy](); ti.plural != "networkpolicies" || ti.scope != "Cluster" || !ti.metadataOnly {
		t.Errorf("policy = %+v", ti)
	}
	if ti, _ := typeInfoFor[podMeta, *podMeta](); ti.apiVersion != "v1" || ti.group != "" || ti.custom || ti.plural != "" || !ti.metadataOnly {
		t.Errorf("podMeta = %+v", ti)
	}
	if ti, _ := typeInfoFor[deploymentProjection, *deploymentProjection](); ti.group != "apps" || ti.version != "v1" || ti.metadataOnly || ti.status != nil {
		t.Errorf("deploymentProjection = %+v", ti)
	}
	if ti, _ := typeInfoFor[localConfigMap, *localConfigMap](); !ti.local || ti.scope != "Namespaced" || ti.custom {
		t.Errorf("localConfigMap = %+v", ti)
	}
	if ti, _ := typeInfoFor[podMeta, *podMeta](); ti.local {
		t.Errorf("podMeta is local")
	}
}

type noObject struct{ Name string }
type untagged struct{ Object }
type badGroup struct {
	Object `kube:"group=nodot"`
}
type bothVersions struct {
	Object `kube:"group=example.dev,apiVersion=v1"`
}
type badOption struct {
	Object `kube:"group=example.dev,colour=red"`
}
type localCluster struct {
	Object `kube:"group=example.dev,scope=Cluster,local"`
}

func TestTypeInfoErrors(t *testing.T) {
	for _, tc := range []struct {
		err  error
		want string
	}{
		{second(parseType(reflect.TypeFor[noObject]())), "doesn't embed kube.Object"},
		{second(typeInfoFor[untagged, *untagged]()), "needs a kube struct tag"},
		{second(typeInfoFor[badGroup, *badGroup]()), "must be a domain name"},
		{second(typeInfoFor[bothVersions, *bothVersions]()), "not both"},
		{second(typeInfoFor[badOption, *badOption]()), "unknown tag option"},
		{second(typeInfoFor[localCluster, *localCluster]()), "can't have scope=Cluster"},
	} {
		if tc.err == nil || !strings.Contains(tc.err.Error(), tc.want) {
			t.Errorf("err = %v, want %q", tc.err, tc.want)
		}
	}
}

func second[A, B any](_ A, b B) B { return b }

func TestPluralize(t *testing.T) {
	for in, want := range map[string]string{"Website": "websites", "Policy": "policies", "Gateway": "gateways", "Ingress": "ingresses", "Box": "boxes", "Batch": "batches", "Mesh": "meshes"} {
		if got := pluralize(in); got != want {
			t.Errorf("pluralize(%q) = %q, want %q", in, got, want)
		}
	}
}

func cm(ns, name, rv string, labels map[string]string, owner string) *widget {
	w := &widget{}
	w.Namespace, w.Name, w.ResourceVersion, w.Labels = ns, name, rv, labels
	if owner != "" {
		w.Annotations = map[string]string{"x/owner": owner}
	}
	return w
}

func TestStore(t *testing.T) {
	var s store[widget, *widget]
	s.ownerKey = "x/owner"
	s.put(cm("a", "one", "1", nil, "a/parent"))
	s.put(cm("a", "two", "1", nil, "a/parent"))
	s.put(cm("b", "one", "1", nil, ""))
	if s.len() != 3 || s.get(Key{"a", "one"}) == nil || s.get(Key{"c", "one"}) != nil {
		t.Fatalf("store = %d objects", s.len())
	}
	if got := len(s.byOwner("a/parent")); got != 2 {
		t.Errorf("byOwner = %d, want 2", got)
	}
	n := 0
	s.each("a", func(*widget) bool { n++; return true })
	if n != 2 {
		t.Errorf("each(a) visited %d", n)
	}

	changes := s.replace(map[Key]*widget{
		{"a", "one"}:   cm("a", "one", "1", nil, "a/parent"),
		{"a", "two"}:   cm("a", "two", "2", nil, ""),
		{"c", "three"}: cm("c", "three", "1", nil, ""),
	})
	var got []string
	for _, c := range changes {
		switch {
		case c.old == nil:
			got = append(got, "add "+c.new.Key().String())
		case c.new == nil:
			got = append(got, "delete "+c.old.Key().String())
		default:
			got = append(got, "update "+c.new.Key().String())
		}
	}
	slices.Sort(got)
	if want := []string{"add c/three", "delete b/one", "update a/two"}; !slices.Equal(got, want) {
		t.Errorf("replace changes = %v, want %v", got, want)
	}
	if got := len(s.byOwner("a/parent")); got != 1 {
		t.Errorf("after replace, byOwner = %d, want 1", got)
	}
	if old := s.remove(cm("a", "one", "2", nil, "a/parent")); old == nil || len(s.byOwner("a/parent")) != 0 {
		t.Error("remove didn't unindex")
	}
}

func TestIntern(t *testing.T) {
	a := &ObjectMeta{Namespace: strings.Clone("default"), Labels: map[string]string{strings.Clone("app"): strings.Clone("web")}}
	b := &ObjectMeta{Namespace: strings.Clone("default"), Labels: map[string]string{strings.Clone("app"): strings.Clone("web")}}
	intern(a)
	intern(b)
	if a.Namespace != "default" || a.Labels["app"] != "web" {
		t.Fatalf("intern changed values: %+v", a)
	}
	if unsafeData(a.Namespace) != unsafeData(b.Namespace) || unsafeData(a.Labels["app"]) != unsafeData(b.Labels["app"]) {
		t.Error("interned strings don't share memory")
	}
}

func unsafeData(s string) *byte { return unsafe.StringData(s) }

type recordingQueue struct{ keys []Key }

func (r *recordingQueue) enqueue(k Key, _ queue.Priority) { r.keys = append(r.keys, k) }

func TestTrackerNameDeps(t *testing.T) {
	tr := newTracker()
	q := &recordingQueue{}
	site := ref{c: q, key: Key{"default", "blog"}}
	tr.add(site, dep{src: 1, ns: "default", name: "config"}, nil)
	tr.changed(1, nil, &ObjectMeta{Namespace: "default", Name: "config"})
	tr.changed(1, nil, &ObjectMeta{Namespace: "default", Name: "other"})
	tr.changed(2, nil, &ObjectMeta{Namespace: "default", Name: "config"})
	if !slices.Equal(q.keys, []Key{{"default", "blog"}}) {
		t.Errorf("enqueued %v", q.keys)
	}
	tr.retain(site, map[dep]struct{}{})
	tr.changed(1, nil, &ObjectMeta{Namespace: "default", Name: "config"})
	if len(q.keys) != 1 || tr.size() != 0 {
		t.Errorf("after retain(nil): enqueued %v, size %d", q.keys, tr.size())
	}
}

func TestTrackerListDeps(t *testing.T) {
	tr := newTracker()
	q := &recordingQueue{}
	sel, _ := parseSelector("team=web")
	inNS := ref{c: q, key: Key{"infra", "a"}}
	cluster := ref{c: q, key: Key{"infra", "b"}}
	tr.add(inNS, dep{src: 1, ns: "shop", sel: sel.String(), list: true}, sel)
	tr.add(cluster, dep{src: 1, sel: sel.String(), list: true}, sel)

	web := &ObjectMeta{Namespace: "shop", Name: "x", Labels: map[string]string{"team": "web"}}
	db := &ObjectMeta{Namespace: "shop", Name: "x", Labels: map[string]string{"team": "db"}}
	elsewhere := &ObjectMeta{Namespace: "other", Name: "y", Labels: map[string]string{"team": "web"}}

	tr.changed(1, nil, web)
	if len(q.keys) != 2 {
		t.Errorf("matching add enqueued %v, want both", q.keys)
	}
	q.keys = nil
	tr.changed(1, web, db)
	if len(q.keys) != 2 {
		t.Errorf("leaving the selector enqueued %v, want both", q.keys)
	}
	q.keys = nil
	tr.changed(1, db, db)
	if len(q.keys) != 0 {
		t.Errorf("non-matching change enqueued %v", q.keys)
	}
	tr.changed(1, nil, elsewhere)
	if !slices.Equal(q.keys, []Key{{"infra", "b"}}) {
		t.Errorf("other namespace enqueued %v, want only the cluster-wide reader", q.keys)
	}
}

func TestSetCondition(t *testing.T) {
	var conds []Condition
	SetCondition(&conds, Condition{Type: "Ready", Status: False, Reason: "Starting"})
	first := conds[0].LastTransitionTime
	if first.IsZero() || first.Nanosecond() != 0 {
		t.Fatalf("LastTransitionTime = %v, want now at second precision", first)
	}
	SetCondition(&conds, Condition{Type: "Ready", Status: False, Reason: "StillStarting"})
	if conds[0].LastTransitionTime != first || conds[0].Reason != "StillStarting" {
		t.Errorf("same status changed the transition time or kept the old reason: %+v", conds[0])
	}
	conds[0].LastTransitionTime = first.Add(-time.Hour)
	SetCondition(&conds, Condition{Type: "Ready", Status: True})
	if !conds[0].LastTransitionTime.After(first.Add(-time.Hour)) {
		t.Error("status change kept the old transition time")
	}
	SetCondition(&conds, Condition{Type: "Synced", Status: True})
	if len(conds) != 2 || FindCondition(conds, "Synced") == nil || FindCondition(conds, "Nope") != nil {
		t.Errorf("conds = %+v", conds)
	}
}

func TestSyncedCondition(t *testing.T) {
	c := syncedCondition(nil, 3)
	if c.Status != True || c.ObservedGeneration != 3 {
		t.Errorf("success = %+v", c)
	}
	c = syncedCondition(Permanent(errorString("bad spec\nmore detail")), 3)
	if c.Status != False || c.Reason != "PermanentError" || c.Message != "bad spec" {
		t.Errorf("permanent = %+v", c)
	}
	c = syncedCondition(errorString(strings.Repeat("x", 2000)), 3)
	if c.Reason != "ReconcileError" || len(c.Message) != 1024 {
		t.Errorf("long error: reason %q, message length %d", c.Reason, len(c.Message))
	}
}

type errorString string

func (e errorString) Error() string { return string(e) }

func TestSpecChangedIgnoresStatusAndResourceVersion(t *testing.T) {
	ti, _ := typeInfoFor[widget, *widget]()
	c := &controller[widget, *widget]{core: core{ti: ti}}
	old := &widget{}
	old.ResourceVersion, old.Spec.Size = "1", 1
	same := *old
	same.ResourceVersion = "2"
	same.Status.ObservedGeneration = 5
	if c.specChanged(old, &same) {
		t.Error("a status and resource version change counted as a change")
	}
	grown := same
	grown.Spec.Size = 2
	labeled := same
	labeled.Labels = map[string]string{"a": "b"}
	deleting := same
	deleting.DeletionTimestamp = &time.Time{}
	for name, w := range map[string]*widget{"spec": &grown, "labels": &labeled, "deletion": &deleting} {
		if !c.specChanged(old, w) {
			t.Errorf("a %s change didn't count", name)
		}
	}
	mti, _ := typeInfoFor[podMeta, *podMeta]()
	mc := &controller[podMeta, *podMeta]{core: core{ti: mti}}
	a, b := &podMeta{}, &podMeta{}
	a.ResourceVersion, b.ResourceVersion = "1", "2"
	if !mc.specChanged(a, b) {
		t.Error("for a metadata-only type, a new resource version must count")
	}
}

// Clusters store these keys on objects, and admission policies copy them, so
// a change to one is a breaking change.
func TestKeysAreStable(t *testing.T) {
	keys := newLabelKeys()
	for _, tc := range []struct{ got, want string }{
		{ControllerLabel, "kube.imjasonh.github.io/controller"},
		{OwnerUIDLabel, "kube.imjasonh.github.io/owner-uid"},
		{OwnerAnnotation, "kube.imjasonh.github.io/owner"},
		{FinalizerName("website"), "kube.imjasonh.github.io/website"},
		{keys.controller, ControllerLabel},
		{keys.ownerUID, OwnerUIDLabel},
		{keys.owner, OwnerAnnotation},
		{keys.applied, "kube.imjasonh.github.io/applied"},
		{keys.cleanup, "kube.imjasonh.github.io/cleanup"},
		{keys.managedBy, "kube.imjasonh.github.io/managed-by"},
		{keys.leaseGroup, "kube.imjasonh.github.io/lease-group"},
		{keys.leaseRole, "kube.imjasonh.github.io/lease-role"},
	} {
		if tc.got != tc.want {
			t.Errorf("key = %q, want %q", tc.got, tc.want)
		}
	}
}

func TestDefaultName(t *testing.T) {
	for _, tc := range []struct{ program, kind, want string }{
		{"shop", "Website", "shop-website"},
		{"website", "Website", "website"},
		{"", "Website", "website"},
		{"My_App", "Widget", "my-app-widget"},
		{"e2e.test", "ConfigMap", "e2e.test-configmap"},
		{"_tool.", "Widget", "tool-widget"},
	} {
		if got := defaultName(tc.program, tc.kind); got != tc.want {
			t.Errorf("defaultName(%q, %q) = %q, want %q", tc.program, tc.kind, got, tc.want)
		}
	}
	long, longer := defaultName(strings.Repeat("a", 44), "Widget"), defaultName(strings.Repeat("a", 45), "Widget")
	for _, name := range []string{long, longer} {
		if !nameRE.MatchString(name) || !strings.HasPrefix(name, strings.Repeat("a", 41)+"-") {
			t.Errorf("long default name %q, want the first 41 characters and a hash", name)
		}
	}
	if long == longer {
		t.Errorf("two long program names both default to %q", long)
	}
}

func TestDuplicateControllerNames(t *testing.T) {
	m := testManager()
	m.Name = "shop"
	first, second := For[gizmo](gizmoReconciler{}), For[gizmo](gizmoReconciler{})
	m.controllers = []Controller{first, second}
	if err := first.prepare(t.Context(), m); err != nil {
		t.Fatal(err)
	}
	if c := first.(*controller[gizmo, *gizmo]); c.name != "shop-gizmo" || c.finalizer != FinalizerName("shop-gizmo") {
		t.Errorf("name = %q, finalizer = %q, want shop-gizmo", c.name, c.finalizer)
	}
	if err := second.prepare(t.Context(), m); err == nil || !strings.Contains(err.Error(), `two controllers are named "shop-gizmo"`) || !strings.Contains(err.Error(), "kube.Named") {
		t.Errorf("err = %v, want one about two controllers named shop-gizmo", err)
	}
	named := For[gizmo](gizmoReconciler{}, Named("gizmo-sizes"))
	m.controllers = []Controller{first, named}
	if err := named.prepare(t.Context(), m); err != nil || named.controllerName() != "gizmo-sizes" {
		t.Errorf("named controller: name = %q, err = %v", named.controllerName(), err)
	}
}

func TestOwnBody(t *testing.T) {
	wti, _ := typeInfoFor[widget, *widget]()
	dti, _ := typeInfoFor[deploymentProjection, *deploymentProjection]()
	c := &controller[widget, *widget]{core: core{name: "widgets", ti: wti, res: resolved{apiVersion: "example.dev/v1", plural: "widgets", namespaced: true}, labels: newLabelKeys()}}
	parent := &widget{}
	parent.Namespace, parent.Name, parent.UID = "shop", "w1", "uid-1"

	child := &deploymentProjection{Object: Meta("w1", map[string]string{"app": "w1"})}
	child.Namespace, child.ResourceVersion, child.UID = "shop", "99", "stale"
	child.Spec.Replicas = new(int32(0))
	body, err := c.body(intent{kind: intentOwn, ti: dti, res: resolved{namespaced: true}, obj: child}, parent)
	if err != nil {
		t.Fatal(err)
	}
	meta := body["metadata"].(map[string]any)
	if _, ok := meta["resourceVersion"]; ok {
		t.Error("body has resourceVersion")
	}
	if _, ok := meta["uid"]; ok {
		t.Error("owned body has a uid")
	}
	labels := meta["labels"].(map[string]any)
	if labels["app"] != "w1" || labels[ControllerLabel] != "widgets" || labels[OwnerUIDLabel] != "uid-1" {
		t.Errorf("labels = %v", labels)
	}
	if meta["annotations"].(map[string]any)[OwnerAnnotation] != "shop/w1" {
		t.Errorf("annotations = %v", meta["annotations"])
	}
	refs := meta["ownerReferences"].([]any)
	if len(refs) != 1 || refs[0].(map[string]any)["uid"] != "uid-1" || refs[0].(map[string]any)["controller"] != true {
		t.Errorf("ownerReferences = %v", refs)
	}
	if body["spec"].(map[string]any)["replicas"] == nil {
		t.Error("an explicit zero replicas was dropped")
	}

	elsewhere := &deploymentProjection{Object: Meta("w1", nil)}
	elsewhere.Namespace = "other"
	body, _ = c.body(intent{kind: intentOwn, ti: dti, res: resolved{namespaced: true}, obj: elsewhere}, parent)
	if _, ok := body["metadata"].(map[string]any)["ownerReferences"]; ok {
		t.Error("a cross-namespace owned object got an owner reference")
	}

	target := &deploymentProjection{Object: Meta("web", nil)}
	target.Namespace = "shop"
	observed := &deploymentProjection{Object: Meta("web", nil)}
	observed.UID = "target-uid"
	body, _ = c.body(intent{kind: intentApply, ti: dti, res: resolved{namespaced: true}, obj: target, observed: observed}, parent)
	meta = body["metadata"].(map[string]any)
	if meta["uid"] != "target-uid" || meta["labels"] != nil || meta["ownerReferences"] != nil {
		t.Errorf("apply body metadata = %v", meta)
	}
}

func TestOwnRefusesAnotherOwnersObject(t *testing.T) {
	parent := &widget{}
	parent.Namespace, parent.Name = "shop", "w1"
	mine := &deploymentProjection{Object: Meta("mine", nil)}
	mine.Namespace, mine.Annotations = "shop", map[string]string{OwnerAnnotation: "shop/w1"}
	theirs := &deploymentProjection{Object: Meta("theirs", nil)}
	theirs.Namespace, theirs.Annotations = "shop", map[string]string{OwnerAnnotation: "shop/w2"}
	ctx, rec := Fake(t.Context(), parent, mine, theirs)
	if Own(ctx, &deploymentProjection{Object: Meta("mine", nil)}) == nil || rec.Err() != nil {
		t.Fatalf("Own of the owner's object failed: %v", rec.Err())
	}
	if Own(ctx, &deploymentProjection{Object: Meta("theirs", nil)}) != nil {
		t.Error("Own returned another owner's object")
	}
	if err := rec.Err(); err == nil || !strings.Contains(err.Error(), "already has another owner, shop/w2") {
		t.Errorf("Err = %v, want an error that names the other owner", err)
	}
	if got := Owned[deploymentProjection](rec); len(got) != 1 || got[0].Name != "mine" {
		t.Errorf("Owned = %v, want only the owner's object", got)
	}
}

func TestMatches(t *testing.T) {
	observed := &deploymentProjection{Object: Meta("web", map[string]string{"app": "web", "extra": "x"})}
	observed.Spec.Replicas = new(int32(3))
	want, _ := toMap(&deploymentProjection{Object: Meta("web", map[string]string{"app": "web"})})
	if !matches(observed, want) {
		t.Error("subset didn't match")
	}
	want["spec"] = map[string]any{"replicas": 4}
	if matches(observed, want) {
		t.Error("different replicas matched")
	}
}

type fakeReconciler struct {
	reconcile func(ctx context.Context, w *widget) error
}

func (f fakeReconciler) Reconcile(ctx context.Context, w *widget) error { return f.reconcile(ctx, w) }

func TestFakeWorld(t *testing.T) {
	parent := &widget{}
	parent.Namespace, parent.Name = "shop", "w1"
	existing := &deploymentProjection{Object: Meta("w1", nil)}
	existing.Namespace, existing.Spec.Replicas = "shop", new(int32(2))
	b := &podMeta{Object: Meta("b", map[string]string{"app": "w1"})}
	a := &podMeta{Object: Meta("a", map[string]string{"app": "w1"})}
	other := &podMeta{Object: Meta("c", map[string]string{"app": "other"})}
	for _, p := range []*podMeta{a, b, other} {
		p.Namespace = "shop"
	}

	r := fakeReconciler{reconcile: func(ctx context.Context, w *widget) error {
		if got := Get[deploymentProjection](ctx, "shop", "missing"); got != nil {
			t.Errorf("Get(missing) = %+v", got)
		}
		pods := List[podMeta](ctx, InNamespace("shop"), MatchingLabels(map[string]string{"app": "w1"}))
		if len(pods) != 2 || pods[0].Name != "a" || pods[1].Name != "b" {
			t.Errorf("List = %v", pods)
		}
		pods[0].Labels["app"] = "mutated"
		desired := &deploymentProjection{Object: Meta("w1", nil)}
		if obs := Own(ctx, desired); obs == nil || *obs.Spec.Replicas != 2 {
			t.Errorf("Own returned %+v, want the observed object", obs)
		}
		if desired.Namespace != "shop" {
			t.Errorf("Own didn't default the namespace: %q", desired.Namespace)
		}
		Own(ctx, desired)
		RequeueAfter(ctx, time.Hour)
		RequeueAfter(ctx, time.Minute)
		return nil
	}}
	ctx, rec := Fake(t.Context(), parent, existing, a, b, other)
	if err := r.Reconcile(ctx, parent); err != nil {
		t.Fatal(err)
	}
	if a.Labels["app"] != "w1" {
		t.Error("changing a listed object changed the world")
	}
	if rec.Err() == nil || !strings.Contains(rec.Err().Error(), "declared twice") {
		t.Errorf("Err = %v, want the duplicate declaration", rec.Err())
	}
	if rec.RequeueAfter() != time.Minute {
		t.Errorf("RequeueAfter = %v", rec.RequeueAfter())
	}
	if len(Owned[deploymentProjection](rec)) != 1 {
		t.Errorf("Owned = %v", Owned[deploymentProjection](rec))
	}
}

type deploymentFull struct {
	Object `kube:"apiVersion=apps/v1,kind=Deployment"`
	Spec   struct {
		Replicas *int32 `json:"replicas,omitempty"`
		Paused   bool   `json:"paused,omitempty"`
	} `json:"spec"`
}

func TestFakeReadsEveryTypeOfAKind(t *testing.T) {
	parent := &widget{}
	parent.Namespace, parent.Name = "shop", "w1"
	two, three, four, five := int32(2), int32(3), int32(4), int32(5)
	full := &deploymentFull{Object: Meta("full", nil)}
	full.Spec.Replicas, full.Spec.Paused = &two, true
	small := &deploymentProjection{Object: Meta("small", nil)}
	small.Spec.Replicas = &three
	hidden := &deploymentFull{Object: Meta("both", nil)}
	hidden.Spec.Replicas = &four
	shown := &deploymentProjection{Object: Meta("both", nil)}
	shown.Spec.Replicas = &five
	pod := &podMeta{Object: Meta("pod", nil)}
	for _, m := range []*ObjectMeta{&full.ObjectMeta, &small.ObjectMeta, &hidden.ObjectMeta, &shown.ObjectMeta, &pod.ObjectMeta} {
		m.Namespace = "shop"
	}

	r := fakeReconciler{reconcile: func(ctx context.Context, w *widget) error {
		if d := Get[deploymentProjection](ctx, "shop", "full"); d == nil || *d.Spec.Replicas != 2 {
			t.Errorf("Get[deploymentProjection](full) = %+v, want the deploymentFull as a deploymentProjection", d)
		}
		if d := Get[deploymentFull](ctx, "shop", "small"); d == nil || *d.Spec.Replicas != 3 || d.Spec.Paused {
			t.Errorf("Get[deploymentFull](small) = %+v, want the deploymentProjection as a deploymentFull", d)
		}
		if d := Get[deploymentProjection](ctx, "shop", "both"); d == nil || *d.Spec.Replicas != 5 {
			t.Errorf("Get[deploymentProjection](both) = %+v, want the deploymentProjection, not the deploymentFull", d)
		}
		var names []string
		for _, d := range List[deploymentProjection](ctx, InNamespace("shop")) {
			names = append(names, d.Name)
		}
		if want := []string{"both", "full", "small"}; !slices.Equal(names, want) {
			t.Errorf("List[deploymentProjection] = %v, want %v", names, want)
		}
		return nil
	}}
	ctx, _ := Fake(t.Context(), parent, full, small, hidden, shown, pod)
	if err := r.Reconcile(ctx, parent); err != nil {
		t.Fatal(err)
	}
}

func TestLocalTypes(t *testing.T) {
	parent := &widget{}
	parent.Namespace, parent.Name = "shop", "w1"
	state := &localConfigMap{Object: Meta("state", nil), Data: map[string]string{"k": "v"}}
	state.Namespace = "system"
	for name, use := range map[string]func(context.Context){
		"Get":  func(ctx context.Context) { Get[localConfigMap](ctx, "system", "state") },
		"List": func(ctx context.Context) { List[localConfigMap](ctx, InNamespace("system")) },
		"Own":  func(ctx context.Context) { Own(ctx, &localConfigMap{Object: Meta("state", nil)}) },
		// The reconciled object's namespace isn't the program's, and the
		// Role doesn't cover it.
		"Apply without a namespace": func(ctx context.Context) { Apply(ctx, &localConfigMap{Object: Meta("state", nil)}) },
		"Fetch without a namespace": func(ctx context.Context) { Fetch[localConfigMap](ctx, "", "state") },
	} {
		ctx, rec := Fake(t.Context(), parent, state)
		use(ctx)
		if err := rec.Err(); !IsPermanent(err) || !strings.Contains(err.Error(), "is local") {
			t.Errorf("%s: Err = %v, want an error that says the type is local", name, err)
		}
	}

	ctx, rec := Fake(t.Context(), parent, state)
	got, err := Fetch[localConfigMap](ctx, "system", "state")
	if err != nil || got == nil || got.Data["k"] != "v" {
		t.Errorf("Fetch = %+v, %v", got, err)
	}
	desired := &localConfigMap{Object: Meta("state", nil), Data: map[string]string{"k": "w"}}
	desired.Namespace = "system"
	Apply(ctx, desired)
	old := &localConfigMap{Object: Meta("old", nil)}
	old.Namespace = "system"
	Delete(ctx, old)
	if rec.Err() != nil || len(Applied[localConfigMap](rec)) != 1 || len(Deleted[localConfigMap](rec)) != 1 {
		t.Errorf("Err = %v, Applied = %v, Deleted = %v", rec.Err(), Applied[localConfigMap](rec), Deleted[localConfigMap](rec))
	}
}

func TestVerbsOutsideReconcilePanic(t *testing.T) {
	defer func() {
		r := recover()
		if r == nil || !strings.Contains(r.(string), "outside a reconcile") {
			t.Errorf("recover() = %v", r)
		}
	}()
	Get[podMeta](t.Context(), "a", "b")
}

func TestPermanent(t *testing.T) {
	if Permanent(nil) != nil {
		t.Error("Permanent(nil) != nil")
	}
	base := errorString("bad")
	err := Permanent(base)
	if !IsPermanent(err) || IsPermanent(base) || err.Error() != "bad" {
		t.Errorf("IsPermanent: %v", err)
	}
	var target errorString
	if !errors.As(err, &target) {
		t.Error("Permanent doesn't unwrap")
	}
}

func TestFakeLastError(t *testing.T) {
	parent := &widget{}
	parent.Namespace, parent.Name = "shop", "w1"
	ctx, _ := Fake(t.Context(), parent)
	if err := LastError(ctx); err != nil {
		t.Errorf("LastError = %v, want nil", err)
	}

	denied := errorString("applying Pod.v1 shop/p: forbidden")
	pod := &podMeta{Object: Meta("p", nil)}
	pod.Namespace = "shop"
	ctx, _ = Fake(t.Context(), parent, denied, pod)
	if err := LastError(ctx); err != denied {
		t.Errorf("LastError = %v, want %v", err, denied)
	}
	if pods := List[podMeta](ctx, InNamespace("shop")); len(pods) != 1 || pods[0].Name != "p" {
		t.Errorf("List = %v, want the Pod and not the error", pods)
	}
}

func TestMetricsFormat(t *testing.T) {
	m := newMetrics()
	m.inc("kube_reconcile_total", "controller", "w", "result", "success")
	m.inc("kube_reconcile_total", "controller", "w", "result", "success")
	m.observe("kube_reconcile_duration_seconds", 0.02, "controller", "w")
	m.gauge("kube_queue_depth", "Keys waiting.", func() []sample { return []sample{{labels: []string{"controller", `a"b`}, value: 3}} })
	var b strings.Builder
	m.write(&b)
	for _, want := range []string{
		"# TYPE kube_reconcile_total counter",
		`kube_reconcile_total{controller="w",result="success"} 2`,
		`kube_reconcile_duration_seconds_bucket{controller="w",le="0.025"} 1`,
		`kube_reconcile_duration_seconds_bucket{controller="w",le="0.01"} 0`,
		`kube_reconcile_duration_seconds_count{controller="w"} 1`,
		`kube_queue_depth{controller="a\"b"} 3`,
	} {
		if !strings.Contains(b.String(), want) {
			t.Errorf("metrics output is missing %q:\n%s", want, b.String())
		}
	}
	if m.counter("kube_reconcile_total", "controller", "w", "result", "success") != 2 {
		t.Error("counter value")
	}
	var nilMetrics *metrics
	nilMetrics.inc("x")
	nilMetrics.observe("x", 1)
}

package kube

import (
	"bytes"
	"context"
	"encoding/json"
	"errors"
	"log/slog"
	"net/http"
	"net/http/httptest"
	"reflect"
	"strings"
	"testing"

	"github.com/imjasonh/playground/kube/internal/jsonpatch"
)

type gizmo struct {
	Object `kube:"group=test.kube.imjasonh.github.io,kind=Gizmo,version=v2"`
	Spec   struct {
		Replicas int    `json:"replicas"`
		Tier     string `json:"tier,omitempty"`
	} `json:"spec"`
	Status struct {
		Seen int `json:"seen,omitempty"`
	} `json:"status,omitzero"`
}

type gizmoV1 struct {
	Object `kube:"group=test.kube.imjasonh.github.io,kind=Gizmo,version=v1,deprecated"`
	Spec   struct {
		Size int `json:"size"`
	} `json:"spec"`
	Status struct {
		Seen int `json:"seen,omitempty"`
	} `json:"status,omitzero"`
}

func (g *gizmoV1) ConvertTo(h *gizmo) error {
	if g.Spec.Size < 0 {
		return errors.New("size can't be negative")
	}
	h.Spec.Replicas = g.Spec.Size
	h.Status.Seen = g.Status.Seen
	return nil
}

func (g *gizmoV1) ConvertFrom(h *gizmo) error {
	g.Spec.Size = h.Spec.Replicas
	g.Status.Seen = h.Status.Seen
	return nil
}

// gizmoV1beta1 has the same fields as v1 and no conversion methods.
type gizmoV1beta1 struct {
	Object `kube:"group=test.kube.imjasonh.github.io,kind=Gizmo,version=v1beta1"`
	Spec   struct {
		Replicas int `json:"replicas"`
	} `json:"spec"`
}

type gizmoReconciler struct{}

func (gizmoReconciler) Reconcile(context.Context, *gizmo) error { return nil }

func testManager() *Manager {
	return &Manager{log: slog.Default(), metrics: newMetrics()}
}

func TestConvert(t *testing.T) {
	m := testManager()
	c := For[gizmo](gizmoReconciler{}, Version[gizmoV1](), Version[gizmoV1beta1]()).(*controller[gizmo, *gizmo])
	if err := c.prepare(t.Context(), m); err != nil {
		t.Fatal(err)
	}
	if !c.conversion || len(c.versions) != 2 {
		t.Fatalf("conversion = %v, versions = %d", c.conversion, len(c.versions))
	}
	v1 := `{"apiVersion":"test.kube.imjasonh.github.io/v1","kind":"Gizmo",` +
		`"metadata":{"name":"g","namespace":"ns","uid":"u1","managedFields":[{"manager":"kubectl"}],"generateName":"g-"},` +
		`"spec":{"size":4},"status":{"seen":2}}`
	out, err := c.convert(json.RawMessage(v1), "test.kube.imjasonh.github.io/v2")
	if err != nil {
		t.Fatal(err)
	}
	var got map[string]any
	_ = json.Unmarshal(out, &got)
	if got["apiVersion"] != "test.kube.imjasonh.github.io/v2" || got["kind"] != "Gizmo" {
		t.Errorf("type = %v %v", got["apiVersion"], got["kind"])
	}
	if spec := got["spec"].(map[string]any); spec["replicas"] != float64(4) || spec["size"] != nil {
		t.Errorf("spec = %v", spec)
	}
	if status := got["status"].(map[string]any); status["seen"] != float64(2) {
		t.Errorf("status = %v", status)
	}
	meta := got["metadata"].(map[string]any)
	if meta["generateName"] != "g-" || meta["managedFields"] == nil || meta["uid"] != "u1" {
		t.Errorf("metadata wasn't copied as is: %v", meta)
	}

	back, err := c.convert(out, "test.kube.imjasonh.github.io/v1")
	if err != nil {
		t.Fatal(err)
	}
	var v1Back, v1Orig any
	_ = json.Unmarshal(back, &v1Back)
	_ = json.Unmarshal([]byte(v1), &v1Orig)
	if !reflect.DeepEqual(v1Back, v1Orig) {
		t.Errorf("v1 -> v2 -> v1 = %s", back)
	}

	beta, err := c.convert(out, "test.kube.imjasonh.github.io/v1beta1")
	if err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(string(beta), `"spec":{"replicas":4}`) {
		t.Errorf("v2 -> v1beta1 = %s", beta)
	}

	if _, err := c.convert(json.RawMessage(`{"apiVersion":"test.kube.imjasonh.github.io/v1","kind":"Gizmo","metadata":{},"spec":{"size":-1}}`), "test.kube.imjasonh.github.io/v2"); err == nil || !strings.Contains(err.Error(), "can't be negative") {
		t.Errorf("a failing ConvertTo returned %v", err)
	}
	if _, err := c.convert(json.RawMessage(`{"apiVersion":"test.kube.imjasonh.github.io/v9","metadata":{}}`), "test.kube.imjasonh.github.io/v2"); err == nil {
		t.Error("converting an unknown version succeeded")
	}
}

func TestVersionsWithoutConversionMethods(t *testing.T) {
	m := testManager()
	c := For[gizmo](gizmoReconciler{}, Version[gizmoV1beta1]()).(*controller[gizmo, *gizmo])
	if err := c.prepare(t.Context(), m); err != nil {
		t.Fatal(err)
	}
	if c.conversion {
		t.Error("versions without conversion methods need a webhook")
	}
	if got := c.crd().conversion["strategy"]; got != "None" {
		t.Errorf("strategy = %v, want None", got)
	}
	if m.needsWebhooks() {
		t.Error("the manager needs webhooks without any conversion methods")
	}
}

// gizmoV1alpha1 is a retired version.
type gizmoV1alpha1 struct {
	Object `kube:"group=test.kube.imjasonh.github.io,kind=Gizmo,version=v1alpha1,unserved"`
	Spec   struct {
		Replicas int `json:"replicas"`
	} `json:"spec"`
}

func TestUnservedVersion(t *testing.T) {
	m := testManager()
	c := For[gizmo](gizmoReconciler{}, Version[gizmoV1alpha1]()).(*controller[gizmo, *gizmo])
	if err := c.prepare(t.Context(), m); err != nil {
		t.Fatal(err)
	}
	crd, err := m.desiredCRD(c.crd())
	if err != nil {
		t.Fatal(err)
	}
	served := map[string]bool{}
	for _, v := range crd["spec"].(map[string]any)["versions"].([]any) {
		v := v.(map[string]any)
		served[v["name"].(string)] = v["served"].(bool)
	}
	if want := map[string]bool{"v2": true, "v1alpha1": false}; !reflect.DeepEqual(served, want) {
		t.Errorf("served = %v, want %v", served, want)
	}
}

func TestAdmissionRuleSkipsSystemNamespaces(t *testing.T) {
	for _, tc := range []struct {
		m    *Manager
		want []string
	}{
		{&Manager{WebhookService: "policy/podpolicy"}, []string{"kube-system", "policy"}},
		{&Manager{WebhookURL: "https://127.0.0.1:9443"}, []string{"kube-system"}},
		{&Manager{WebhookService: "kube-system/podpolicy"}, []string{"kube-system"}},
	} {
		ti := &typeInfo{version: "v1", apiVersion: "v1", kind: "Pod"}
		hook := tc.m.webhooks().admissionRule(ti, resolved{plural: "pods", namespaced: true}, true)
		sel := hook["namespaceSelector"].(map[string]any)["matchExpressions"].([]any)[0].(map[string]any)
		if sel["operator"] != "NotIn" || !reflect.DeepEqual(sel["values"], tc.want) {
			t.Errorf("%+v: selector = %v, want NotIn %v", tc.m, sel, tc.want)
		}
	}
}

func TestVersionErrors(t *testing.T) {
	type other struct {
		Object `kube:"group=test.kube.imjasonh.github.io,kind=Other,version=v1"`
	}
	type deployment struct {
		Object `kube:"apiVersion=apps/v1,kind=Deployment"`
	}
	type retired struct {
		Object `kube:"group=test.kube.imjasonh.github.io,kind=Retired,version=v1,unserved"`
	}
	for _, tc := range []struct {
		c    Controller
		want string
	}{
		{For[gizmo](gizmoReconciler{}, Version[other]()), "same group and kind"},
		{For[gizmo](gizmoReconciler{}, Version[gizmoV1](), Version[gizmoV1]()), "twice"},
		{For[deployment](nop[deployment]{}, Version[gizmoV1]()), "already exists"},
		{For[retired](nop[retired]{}), "must be served"},
	} {
		err := tc.c.prepare(t.Context(), testManager())
		if err == nil || !strings.Contains(err.Error(), tc.want) {
			t.Errorf("got %v, want an error containing %q", err, tc.want)
		}
	}
}

type nop[T any] struct{}

func (nop[T]) Reconcile(context.Context, *T) error { return nil }

// labeler is a mutating webhook for ConfigMaps that sees only metadata.
type configMapMeta struct {
	Object `kube:"apiVersion=v1,kind=ConfigMap"`
}

type labeler struct{}

func (labeler) Default(_ context.Context, cm, _ *configMapMeta) error {
	if cm.Labels == nil {
		cm.Labels = map[string]string{}
	}
	cm.Labels["example.com/defaulted"] = "true"
	return nil
}

func (labeler) Validate(_ context.Context, cm, old *configMapMeta) error {
	if cm.Labels["frozen"] == "true" && old != nil {
		return errors.New("frozen ConfigMaps can't change")
	}
	return nil
}

func TestMutateSendsOnlyChangedFields(t *testing.T) {
	ti, err := typeInfoFor[configMapMeta, *configMapMeta]()
	if err != nil {
		t.Fatal(err)
	}
	obj := `{"apiVersion":"v1","kind":"ConfigMap","metadata":{"name":"cm","namespace":"ns","annotations":{"a/b":"c"}},` +
		`"data":{"key":"value"},"immutable":false}`
	resp := mutate[configMapMeta, *configMapMeta](t.Context(), testManager(), ti, labeler{}, &admissionRequest{Operation: "CREATE", Object: json.RawMessage(obj)})
	if !resp.Allowed || resp.PatchType != "JSONPatch" {
		t.Fatalf("response = %+v", resp)
	}
	if string(resp.Patch) != `[{"op":"add","path":"/metadata/labels","value":{"example.com/defaulted":"true"}}]` {
		t.Errorf("patch = %s", resp.Patch)
	}
	var doc any
	_ = json.Unmarshal([]byte(obj), &doc)
	var ops []struct {
		Op    string `json:"op"`
		Path  string `json:"path"`
		Value any    `json:"value"`
	}
	_ = json.Unmarshal(resp.Patch, &ops)
	var jops []jsonpatch.Op
	for _, o := range ops {
		jops = append(jops, jsonpatch.Op{Op: o.Op, Path: o.Path, Value: o.Value})
	}
	patched, err := jsonpatch.Apply(doc, jops)
	if err != nil {
		t.Fatal(err)
	}
	b, _ := json.Marshal(patched)
	if !strings.Contains(string(b), `"data":{"key":"value"}`) || !strings.Contains(string(b), `"a/b":"c"`) {
		t.Errorf("patched object lost fields: %s", b)
	}

	again := mutate[configMapMeta, *configMapMeta](t.Context(), testManager(), ti, labeler{}, &admissionRequest{Operation: "UPDATE", Object: json.RawMessage(b)})
	if !again.Allowed || again.Patch != nil {
		t.Errorf("defaulting a defaulted object = %+v, want no patch", again)
	}
}

func TestValidate(t *testing.T) {
	ti, err := typeInfoFor[configMapMeta, *configMapMeta]()
	if err != nil {
		t.Fatal(err)
	}
	frozen := json.RawMessage(`{"metadata":{"name":"cm","labels":{"frozen":"true"}}}`)
	m := testManager()
	if r := validate[configMapMeta, *configMapMeta](t.Context(), m, ti, labeler{}, &admissionRequest{Operation: "CREATE", Object: frozen}); !r.Allowed {
		t.Errorf("create = %+v", r)
	}
	r := validate[configMapMeta, *configMapMeta](t.Context(), m, ti, labeler{}, &admissionRequest{Operation: "UPDATE", Object: frozen, OldObject: frozen})
	if r.Allowed || r.Result == nil || r.Result.Message != "frozen ConfigMaps can't change" || r.Result.Code != 403 {
		t.Errorf("update = %+v", r)
	}
}

type writer struct{}

func (writer) Validate(ctx context.Context, cm, _ *configMapMeta) error {
	Own(ctx, &configMapMeta{Object: Meta("copy", nil)})
	return nil
}

func TestWebhooksCantWrite(t *testing.T) {
	ti, _ := typeInfoFor[configMapMeta, *configMapMeta]()
	r := validate[configMapMeta, *configMapMeta](t.Context(), testManager(), ti, writer{}, &admissionRequest{Operation: "CREATE", Object: json.RawMessage(`{"metadata":{"name":"cm"}}`)})
	if r.Allowed || !strings.Contains(r.Result.Message, "kube.Own can't be called in a webhook") {
		t.Errorf("response = %+v", r.Result)
	}
}

type reader struct{ went *bool }

func (r reader) Validate(ctx context.Context, cm, _ *configMapMeta) error {
	Get[localConfigMap](ctx, "system", "state")
	*r.went = true
	return nil
}

// TestWebhooksRejectFailedReads stops a Validate with a Get that can't read.
// The webhook rejects the request with the read's error and doesn't report a
// panic.
func TestWebhooksRejectFailedReads(t *testing.T) {
	var logs bytes.Buffer
	m := testManager()
	m.log = slog.New(slog.NewTextHandler(&logs, nil))
	ti, _ := typeInfoFor[configMapMeta, *configMapMeta]()
	went := false
	body := `{"request":{"uid":"u1","operation":"CREATE","object":{"metadata":{"name":"cm"}}}}`
	rec := httptest.NewRecorder()
	serveAdmission(rec, httptest.NewRequest(http.MethodPost, "/validate", strings.NewReader(body)), m, ti, func(ctx context.Context, req *admissionRequest) *admissionResponse {
		return validate[configMapMeta, *configMapMeta](ctx, m, ti, reader{&went}, req)
	})
	var review admissionReview
	if err := json.Unmarshal(rec.Body.Bytes(), &review); err != nil {
		t.Fatal(err)
	}
	if r := review.Response; went || r == nil || r.Allowed || r.Result == nil || !strings.Contains(r.Result.Message, "is local") {
		t.Errorf("went on = %v, response = %+v; want a rejection with the read's error", went, r)
	}
	if strings.Contains(logs.String(), "panicked") {
		t.Errorf("the webhook reported a panic:\n%s", logs.String())
	}
}

func TestWebhooksNeedHandlers(t *testing.T) {
	err := Webhooks[configMapMeta](struct{}{}).prepare(t.Context(), testManager())
	if err == nil || !strings.Contains(err.Error(), "neither") || !strings.Contains(err.Error(), "Default(context.Context, *configMapMeta, *configMapMeta) error") {
		t.Errorf("err = %v", err)
	}
}

// pointerFinalizer has Finalize only on its pointer type.
type pointerFinalizer struct{ gizmoReconciler }

func (*pointerFinalizer) Finalize(context.Context, *gizmo) error { return nil }

type oldlessValidator struct{ gizmoReconciler }

func (oldlessValidator) Validate(context.Context, *gizmo) error { return nil }

type oldlessDefaulter struct{ gizmoReconciler }

func (oldlessDefaulter) Default(context.Context, *gizmo) error { return nil }

// oldlessLabeler has a Validate method and a Default method without old.
type oldlessLabeler struct{}

func (oldlessLabeler) Validate(context.Context, *configMapMeta, *configMapMeta) error { return nil }
func (oldlessLabeler) Default(context.Context, *configMapMeta) error                  { return nil }

// halfConverter has ConvertTo and a misspelled ConvertFrom.
type halfConverter struct {
	Object `kube:"group=test.kube.imjasonh.github.io,kind=Gizmo,version=v1alpha1"`
}

func (*halfConverter) ConvertTo(*gizmo) error   { return nil }
func (*halfConverter) ConvertFROM(*gizmo) error { return nil }

// valueConverter's ConvertTo takes a gizmo instead of a *gizmo.
type valueConverter struct {
	Object `kube:"group=test.kube.imjasonh.github.io,kind=Gizmo,version=v1alpha2"`
}

func (*valueConverter) ConvertTo(gizmo) error    { return nil }
func (*valueConverter) ConvertFrom(*gizmo) error { return nil }

func TestNearMissMethods(t *testing.T) {
	for _, tc := range []struct {
		name string
		c    Controller
		want string
	}{
		{"Finalize on the pointer type", For[gizmo](pointerFinalizer{}),
			"kube: kube.pointerFinalizer doesn't have the method Finalize(context.Context, *kube.gizmo) error, but *kube.pointerFinalizer does, so pass a *kube.pointerFinalizer"},
		{"Validate without old", For[gizmo](oldlessValidator{}),
			"kube: kube.oldlessValidator has the method Validate(context.Context, *kube.gizmo) error, but the framework calls Validate(context.Context, *kube.gizmo, *kube.gizmo) error"},
		{"Default without old", For[gizmo](oldlessDefaulter{}),
			"kube: kube.oldlessDefaulter has the method Default(context.Context, *kube.gizmo) error, but the framework calls Default(context.Context, *kube.gizmo, *kube.gizmo) error"},
		{"ConvertTo without ConvertFrom", For[gizmo](gizmoReconciler{}, Version[halfConverter]()),
			"kube.Version: *kube.halfConverter has the method ConvertTo(*kube.gizmo) error but not ConvertFrom(*kube.gizmo) error"},
		{"ConvertTo with another signature", For[gizmo](gizmoReconciler{}, Version[valueConverter]()),
			"kube.Version: *kube.valueConverter has the method ConvertTo(kube.gizmo) error, but the framework calls ConvertTo(*kube.gizmo) error"},
		{"Webhooks with Default without old", Webhooks[configMapMeta](oldlessLabeler{}),
			"kube.Webhooks[ConfigMap]: kube.oldlessLabeler has the method Default(context.Context, *kube.configMapMeta) error, but the framework calls Default(context.Context, *kube.configMapMeta, *kube.configMapMeta) error"},
	} {
		if _, err := tc.c.describe(); err == nil || err.Error() != tc.want {
			t.Errorf("%s: describe: got %v, want %q", tc.name, err, tc.want)
		}
		if err := tc.c.prepare(t.Context(), testManager()); err == nil || err.Error() != tc.want {
			t.Errorf("%s: prepare: got %v, want %q", tc.name, err, tc.want)
		}
	}
	d, err := For[gizmo](&pointerFinalizer{}).describe()
	if err != nil || !d.finalizes {
		t.Errorf("describe of a *pointerFinalizer = %+v, %v; want a finalizer", d, err)
	}
}

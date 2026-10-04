package kube

import (
	"context"
	"encoding/json"
	"errors"
	"io"
	"log/slog"
	"maps"
	"net/http"
	"net/http/httptest"
	"net/url"
	"reflect"
	"slices"
	"strings"
	"sync"
	"sync/atomic"
	"testing"
	"time"

	"github.com/imjasonh/playground/kube/internal/client"
)

func TestCompareVersions(t *testing.T) {
	// The order from the Kubernetes documentation on version priority.
	want := []string{"v10", "v2", "v1", "v11beta2", "v10beta3", "v3beta1", "v12alpha1", "v11alpha2", "foo1", "foo10"}
	got := slices.Clone(want)
	slices.Reverse(got)
	slices.SortFunc(got, func(a, b string) int { return compareVersions(b, a) })
	if !slices.Equal(got, want) {
		t.Errorf("sorted = %v, want %v", got, want)
	}
	if compareVersions("v1", "v1") != 0 {
		t.Error("v1 doesn't equal itself")
	}
}

func decode(t *testing.T, s string) map[string]any {
	t.Helper()
	var m map[string]any
	if err := json.Unmarshal([]byte(s), &m); err != nil {
		t.Fatal(err)
	}
	return m
}

func TestDiffSchemas(t *testing.T) {
	live := decode(t, `{"type":"object","properties":{
		"spec":{"type":"object","required":["a"],"properties":{
			"a":{"type":"string"},
			"gone":{"type":"string"},
			"size":{"type":"integer"},
			"items":{"type":"array","items":{"type":"object","properties":{"name":{"type":"string"},"old":{"type":"string"}}}},
			"labels":{"type":"object","additionalProperties":{"type":"object","properties":{"x":{"type":"string"}}}},
			"free":{"x-kubernetes-preserve-unknown-fields":true},
			"anything":{"type":"object","properties":{"k":{"type":"string"}}}
		}}}}`)
	ours := decode(t, `{"type":"object","properties":{
		"spec":{"type":"object","required":["a","b","c"],"properties":{
			"a":{"type":"string"},
			"b":{"type":"string"},
			"c":{"type":"string","default":"x"},
			"size":{"type":"string"},
			"items":{"type":"array","items":{"type":"object","properties":{"name":{"type":"string"}}}},
			"labels":{"type":"object","additionalProperties":{"type":"object","properties":{}}},
			"free":{"type":"object","properties":{"k":{"type":"string"}}},
			"anything":{"x-kubernetes-preserve-unknown-fields":true}
		}}}}`)
	var got []schemaChange
	diffSchemas(live, ours, nil, &got)
	want := []schemaChange{
		{changeType, []string{"spec", "free"}},
		{changeRemoved, []string{"spec", "gone"}},
		{changeRemoved, []string{"spec", "items", "[]", "old"}},
		{changeRemoved, []string{"spec", "labels", "{}", "x"}},
		{changeType, []string{"spec", "size"}},
		{changeRequired, []string{"spec", "b"}},
	}
	if !reflect.DeepEqual(got, want) {
		t.Errorf("diffSchemas =\n%v\nwant\n%v", got, want)
	}
	var none []schemaChange
	diffSchemas(live, live, nil, &none)
	if len(none) != 0 {
		t.Errorf("diffSchemas of a schema with itself = %v", none)
	}
}

func TestValuesAt(t *testing.T) {
	obj := decode(t, `{"spec":{"a":"x","n":null,"items":[{"name":"one"},{"name":"two","old":"y"}],"labels":{"k":{"x":"z"}},"empty":{}}}`)
	for _, tc := range []struct {
		path []string
		has  bool
	}{
		{[]string{"spec", "a"}, true},
		{[]string{"spec", "n"}, false},
		{[]string{"spec", "missing"}, false},
		{[]string{"spec", "items", "[]", "old"}, true},
		{[]string{"spec", "items", "[]", "other"}, false},
		{[]string{"spec", "labels", "{}", "x"}, true},
		{[]string{"spec", "labels", "{}", "y"}, false},
		{[]string{"spec", "a", "deeper"}, false},
	} {
		if got := hasValueAt(obj, tc.path); got != tc.has {
			t.Errorf("hasValueAt(%v) = %v, want %v", tc.path, got, tc.has)
		}
	}
	for _, tc := range []struct {
		path    []string
		missing bool
	}{
		{[]string{"spec", "a"}, false},
		{[]string{"spec", "b"}, true},
		{[]string{"spec", "n"}, true},
		{[]string{"status", "b"}, false}, // no parent, so nothing is missing
		{[]string{"spec", "items", "[]", "old"}, true},
		{[]string{"spec", "items", "[]", "name"}, false},
		{[]string{"spec", "labels", "{}", "x"}, false},
		{[]string{"spec", "empty", "x"}, true},
	} {
		if got := missingAt(obj, tc.path); got != tc.missing {
			t.Errorf("missingAt(%v) = %v, want %v", tc.path, got, tc.missing)
		}
	}
}

func TestSetSchemaAt(t *testing.T) {
	live := decode(t, `{"properties":{"spec":{"properties":{"gone":{"type":"string"},"items":{"items":{"properties":{"old":{"type":"integer"}}}},"m":{"additionalProperties":{"type":"string"}}}}}}`)
	ours := decode(t, `{"properties":{"spec":{"properties":{"items":{"items":{}},"m":{"additionalProperties":{"type":"integer"}}}}}}`)
	for _, p := range [][]string{{"spec", "gone"}, {"spec", "items", "[]", "old"}, {"spec", "m", "{}"}} {
		setSchemaAt(ours, p, schemaAt(live, p))
	}
	if !reflect.DeepEqual(ours, live) {
		t.Errorf("after keeping live's fields:\n%v\nwant\n%v", ours, live)
	}
	if got := formatPath([]string{"spec", "items", "[]", "old"}); got != "spec.items[].old" {
		t.Errorf("formatPath = %q", got)
	}
	if got := formatPath([]string{"spec", "m", "{}", "x"}); got != "spec.m{}.x" {
		t.Errorf("formatPath = %q", got)
	}
}

// crdAPI is an API server that answers each request with the next of its
// scripted replies, after delay, and records the requests. It answers one
// request at a time.
type crdAPI struct {
	mu       sync.Mutex
	delay    time.Duration
	replies  []crdReply
	requests []crdRequest
}

type crdReply struct {
	code int
	body any
}

type crdRequest struct {
	line  string // method and path
	query url.Values
	body  []byte
}

// script sets the replies to the next requests and forgets earlier requests.
func (a *crdAPI) script(replies ...crdReply) {
	a.mu.Lock()
	defer a.mu.Unlock()
	a.replies, a.requests = replies, nil
}

func (a *crdAPI) got() []crdRequest {
	a.mu.Lock()
	defer a.mu.Unlock()
	return slices.Clone(a.requests)
}

func (a *crdAPI) ServeHTTP(w http.ResponseWriter, r *http.Request) {
	body, _ := io.ReadAll(r.Body)
	a.mu.Lock()
	defer a.mu.Unlock()
	time.Sleep(a.delay)
	a.requests = append(a.requests, crdRequest{r.Method + " " + r.URL.Path, r.URL.Query(), body})
	if len(a.replies) == 0 {
		http.Error(w, "unexpected request", http.StatusInternalServerError)
		return
	}
	reply := a.replies[0]
	a.replies = a.replies[1:]
	reply.write(w)
}

func (r crdReply) write(w http.ResponseWriter) {
	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(r.code)
	_ = json.NewEncoder(w).Encode(r.body)
}

func crdError(code int, reason string) crdReply {
	return crdReply{code, map[string]any{"kind": "Status", "status": "Failure", "reason": reason, "code": code}}
}

// crdWith returns a reply with a CustomResourceDefinition that has the
// versions in served, each served or not.
func crdWith(established bool, served map[string]bool) crdReply {
	var crd liveCRD
	for _, v := range slices.Sorted(maps.Keys(served)) {
		crd.Spec.Versions = append(crd.Spec.Versions, map[string]any{"name": v, "served": served[v]})
	}
	c := Condition{Type: "Established", Status: False}
	if established {
		c.Status = True
	}
	crd.Status.Conditions = []Condition{c}
	return crdReply{http.StatusOK, crd}
}

// newCRDManager returns a Manager named owner whose API server is api.
func newCRDManager(t *testing.T, api http.Handler) *Manager {
	t.Helper()
	srv := httptest.NewServer(api)
	t.Cleanup(srv.Close)
	c, err := client.New(&client.Config{Host: srv.URL}, "test")
	if err != nil {
		t.Fatal(err)
	}
	m := testManager()
	m.Name, m.client, m.crdCalls = "owner", c, map[*typeInfo]*crdCall{}
	return m
}

func TestCreateCRD(t *testing.T) {
	ti, err := typeInfoFor[gizmo]()
	if err != nil {
		t.Fatal(err)
	}
	a := &crdAPI{}
	m := newCRDManager(t, a)
	get := "GET " + crdPath("gizmos.test.kube.imjasonh.github.io")
	post := "POST /apis/apiextensions.k8s.io/v1/customresourcedefinitions"
	notFound, forbidden := crdError(http.StatusNotFound, "NotFound"), crdError(http.StatusForbidden, "Forbidden")
	created := crdReply{http.StatusCreated, nil}
	v2 := map[string]bool{"v2": true}
	for _, tc := range []struct {
		name    string
		replies []crdReply
		want    []string
		err     string
	}{
		{"a missing CRD", []crdReply{notFound, created, crdWith(true, v2)}, []string{get, post, get}, ""},
		{"a CRD that another program creates first", []crdReply{notFound, crdError(http.StatusConflict, "AlreadyExists"), crdWith(true, v2)}, []string{get, post, get}, ""},
		{"a new CRD that isn't established yet", []crdReply{notFound, created, crdWith(false, v2), crdWith(true, v2)}, []string{get, post, get, get}, ""},
		{"an existing CRD with other versions", []crdReply{crdWith(true, map[string]bool{"v1": false, "v2": true, "v3": true})}, []string{get}, ""},
		{"an existing CRD that isn't established yet", []crdReply{crdWith(false, v2), crdWith(true, v2)}, []string{get, get}, ""},
		{"an existing CRD without the version", []crdReply{crdWith(true, map[string]bool{"v1": true})}, []string{get}, "doesn't serve version v2"},
		{"an existing CRD that doesn't serve the version", []crdReply{crdWith(true, map[string]bool{"v1": true, "v2": false})}, []string{get}, "doesn't serve version v2"},
		{"no permission to get CRDs", []crdReply{forbidden}, []string{get}, ""},
		{"no permission to create CRDs", []crdReply{notFound, forbidden}, []string{get, post}, "creating CustomResourceDefinition"},
	} {
		a.script(tc.replies...)
		err := m.createCRD(t.Context(), ti)
		switch {
		case tc.err == "" && err != nil:
			t.Errorf("%s: createCRD = %v", tc.name, err)
		case tc.err != "" && (err == nil || !strings.Contains(err.Error(), tc.err)):
			t.Errorf("%s: createCRD = %v, want an error containing %q", tc.name, err, tc.err)
		}
		var lines []string
		for _, r := range a.got() {
			lines = append(lines, r.line)
			if r.line != post {
				continue
			}
			var crd liveCRD
			if err := json.Unmarshal(r.body, &crd); err != nil {
				t.Fatal(err)
			}
			if fm := r.query.Get("fieldManager"); fm != "owner" {
				t.Errorf("%s: created the CRD as field manager %q, want owner", tc.name, fm)
			}
			if l := crd.Metadata.Labels[newLabelKeys(m.Domain).managedBy]; l != "owner" {
				t.Errorf("%s: created the CRD with managed-by label %q, want owner", tc.name, l)
			}
			if len(crd.Spec.Versions) != 1 || crd.storage() != "v2" {
				t.Errorf("%s: created the CRD with versions %v, want only v2", tc.name, crd.Spec.Versions)
			}
		}
		if !slices.Equal(lines, tc.want) {
			t.Errorf("%s: requests = %q, want %q", tc.name, lines, tc.want)
		}
	}
}

// TestPlanCRDOfAnotherProgram checks the errors about a version that the
// program doesn't declare, in a CRD that the program installed or that
// another program created.
func TestPlanCRDOfAnotherProgram(t *testing.T) {
	gizmos, err := typeInfoFor[gizmo]()
	if err != nil {
		t.Fatal(err)
	}
	m := testManager()
	m.Name = "gizmos"
	const other = "owner installed the CustomResourceDefinition and may own the type without reconciling it"
	for _, tc := range []struct {
		name, by, version, want string
	}{
		{"an older version that the program installed", "gizmos", "v1", "keep its kube.Version"},
		{"an older version that another program created", "owner", "v1", other + "; declare v1 with kube.Version"},
		{"a newer version that the program installed", "gizmos", "v3", "which is newer than this program's versions"},
		{"a newer version that another program created", "owner", "v3", other + "; declare v3 with kube.Version"},
	} {
		var live liveCRD
		live.Metadata.Labels = map[string]string{newLabelKeys(m.Domain).managedBy: tc.by}
		live.Spec.Versions = []map[string]any{{"name": tc.version, "served": true, "storage": true}}
		live.Status.StoredVersions = []string{tc.version}
		_, err := m.planCRD(t.Context(), crdSpec{ti: gizmos}, &live, map[string]any{})
		if err == nil {
			t.Errorf("%s: planCRD succeeded", tc.name)
			continue
		}
		if !strings.Contains(err.Error(), tc.want) || tc.by == m.Name && strings.Contains(err.Error(), "installed the CustomResourceDefinition") {
			t.Errorf("%s: planCRD = %v, want an error containing %q", tc.name, err, tc.want)
		}
	}
}

func TestEnsureCRD(t *testing.T) {
	a := &crdAPI{}
	m := newCRDManager(t, a)
	gizmos, err := typeInfoFor[gizmo]()
	if err != nil {
		t.Fatal(err)
	}
	gizmosV1, err := typeInfoFor[gizmoV1]()
	if err != nil {
		t.Fatal(err)
	}
	configMaps, err := typeInfoFor[configMapMeta]()
	if err != nil {
		t.Fatal(err)
	}
	m.controllers = []Controller{For[gizmo](gizmoReconciler{})}
	for _, ti := range []*typeInfo{configMaps, gizmosV1} {
		a.script()
		if err := m.ensureCRD(t.Context(), ti); err != nil || len(a.got()) > 0 {
			t.Errorf("ensureCRD(%v) = %v after requests %v, want no requests", ti, err, a.got())
		}
	}

	m.controllers = nil
	a.script(crdError(http.StatusNotFound, "NotFound"), crdError(http.StatusForbidden, "Forbidden"))
	if err := m.ensureCRD(t.Context(), gizmos); err == nil {
		t.Error("ensureCRD succeeded without permission to create the CRD")
	}
	a.script(crdError(http.StatusNotFound, "NotFound"), crdReply{http.StatusCreated, nil}, crdWith(true, map[string]bool{"v2": true}))
	if err := m.ensureCRD(t.Context(), gizmos); err != nil || len(a.got()) != 3 {
		t.Errorf("after an error, ensureCRD = %v after %d requests, want 3", err, len(a.got()))
	}
	a.script()
	if err := m.ensureCRD(t.Context(), gizmos); err != nil || len(a.got()) > 0 {
		t.Errorf("a second ensureCRD = %v after %d requests, want none", err, len(a.got()))
	}
}

// TestEnsureCRDConcurrently makes the first uses of a type at once, as a
// controller's workers do, and expects one check and creation of its CRD.
func TestEnsureCRDConcurrently(t *testing.T) {
	a := &crdAPI{delay: 10 * time.Millisecond}
	m := newCRDManager(t, a)
	gizmos, err := typeInfoFor[gizmo]()
	if err != nil {
		t.Fatal(err)
	}
	a.script(crdError(http.StatusNotFound, "NotFound"), crdReply{http.StatusCreated, nil}, crdWith(true, map[string]bool{"v2": true}))
	start := make(chan struct{})
	var wg sync.WaitGroup
	for range 8 {
		wg.Go(func() {
			<-start
			if err := m.ensureCRD(t.Context(), gizmos); err != nil {
				t.Error(err)
			}
		})
	}
	close(start)
	wg.Wait()
	var lines []string
	for _, r := range a.got() {
		lines = append(lines, r.line)
	}
	get := "GET " + crdPath("gizmos.test.kube.imjasonh.github.io")
	if want := []string{get, "POST /apis/apiextensions.k8s.io/v1/customresourcedefinitions", get}; !slices.Equal(lines, want) {
		t.Errorf("requests = %q, want %q", lines, want)
	}
}

// TestEnsureCRDAfterCanceledCreate ends the context of the first use of a type
// while it waits for the CRD that it created, and expects a use that waits for
// it with a live context to succeed.
func TestEnsureCRDAfterCanceledCreate(t *testing.T) {
	gizmos, err := typeInfoFor[gizmo]()
	if err != nil {
		t.Fatal(err)
	}
	var requests atomic.Int64
	var established atomic.Bool
	m := newCRDManager(t, http.HandlerFunc(func(w http.ResponseWriter, _ *http.Request) {
		switch requests.Add(1) {
		case 1:
			crdError(http.StatusNotFound, "NotFound").write(w)
		case 2:
			crdReply{http.StatusCreated, nil}.write(w)
		default:
			crdWith(established.Load(), map[string]bool{"v2": true}).write(w)
		}
	}))
	ctx, cancel := context.WithCancel(t.Context())
	defer cancel()
	first := make(chan error, 1)
	go func() { first <- m.ensureCRD(ctx, gizmos) }()
	for requests.Load() < 3 {
		select {
		case err := <-first:
			t.Fatalf("the first use = %v before its context ended", err)
		case <-time.After(time.Millisecond):
		}
	}
	second := make(chan error, 1)
	go func() { second <- m.ensureCRD(t.Context(), gizmos) }()
	time.Sleep(100 * time.Millisecond)
	cancel()
	if err := <-first; !errors.Is(err, context.Canceled) {
		t.Errorf("the first use = %v, want %v", err, context.Canceled)
	}
	established.Store(true)
	if err := <-second; err != nil {
		t.Errorf("the second use = %v after the first use's context ended", err)
	}
}

// TestEnsureCRDAfterPanic makes creating a type's CRD panic, and expects the
// next use of the type to try again instead of waiting for the call that
// panicked.
func TestEnsureCRDAfterPanic(t *testing.T) {
	a := &crdAPI{}
	m := newCRDManager(t, a)
	gizmos, err := typeInfoFor[gizmo]()
	if err != nil {
		t.Fatal(err)
	}
	m.log = slog.New(panicHandler{})
	a.script(crdError(http.StatusNotFound, "NotFound"), crdReply{http.StatusCreated, nil})
	func() {
		defer func() { _ = recover() }()
		_ = m.ensureCRD(t.Context(), gizmos)
		t.Error("ensureCRD didn't panic")
	}()
	m.log = slog.Default()
	a.script(crdWith(true, map[string]bool{"v2": true}))
	ctx, cancel := context.WithTimeout(t.Context(), 5*time.Second)
	defer cancel()
	if err := m.ensureCRD(ctx, gizmos); err != nil {
		t.Errorf("after a panic, ensureCRD = %v", err)
	}
}

// panicHandler is a slog.Handler that panics when it handles a record.
type panicHandler struct{}

func (panicHandler) Enabled(context.Context, slog.Level) bool  { return true }
func (panicHandler) Handle(context.Context, slog.Record) error { panic("logging") }
func (h panicHandler) WithAttrs([]slog.Attr) slog.Handler      { return h }
func (h panicHandler) WithGroup(string) slog.Handler           { return h }

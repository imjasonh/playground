package jsonpatch

import (
	"encoding/json"
	"math/rand/v2"
	"reflect"
	"strconv"
	"testing"
)

func decode(t *testing.T, s string) any {
	t.Helper()
	var v any
	if err := json.Unmarshal([]byte(s), &v); err != nil {
		t.Fatal(err)
	}
	return v
}

func TestDiffApplies(t *testing.T) {
	for _, tc := range []struct{ from, to string }{
		{`{}`, `{}`},
		{`{"a":1}`, `{"a":2}`},
		{`{"a":1,"b":2}`, `{"b":2,"c":{"d":[1,2]}}`},
		{`{"a":[1,2,3]}`, `{"a":[1,5]}`},
		{`{"a":[1]}`, `{"a":[1,{"x":true},null]}`},
		{`{"a":{"b":1}}`, `{"a":[1]}`},
		{`{"a/b":{"~c":1}}`, `{"a/b":{"~c":2,"d":null}}`},
		{`[1,2]`, `{"a":1}`},
		{`{"a":null}`, `{"a":{"b":1}}`},
	} {
		from, to := decode(t, tc.from), decode(t, tc.to)
		ops := Diff(from, to)
		got, err := Apply(from, ops)
		if err != nil {
			t.Errorf("%s -> %s: applying %v: %v", tc.from, tc.to, ops, err)
			continue
		}
		if !reflect.DeepEqual(got, to) {
			t.Errorf("%s -> %s: patch %v gives %v", tc.from, tc.to, ops, got)
		}
		if !reflect.DeepEqual(from, decode(t, tc.from)) {
			t.Errorf("Apply changed its input")
		}
	}
}

func randomValue(r *rand.Rand, depth int) any {
	switch n := r.IntN(6); {
	case depth > 3 || n == 0:
		return float64(r.IntN(3))
	case n == 1:
		return "s" + strconv.Itoa(r.IntN(3))
	case n == 2:
		return nil
	case n == 3:
		out := make([]any, r.IntN(4))
		for i := range out {
			out[i] = randomValue(r, depth+1)
		}
		return out
	default:
		out := map[string]any{}
		for range r.IntN(4) {
			out[[]string{"a", "b", "c/d", "e~f"}[r.IntN(4)]] = randomValue(r, depth+1)
		}
		return out
	}
}

func TestDiffAppliesToRandomDocuments(t *testing.T) {
	r := rand.New(rand.NewPCG(1, 2))
	for i := range 5000 {
		from, to := randomValue(r, 0), randomValue(r, 0)
		got, err := Apply(from, Diff(from, to))
		if err != nil {
			t.Fatalf("case %d: %v -> %v: %v", i, from, to, err)
		}
		if !reflect.DeepEqual(got, to) {
			t.Fatalf("case %d: %v -> %v: got %v", i, from, to, got)
		}
	}
}

func TestOverlayKeepsFieldsTheViewsLeaveOut(t *testing.T) {
	doc := decode(t, `{
		"metadata": {"name": "web", "managedFields": [{"manager": "kubectl"}], "labels": {"app": "web"}},
		"spec": {
			"replicas": 1,
			"paused": false,
			"containers": [
				{"name": "app", "image": "app:1", "env": [{"name": "A", "value": "1"}]},
				{"name": "sidecar", "image": "proxy:1", "ports": [{"containerPort": 15001}]}
			]
		}
	}`)
	before := decode(t, `{
		"metadata": {"name": "web", "labels": {"app": "web"}},
		"spec": {"replicas": 1, "containers": [{"name": "app", "image": "app:1"}, {"name": "sidecar", "image": "proxy:1"}], "tier": ""}
	}`)
	after := decode(t, `{
		"metadata": {"name": "web", "labels": {"app": "web", "team": "shop"}},
		"spec": {"replicas": 3, "containers": [{"name": "app", "image": "app:2"}, {"name": "sidecar", "image": "proxy:1"}, {"name": "log", "image": "log:1"}], "tier": ""}
	}`)
	got := Overlay(doc, before, after)
	want := decode(t, `{
		"metadata": {"name": "web", "managedFields": [{"manager": "kubectl"}], "labels": {"app": "web", "team": "shop"}},
		"spec": {
			"replicas": 3,
			"paused": false,
			"containers": [
				{"name": "app", "image": "app:2", "env": [{"name": "A", "value": "1"}]},
				{"name": "sidecar", "image": "proxy:1", "ports": [{"containerPort": 15001}]},
				{"name": "log", "image": "log:1"}
			]
		}
	}`)
	if !reflect.DeepEqual(got, want) {
		gb, _ := json.Marshal(got)
		t.Fatalf("Overlay = %s", gb)
	}
	ops := Diff(doc, got)
	b, _ := json.Marshal(ops)
	wantOps := `[{"op":"add","path":"/metadata/labels/team","value":"shop"},` +
		`{"op":"replace","path":"/spec/containers/0/image","value":"app:2"},` +
		`{"op":"add","path":"/spec/containers/2","value":{"image":"log:1","name":"log"}},` +
		`{"op":"replace","path":"/spec/replicas","value":3}]`
	if string(b) != wantOps {
		t.Errorf("patch = %s\nwant    %s", b, wantOps)
	}
}

func TestOverlayRemovesFieldsThatAfterDrops(t *testing.T) {
	doc := decode(t, `{"spec": {"suspend": true, "other": 1}}`)
	before := decode(t, `{"spec": {"suspend": true}}`)
	after := decode(t, `{"spec": {}}`)
	got := Overlay(doc, before, after)
	if !reflect.DeepEqual(got, decode(t, `{"spec": {"other": 1}}`)) {
		t.Errorf("Overlay = %v", got)
	}
}

func TestOverlayAddsFieldsMissingFromTheDocument(t *testing.T) {
	doc := decode(t, `{"metadata": {"name": "w"}}`)
	before := decode(t, `{"metadata": {"name": "w"}, "spec": {"size": 0, "color": ""}}`)
	after := decode(t, `{"metadata": {"name": "w"}, "spec": {"size": 3, "color": ""}}`)
	got := Overlay(doc, before, after)
	if !reflect.DeepEqual(got, decode(t, `{"metadata": {"name": "w"}, "spec": {"size": 3}}`)) {
		t.Errorf("Overlay = %v", got)
	}
	patched, err := Apply(doc, Diff(doc, got))
	if err != nil || !reflect.DeepEqual(patched, got) {
		t.Errorf("patch didn't apply: %v, %v", patched, err)
	}
}

func TestOpJSON(t *testing.T) {
	b, _ := json.Marshal([]Op{{Op: "add", Path: "/a", Value: nil}, {Op: "remove", Path: "/b"}})
	if string(b) != `[{"op":"add","path":"/a","value":null},{"op":"remove","path":"/b"}]` {
		t.Errorf("JSON = %s", b)
	}
}

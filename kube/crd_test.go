package kube

import (
	"encoding/json"
	"reflect"
	"slices"
	"testing"
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

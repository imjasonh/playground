//go:build !kube_nogenerate

package kube

import (
	"bytes"
	"encoding/json"
	"reflect"
	"strings"
	"testing"

	v1 "github.com/google/go-containerregistry/pkg/v1"
)

func TestEventGrantsFor(t *testing.T) {
	p := &installPlan{cluster: grants{}, local: grants{}, watched: grants{}, defaultNS: grants{}}
	same := func(a, b grants) bool {
		return reflect.ValueOf(a).UnsafePointer() == reflect.ValueOf(b).UnsafePointer()
	}
	for _, tc := range []struct {
		name     string
		ti       *typeInfo
		watching bool
		want     grants
	}{
		{"a namespaced type in a program that watches one namespace", &typeInfo{scope: "Namespaced"}, true, p.watched},
		{"a namespaced type in a program that watches every namespace", &typeInfo{scope: "Namespaced"}, false, p.cluster},
		{"a cluster-scoped type", &typeInfo{scope: "Cluster"}, false, p.defaultNS},
		{"a cluster-scoped type in a program that watches one namespace", &typeInfo{scope: "Cluster"}, true, p.defaultNS},
		{"a type whose scope discovery decides", &typeInfo{}, true, p.cluster},
	} {
		if got := p.eventGrantsFor(tc.ti, tc.watching); !same(got, tc.want) {
			t.Errorf("%s: got the wrong grants", tc.name)
		}
	}
}

func TestPlanGrantsEventsOnlyToProgramsThatRecordThem(t *testing.T) {
	const rule = `{"apiGroups":["events.k8s.io"],"resources":["events"],"verbs":["create","patch"]}`
	const website = "github.com/imjasonh/playground/kube/examples/website"
	rules := func(g grants) string {
		b, _ := json.Marshal(g.rules())
		return string(b)
	}
	for _, tc := range []struct {
		name                               string
		pkg                                string
		c                                  Controller
		namespace, watch                   string
		cluster, local, watched, defaultNS bool
	}{
		{"a namespaced type", website, For[widget](nop[widget]{}), "app", "", true, false, false, false},
		{"a namespaced type in a program that watches one namespace", website, For[widget](nop[widget]{}), "app", "team", false, false, true, false},
		{"a namespaced type in a program that watches its own namespace", website, For[widget](nop[widget]{}), "app", "app", false, true, false, false},
		{"a cluster-scoped type", website, For[policy](nop[policy]{}), "app", "", false, false, false, true},
		{"a cluster-scoped type in a program installed in default", website, For[policy](nop[policy]{}), "default", "", false, true, false, false},
		{"a cluster-scoped type in a program that watches default", website, For[policy](nop[policy]{}), "app", "default", false, false, true, false},
		{"a program that doesn't call Eventf", "github.com/imjasonh/playground/kube/examples/replicator", For[widget](nop[widget]{}), "app", "", false, false, false, false},
		{"a program without reconcilers", website, Webhooks[configMapMeta](labeler{}), "app", "", false, false, false, false},
	} {
		o := &generateOptions{namespace: tc.namespace, watchNamespace: tc.watch, replicas: 1, shards: 1, platforms: []v1.Platform{{OS: "linux", Architecture: "amd64"}}, stderr: &bytes.Buffer{}}
		p, err := o.plan(t.Context(), []Controller{tc.c}, tc.pkg)
		if err != nil {
			t.Fatal(err)
		}
		for _, g := range []struct {
			role   string
			grants grants
			want   bool
		}{
			{"the ClusterRole", p.cluster, tc.cluster},
			{"the Role in the program's namespace", p.local, tc.local},
			{"the Role in the watched namespace", p.watched, tc.watched},
			{"the Role in default", p.defaultNS, tc.defaultNS},
		} {
			if got := rules(g.grants); strings.Contains(got, rule) != g.want {
				t.Errorf("%s: %s has rules %s; want the events rule there: %v", tc.name, g.role, got, g.want)
			}
		}
	}
}

func TestManifestsForEventsInDefault(t *testing.T) {
	o := &generateOptions{program: "app", name: "app", namespace: "app-system", replicas: 1, shards: 1}
	p := &installPlan{cluster: grants{}, local: grants{}, watched: grants{}, defaultNS: grants{}}
	p.defaultNS.add("events.k8s.io", "events", "", "create", "patch")
	byKind := map[string]map[string]any{}
	for _, d := range o.manifests("ref", p) {
		b, _ := json.Marshal(d)
		var m map[string]any
		_ = json.Unmarshal(b, &m)
		byKind[m["kind"].(string)] = m
	}
	role, binding := byKind["Role"], byKind["RoleBinding"]
	if role == nil || role["metadata"].(map[string]any)["namespace"] != "default" || binding["metadata"].(map[string]any)["namespace"] != "default" {
		t.Fatalf("Role = %v, RoleBinding = %v, want them in default", role, binding)
	}
	if b, _ := json.Marshal(role["rules"]); string(b) != `[{"apiGroups":["events.k8s.io"],"resources":["events"],"verbs":["create","patch"]}]` {
		t.Errorf("Role rules = %s", b)
	}
	if b, _ := json.Marshal(binding["subjects"]); string(b) != `[{"kind":"ServiceAccount","name":"app","namespace":"app-system"}]` {
		t.Errorf("RoleBinding subjects = %s", b)
	}
}

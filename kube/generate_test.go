//go:build !kube_nogenerate

package kube

import (
	"bytes"
	"context"
	"encoding/json"
	"reflect"
	"slices"
	"strings"
	"testing"

	v1 "github.com/google/go-containerregistry/pkg/v1"
)

func TestGrantRules(t *testing.T) {
	g := grants{}
	g.add("apps", "deployments", "", "list", "watch")
	g.add("apps", "deployments", "", "create", "patch", "list")
	g.add("", "services", "", "create", "list", "patch", "watch")
	g.add("", "configmaps", "", "list", "watch")
	g.add("", "secrets", "app-webhook-tls", "get", "update")
	b, err := json.Marshal(g.rules())
	if err != nil {
		t.Fatal(err)
	}
	want := `[` +
		`{"apiGroups":[""],"resources":["configmaps"],"verbs":["list","watch"]},` +
		`{"apiGroups":[""],"resources":["secrets"],"resourceNames":["app-webhook-tls"],"verbs":["get","update"]},` +
		`{"apiGroups":[""],"resources":["services"],"verbs":["create","list","patch","watch"]},` +
		`{"apiGroups":["apps"],"resources":["deployments"],"verbs":["create","list","patch","watch"]}]`
	if string(b) != want {
		t.Errorf("rules =\n%s\nwant\n%s", b, want)
	}
	g.add("", "configmaps", "", "create", "patch")
	g.add("", "services", "", "list")
	b, _ = json.Marshal(g.rules())
	if !strings.Contains(string(b), `{"apiGroups":[""],"resources":["configmaps","services"],"verbs":["create","list","patch","watch"]}`) {
		t.Errorf("resources with the same verbs aren't combined: %s", b)
	}
}

func TestResourceName(t *testing.T) {
	for _, tc := range []struct {
		ti            typeInfo
		group, plural string
	}{
		{typeInfo{group: "apps", kind: "Deployment"}, "apps", "deployments"},
		{typeInfo{kind: "Endpoints"}, "", "endpoints"},
		{typeInfo{group: "networking.k8s.io", kind: "Ingress"}, "networking.k8s.io", "ingresses"},
		{typeInfo{group: "networking.k8s.io", kind: "NetworkPolicy"}, "networking.k8s.io", "networkpolicies"},
		{typeInfo{group: "example.dev", kind: "Moose", plural: "moose"}, "example.dev", "moose"},
	} {
		if g, p := resourceName(&tc.ti); g != tc.group || p != tc.plural {
			t.Errorf("resourceName(%s) = %q, %q, want %q, %q", tc.ti.kind, g, p, tc.group, tc.plural)
		}
	}
}

func TestObjectName(t *testing.T) {
	for in, want := range map[string]string{"website": "website", "My_Controller": "my-controller", "__": "controller", "a.b": "a-b"} {
		if got := objectName(in); got != want {
			t.Errorf("objectName(%q) = %q, want %q", in, got, want)
		}
	}
}

type conversionHub struct {
	Object `kube:"group=test.kube.imjasonh.github.io,kind=Hub,version=v2"`
}

type conversionSpoke struct {
	Object `kube:"group=test.kube.imjasonh.github.io,kind=Hub,version=v1"`
}

func (*conversionSpoke) ConvertTo(*conversionHub) error   { return nil }
func (*conversionSpoke) ConvertFrom(*conversionHub) error { return nil }

type validatingReconciler struct{ gizmoReconciler }

func (validatingReconciler) Validate(context.Context, *gizmo, *gizmo) error { return nil }

func TestDescribe(t *testing.T) {
	type deployment struct {
		Object `kube:"apiVersion=apps/v1,kind=Deployment"`
	}
	for _, tc := range []struct {
		name string
		c    Controller
		want declared
	}{
		{"reconciler", For[gizmo](gizmoReconciler{}, Owns[deployment]()), declared{reconciles: true, owns: []*typeInfo{{kind: "Deployment"}}}},
		{"validator", For[gizmo](validatingReconciler{}), declared{reconciles: true, webhooks: true}},
		{"conversion", For[conversionHub](nop[conversionHub]{}, Version[conversionSpoke]()), declared{reconciles: true, webhooks: true}},
		{"no conversion", For[gizmo](gizmoReconciler{}, Version[gizmoV1beta1]()), declared{reconciles: true}},
		{"webhooks", Webhooks[configMapMeta](labeler{}), declared{webhooks: true}},
	} {
		got, err := tc.c.describe()
		if err != nil {
			t.Fatal(err)
		}
		if got.ti == nil || got.reconciles != tc.want.reconciles || got.webhooks != tc.want.webhooks || len(got.owns) != len(tc.want.owns) {
			t.Errorf("%s: describe = %+v, want %+v", tc.name, got, tc.want)
		}
		for i, o := range got.owns {
			if o.kind != tc.want.owns[i].kind {
				t.Errorf("%s: owns %s, want %s", tc.name, o.kind, tc.want.owns[i].kind)
			}
		}
	}
}

func TestManifests(t *testing.T) {
	o := &generateOptions{program: "web_site", name: "web-site", namespace: "sites", replicas: 3, shards: 1, args: []string{"-v"}}
	p := &installPlan{cluster: grants{}, local: grants{}, webhooks: true, electLeader: true}
	p.cluster.add("apps", "deployments", "", "list")
	p.local.add("coordination.k8s.io", "leases", "", "get")
	docs := o.manifests("ghcr.io/you/web-site@sha256:abc", p)
	var kinds []string
	var deployment, service map[string]any
	for _, d := range docs {
		b, _ := json.Marshal(d)
		var m map[string]any
		_ = json.Unmarshal(b, &m)
		kinds = append(kinds, m["kind"].(string))
		meta := m["metadata"].(map[string]any)
		if m["kind"] != "Namespace" && meta["name"] != "web-site" {
			t.Errorf("%s is named %v", m["kind"], meta["name"])
		}
		switch m["kind"] {
		case "Deployment":
			deployment = m
		case "Service":
			service = m
		}
	}
	want := []string{"Namespace", "ServiceAccount", "ClusterRole", "ClusterRoleBinding", "Role", "RoleBinding", "Service", "Deployment", "PodDisruptionBudget"}
	if !slices.Equal(kinds, want) {
		t.Errorf("kinds = %v, want %v", kinds, want)
	}
	b, _ := json.Marshal(deployment)
	for _, s := range []string{
		`"replicas":3`,
		`"image":"ghcr.io/you/web-site@sha256:abc"`,
		`"args":["-addr=:8080","-leader-elect","-webhook-addr=:9443","-webhook-service=sites/web-site","-v"]`,
		`"serviceAccountName":"web-site"`,
		`"runAsNonRoot":true`,
		`"readOnlyRootFilesystem":true`,
	} {
		if !strings.Contains(string(b), s) {
			t.Errorf("the Deployment lacks %s: %s", s, b)
		}
	}
	if b, _ := json.Marshal(service); !strings.Contains(string(b), `"ports":[{"name":"webhook","port":443,"targetPort":"webhook"}]`) {
		t.Errorf("Service = %s", b)
	}

	o.replicas, o.shards = 1, 1
	docs = o.manifests("ref", &installPlan{cluster: grants{}, local: grants{}})
	kinds = nil
	for _, d := range docs {
		kinds = append(kinds, d[1].value.(string))
	}
	if want := []string{"Namespace", "ServiceAccount", "ClusterRole", "ClusterRoleBinding", "Deployment"}; !slices.Equal(kinds, want) {
		t.Errorf("one replica without webhooks: kinds = %v, want %v", kinds, want)
	}
	b, _ = json.Marshal(docs[len(docs)-1])
	if !strings.Contains(string(b), `"args":["-addr=:8080","-v"]`) {
		t.Errorf("one replica without webhooks: %s", b)
	}
}

func TestGenerateArguments(t *testing.T) {
	for _, tc := range []struct {
		args []string
		want string
	}{
		{nil, "-registry is required"},
		{[]string{"-registry=ghcr.io/you", "extra"}, `unexpected argument "extra"`},
		{[]string{"-registry=ghcr.io/you", "-platform=linux"}, "isn't os/architecture"},
		{[]string{"-registry=ghcr.io/you", "-replicas=0"}, "at least 1"},
		{[]string{"-registry=ghcr.io/you", "-nope"}, "flag provided but not defined"},
	} {
		var stderr bytes.Buffer
		err := generate(t.Context(), tc.args, nil, &bytes.Buffer{}, &stderr)
		if err == nil || !strings.Contains(err.Error(), tc.want) {
			t.Errorf("generate %q = %v, want an error containing %q", tc.args, err, tc.want)
		}
	}
	if p, err := v1.ParsePlatform("linux/arm/v7"); err != nil || !reflect.DeepEqual(buildEnv(*p)[len(buildEnv(*p))-1], "GOARM=7") {
		t.Errorf("buildEnv(linux/arm/v7) doesn't set GOARM: %v", err)
	}
}

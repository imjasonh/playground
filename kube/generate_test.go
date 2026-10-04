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
		{"conversion", For[conversionHub](nop[conversionHub]{}, Version[conversionSpoke]()), declared{reconciles: true, webhooks: true, versioned: true}},
		{"no conversion", For[gizmo](gizmoReconciler{}, Version[gizmoV1beta1]()), declared{reconciles: true, versioned: true}},
		{"webhooks", Webhooks[configMapMeta](labeler{}), declared{webhooks: true}},
	} {
		got, err := tc.c.describe()
		if err != nil {
			t.Fatal(err)
		}
		if got.ti == nil || got.reconciles != tc.want.reconciles || got.webhooks != tc.want.webhooks || got.versioned != tc.want.versioned || len(got.owns) != len(tc.want.owns) {
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
		`"volumeMounts":[{"mountPath":"/tmp","name":"tmp"}]`,
		`"volumes":[{"emptyDir":{},"name":"tmp"}]`,
	} {
		if !strings.Contains(string(b), s) {
			t.Errorf("the Deployment lacks %s: %s", s, b)
		}
	}
	if b, _ := json.Marshal(service); !strings.Contains(string(b), `"ports":[{"name":"webhook","port":443,"targetPort":"webhook"}]`) {
		t.Errorf("Service = %s", b)
	}

	o.tmpSize = "1Gi"
	docs = o.manifests("ref", p)
	if b, _ := json.Marshal(docs[len(docs)-2]); !strings.Contains(string(b), `"volumes":[{"name":"tmp","emptyDir":{"sizeLimit":"1Gi"}}]`) {
		t.Errorf("with -tmp-size=1Gi, the Deployment = %s", b)
	}
	o.tmpSize = ""

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

func TestManifestsServe(t *testing.T) {
	o := &generateOptions{program: "probe", name: "probe", namespace: "probe", replicas: 1, shards: 1}
	for _, tc := range []struct {
		webhooks             bool
		args, ports, service string
	}{
		{
			false,
			`"args":["-addr=:8080","-serve-addr=:8081"]`,
			`"ports":[{"name":"http","containerPort":8080},{"name":"serve","containerPort":8081}]`,
			`"ports":[{"name":"serve","port":80,"targetPort":"serve"}]`,
		},
		{
			true,
			`"args":["-addr=:8080","-webhook-addr=:9443","-webhook-service=probe/probe","-serve-addr=:8081"]`,
			`"ports":[{"name":"http","containerPort":8080},{"name":"webhook","containerPort":9443},{"name":"serve","containerPort":8081}]`,
			`"ports":[{"name":"webhook","port":443,"targetPort":"webhook"},{"name":"serve","port":80,"targetPort":"serve"}]`,
		},
	} {
		byKind := map[string]string{}
		var kinds []string
		for _, d := range o.manifests("ref", &installPlan{cluster: grants{}, local: grants{}, webhooks: tc.webhooks, serves: true}) {
			b, _ := json.Marshal(d)
			kind := d[1].value.(string)
			kinds = append(kinds, kind)
			byKind[kind] = string(b)
		}
		if want := []string{"Namespace", "ServiceAccount", "ClusterRole", "ClusterRoleBinding", "Service", "Deployment"}; !slices.Equal(kinds, want) {
			t.Errorf("webhooks %v: kinds = %v, want %v", tc.webhooks, kinds, want)
		}
		for _, s := range []string{tc.args, tc.ports} {
			if !strings.Contains(byKind["Deployment"], s) {
				t.Errorf("webhooks %v: the Deployment lacks %s: %s", tc.webhooks, s, byKind["Deployment"])
			}
		}
		if !strings.Contains(byKind["Service"], tc.service) {
			t.Errorf("webhooks %v: Service = %s, want %s", tc.webhooks, byKind["Service"], tc.service)
		}
		if want := `"lifecycle":{"preStop":{"sleep":{"seconds":5}}}`; !strings.Contains(byKind["Deployment"], want) {
			t.Errorf("webhooks %v: the Deployment lacks %s: %s", tc.webhooks, want, byKind["Deployment"])
		}
	}
	for _, d := range o.manifests("ref", &installPlan{cluster: grants{}, local: grants{}, webhooks: true}) {
		if b, _ := json.Marshal(d); strings.Contains(string(b), "preStop") {
			t.Errorf("a program that doesn't serve waits before it stops: %s", b)
		}
	}
}

func TestGrantsFor(t *testing.T) {
	p := &installPlan{cluster: grants{}, local: grants{}, watched: grants{}}
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
		{"a cluster-scoped type", &typeInfo{scope: "Cluster"}, true, p.cluster},
		{"a type whose scope discovery decides", &typeInfo{}, true, p.cluster},
	} {
		if got := p.grantsFor(tc.ti, tc.watching); !same(got, tc.want) {
			t.Errorf("%s: got the wrong grants", tc.name)
		}
	}
}

func TestManifestsForOneNamespace(t *testing.T) {
	o := &generateOptions{program: "app", name: "app", namespace: "app-system", replicas: 1, shards: 1, watchNamespace: "team"}
	p := &installPlan{cluster: grants{}, local: grants{}, watched: grants{}}
	p.cluster.add("apiextensions.k8s.io", "customresourcedefinitions", "", "create")
	p.watched.add("", "secrets", "", "get")
	byKind := map[string]map[string]any{}
	for _, d := range o.manifests("ref", p) {
		b, _ := json.Marshal(d)
		var m map[string]any
		_ = json.Unmarshal(b, &m)
		byKind[m["kind"].(string)] = m
	}
	role, binding := byKind["Role"], byKind["RoleBinding"]
	if role == nil || role["metadata"].(map[string]any)["namespace"] != "team" {
		t.Fatalf("Role = %v, want one in team", role)
	}
	if b, _ := json.Marshal(role["rules"]); string(b) != `[{"apiGroups":[""],"resources":["secrets"],"verbs":["get"]}]` {
		t.Errorf("Role rules = %s", b)
	}
	if b, _ := json.Marshal(binding["subjects"]); string(b) != `[{"kind":"ServiceAccount","name":"app","namespace":"app-system"}]` {
		t.Errorf("RoleBinding subjects = %s", b)
	}
	if b, _ := json.Marshal(byKind["ClusterRole"]["rules"]); strings.Contains(string(b), "secrets") {
		t.Errorf("ClusterRole rules = %s, want no secrets", b)
	}
	if b, _ := json.Marshal(byKind["Deployment"]); !strings.Contains(string(b), `"args":["-addr=:8080","-namespace=team"]`) {
		t.Errorf("Deployment = %s, want -namespace=team", b)
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
		{[]string{"-registry=ghcr.io/you", "-tmp-size=lots"}, "isn't a quantity"},
		{[]string{"-registry=ghcr.io/you", "-watch-namespace=Team_A"}, "isn't a namespace name"},
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

//go:build !kube_nogenerate

package kube

import (
	"bytes"
	"context"
	"encoding/json"
	"flag"
	"io"
	"maps"
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

type finalizingReconciler struct{ gizmoReconciler }

func (finalizingReconciler) Finalize(context.Context, *gizmo) error { return nil }

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
		{"finalizer", For[gizmo](finalizingReconciler{}), declared{reconciles: true, finalizes: true}},
		{"finalizer from an earlier version", For[gizmo](gizmoReconciler{}, RemovesFinalizer()), declared{reconciles: true, finalizes: true}},
		{"conversion", For[conversionHub](nop[conversionHub]{}, Version[conversionSpoke]()), declared{reconciles: true, webhooks: true, versioned: true}},
		{"no conversion", For[gizmo](gizmoReconciler{}, Version[gizmoV1beta1]()), declared{reconciles: true, versioned: true}},
		{"webhooks", Webhooks[configMapMeta](labeler{}), declared{webhooks: true}},
	} {
		got, err := tc.c.describe()
		if err != nil {
			t.Fatal(err)
		}
		if got.ti == nil || got.reconciles != tc.want.reconciles || got.finalizes != tc.want.finalizes || got.webhooks != tc.want.webhooks || got.versioned != tc.want.versioned || len(got.owns) != len(tc.want.owns) {
			t.Errorf("%s: describe = %+v, want %+v", tc.name, got, tc.want)
		}
		for i, o := range got.owns {
			if o.kind != tc.want.owns[i].kind {
				t.Errorf("%s: owns %s, want %s", tc.name, o.kind, tc.want.owns[i].kind)
			}
		}
	}
}

func TestPlanPatch(t *testing.T) {
	type deployment struct {
		Object `kube:"apiVersion=apps/v1,kind=Deployment"`
	}
	type namespace struct {
		Object `kube:"apiVersion=v1,kind=Namespace,scope=Cluster"`
	}
	const (
		deletes      = "github.com/imjasonh/playground/kube/examples/janitor"
		owns         = "github.com/imjasonh/playground/kube/examples/website"
		genericOwner = "github.com/imjasonh/playground/kube/testdata/genericowner"
	)
	for _, tc := range []struct {
		name  string
		c     Controller
		pkg   string
		watch string
		patch bool
		// role says that the rules for the reconciled type go in the Role
		// in the watched namespace instead of the ClusterRole.
		role bool
	}{
		{"status only", For[gizmo](gizmoReconciler{}), deletes, "", false, false},
		{"finalizer", For[gizmo](finalizingReconciler{}), deletes, "", true, false},
		{"finalizer from an earlier version", For[gizmo](gizmoReconciler{}, RemovesFinalizer()), deletes, "", true, false},
		{"more than one version", For[gizmo](gizmoReconciler{}, Version[gizmoV1beta1]()), deletes, "", true, false},
		{"declared owned type", For[gizmo](gizmoReconciler{}, Owns[deployment]()), deletes, "", true, false},
		{"program that owns objects", For[gizmo](gizmoReconciler{}), owns, "", true, false},
		{"program that owns objects of types that generate can't tell", For[gizmo](gizmoReconciler{}), genericOwner, "", true, false},
		{"cluster-scoped type in a program that owns objects", For[namespace](nop[namespace]{}), owns, "", false, false},
		{"program that owns objects and watches one namespace", For[gizmo](gizmoReconciler{}), owns, "sites", true, true},
		{"more than one version in a program that watches one namespace", For[gizmo](gizmoReconciler{}, Version[gizmoV1beta1]()), deletes, "sites", true, false},
	} {
		o := &generateOptions{program: "test", watchNamespace: tc.watch, platforms: []v1.Platform{{OS: "linux", Architecture: "amd64"}}, replicas: 1, shards: 1, stderr: io.Discard}
		p, err := o.plan(t.Context(), []Controller{tc.c}, tc.pkg)
		if err != nil {
			t.Fatal(err)
		}
		d, err := tc.c.describe()
		if err != nil {
			t.Fatal(err)
		}
		g, r := resourceName(d.ti)
		rules, other, where := p.cluster, p.watched, "ClusterRole"
		if tc.role {
			rules, other, where = p.watched, p.cluster, "Role"
		}
		if got := rules[grantKey{g, r, ""}]["patch"]; got != tc.patch {
			t.Errorf("%s: patch on %s in the %s = %t, want %t", tc.name, r, where, got, tc.patch)
		}
		if other[grantKey{g, r, ""}]["patch"] {
			t.Errorf("%s: patch on %s outside the %s", tc.name, r, where)
		}
		if d.ti.status != nil && !rules[grantKey{g, r + "/status", ""}]["patch"] {
			t.Errorf("%s: no patch on %s/status in the %s", tc.name, r, where)
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
		`"env":[{"name":"KUBE_IMAGE","value":"ghcr.io/you/web-site@sha256:abc"}]`,
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

func TestManifestsTokens(t *testing.T) {
	o := &generateOptions{program: "sts", name: "sts", namespace: "sts", replicas: 1, shards: 1, args: []string{"-v"}}
	docs := o.manifests("ref", &installPlan{cluster: grants{}, local: grants{}, tokens: []string{"https://octo-sts.dev", "probe"}})
	b, _ := json.Marshal(docs[len(docs)-1])
	for _, s := range []string{
		`"args":["-addr=:8080","-token-dir=/var/run/secrets/tokens","-v"]`,
		`"volumeMounts":[{"name":"tmp","mountPath":"/tmp"},{"name":"tokens","mountPath":"/var/run/secrets/tokens","readOnly":true}]`,
		`{"name":"tokens","projected":{"sources":[` +
			`{"serviceAccountToken":{"audience":"https://octo-sts.dev","expirationSeconds":3600,"path":"5ed769dad83e947182558c07a2054d31423885eaab718996164c0f14d4713c35"}},` +
			`{"serviceAccountToken":{"audience":"probe","expirationSeconds":3600,"path":"ba9c736f19e7f60b7f6764adb0b7908c0a2b394e09b6c09863528c7f2bc86095"}}]}}`,
	} {
		if !strings.Contains(string(b), s) {
			t.Errorf("the Deployment lacks %s: %s", s, b)
		}
	}
	docs = o.manifests("ref", &installPlan{cluster: grants{}, local: grants{}})
	if b, _ := json.Marshal(docs[len(docs)-1]); strings.Contains(string(b), "token") {
		t.Errorf("a program that requests no tokens mounts some: %s", b)
	}
}

func TestPlanTokens(t *testing.T) {
	for _, tc := range []struct {
		pkg     string
		tokens  []string
		request bool
	}{
		{"github.com/imjasonh/playground/kube/examples/probe", []string{"probe"}, false},
		{"github.com/imjasonh/playground/kube/testdata/tokens", []string{"https://octo-sts.dev", "probe"}, true},
	} {
		var stderr bytes.Buffer
		o := &generateOptions{program: "prog", name: "prog", namespace: "prog", replicas: 1, shards: 1, platforms: []v1.Platform{{OS: "linux", Architecture: "amd64"}}, stderr: &stderr}
		p, err := o.plan(t.Context(), nil, tc.pkg)
		if err != nil {
			t.Fatal(err)
		}
		if !slices.Equal(p.tokens, tc.tokens) {
			t.Errorf("%s: tokens = %q, want %q", tc.pkg, p.tokens, tc.tokens)
		}
		rules, _ := json.Marshal(p.local.rules())
		if want := `{"apiGroups":[""],"resources":["serviceaccounts/token"],"resourceNames":["prog"],"verbs":["create"]}`; strings.Contains(string(rules), want) != tc.request {
			t.Errorf("%s: Role rules = %s, want the rule %s: %v", tc.pkg, rules, want, tc.request)
		}
		if logged := strings.Contains(stderr.String(), "testdata/tokens/main.go:19:"); logged != tc.request {
			t.Errorf("%s: generate wrote:\n%s\nwant the position of RequestToken with a variable: %v", tc.pkg, stderr.String(), tc.request)
		}
	}
}

func TestManifestsVolume(t *testing.T) {
	o := &generateOptions{program: "eventlog", name: "eventlog", namespace: "eventlog", replicas: 1, shards: 1, volumeSize: "5Gi", storageClass: "fast"}
	byKind := map[string]string{}
	var kinds []string
	for _, d := range o.manifests("ref", &installPlan{cluster: grants{}, local: grants{}, serves: true, volume: "/var/lib/eventlog"}) {
		b, _ := json.Marshal(d)
		kind := d[1].value.(string)
		kinds = append(kinds, kind)
		byKind[kind] = string(b)
	}
	if want := []string{"Namespace", "ServiceAccount", "ClusterRole", "ClusterRoleBinding", "Service", "PersistentVolumeClaim", "Deployment"}; !slices.Equal(kinds, want) {
		t.Errorf("kinds = %v, want %v", kinds, want)
	}
	claim := `{"apiVersion":"v1","kind":"PersistentVolumeClaim","metadata":{"name":"eventlog","namespace":"eventlog","labels":{"app.kubernetes.io/name":"eventlog"}},` +
		`"spec":{"accessModes":["ReadWriteOnce"],"storageClassName":"fast","resources":{"requests":{"storage":"5Gi"}}}}`
	if byKind["PersistentVolumeClaim"] != claim {
		t.Errorf("PersistentVolumeClaim =\n%s\nwant\n%s", byKind["PersistentVolumeClaim"], claim)
	}
	for _, s := range []string{
		`"spec":{"replicas":1,"strategy":{"type":"Recreate"},"selector"`,
		`"securityContext":{"runAsNonRoot":true,"seccompProfile":{"type":"RuntimeDefault"},"fsGroup":65532,"fsGroupChangePolicy":"OnRootMismatch"}`,
		`"volumeMounts":[{"name":"tmp","mountPath":"/tmp"},{"name":"data","mountPath":"/var/lib/eventlog"}]`,
		`"volumes":[{"name":"tmp","emptyDir":{}},{"name":"data","persistentVolumeClaim":{"claimName":"eventlog"}}]`,
		`"args":["-addr=:8080","-serve-addr=:8081"]`,
	} {
		if !strings.Contains(byKind["Deployment"], s) {
			t.Errorf("the Deployment lacks %s: %s", s, byKind["Deployment"])
		}
	}

	o.storageClass = ""
	for _, d := range o.manifests("ref", &installPlan{cluster: grants{}, local: grants{}, volume: "/var/lib/eventlog"}) {
		if b, _ := json.Marshal(d); d[1].value == "PersistentVolumeClaim" && strings.Contains(string(b), "storageClassName") {
			t.Errorf("without -storage-class, the claim names a StorageClass: %s", b)
		}
	}
	for _, d := range o.manifests("ref", &installPlan{cluster: grants{}, local: grants{}}) {
		if b, _ := json.Marshal(d); d[1].value == "PersistentVolumeClaim" || strings.Contains(string(b), "Recreate") || strings.Contains(string(b), "fsGroup") {
			t.Errorf("without a volume: %s", b)
		}
	}
}

func TestPlanVolume(t *testing.T) {
	const pkg = "github.com/imjasonh/playground/kube/examples/eventlog"
	options := func(volumeFlags ...string) *generateOptions {
		return &generateOptions{
			program: "prog", name: "prog", namespace: "prog", replicas: 2, shards: 1, volumeSize: "1Gi", volumeFlags: volumeFlags,
			platforms: []v1.Platform{{OS: "linux", Architecture: "amd64"}}, stderr: io.Discard,
		}
	}
	o := options()
	p, err := o.plan(t.Context(), []Controller{For[gizmo](gizmoReconciler{}), Volume("/var/lib/prog")}, pkg)
	if err != nil {
		t.Fatal(err)
	}
	if p.volume != "/var/lib/prog" || p.electLeader || o.replicas != 1 {
		t.Errorf("volume = %q, electLeader = %v, replicas = %d; want /var/lib/prog, one replica, and no leader election", p.volume, p.electLeader, o.replicas)
	}
	if rules, _ := json.Marshal(p.local.rules()); strings.Contains(string(rules), "leases") {
		t.Errorf("Role rules = %s, want none for leases", rules)
	}

	for _, tc := range []struct {
		name        string
		controllers []Controller
		flags       []string
		want        string
	}{
		{"two volumes", []Controller{Volume("/var/lib/a"), For[gizmo](gizmoReconciler{}), Volume("/var/lib/b")}, nil, "declares more than one kube.Volume"},
		{"-volume-size without a volume", nil, []string{"-volume-size"}, "has no kube.Volume, so leave out -volume-size"},
		{"both flags without a volume", []Controller{For[gizmo](gizmoReconciler{})}, []string{"-storage-class", "-volume-size"}, "leave out -storage-class and -volume-size"},
	} {
		if _, err := options(tc.flags...).plan(t.Context(), tc.controllers, pkg); err == nil || !strings.Contains(err.Error(), tc.want) {
			t.Errorf("%s: err = %v, want %q", tc.name, err, tc.want)
		}
	}
	if _, err := options("-storage-class", "-volume-size").plan(t.Context(), []Controller{Volume("/var/lib/prog")}, pkg); err != nil {
		t.Errorf("a volume with -storage-class and -volume-size: %v", err)
	}
}

func TestOneWriter(t *testing.T) {
	for _, tc := range []struct {
		name         string
		volume       string
		replicas     int
		replicasSet  bool
		shards       int
		wantReplicas int
		wantErr      bool
	}{
		{"no volume", "", 2, false, 1, 2, false},
		{"no volume, shards", "", 3, true, 8, 3, false},
		{"a volume", "/var/lib/app", 2, false, 1, 1, false},
		{"a volume and -replicas=1", "/var/lib/app", 1, true, 1, 1, false},
		{"a volume and -replicas=3", "/var/lib/app", 3, true, 1, 0, true},
		{"a volume and -shards=4", "/var/lib/app", 2, false, 4, 0, true},
	} {
		o := &generateOptions{replicas: tc.replicas, replicasSet: tc.replicasSet, shards: tc.shards}
		err := o.oneWriter(tc.volume)
		switch {
		case tc.wantErr && (err == nil || !strings.Contains(err.Error(), "which one replica writes")):
			t.Errorf("%s: err = %v, want one about the volume", tc.name, err)
		case !tc.wantErr && err != nil:
			t.Errorf("%s: %v", tc.name, err)
		case !tc.wantErr && o.replicas != tc.wantReplicas:
			t.Errorf("%s: replicas = %d, want %d", tc.name, o.replicas, tc.wantReplicas)
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

func TestPlanGrantsStatusOfAppliedTypes(t *testing.T) {
	o := &generateOptions{platforms: []v1.Platform{{OS: "linux", Architecture: "amd64"}}, replicas: 1, shards: 1, stderr: io.Discard}
	p, err := o.plan(t.Context(), nil, "./testdata/applystatus")
	if err != nil {
		t.Fatal(err)
	}
	for _, tc := range []struct {
		group, resource string
		want            []string
	}{
		{"apps", "deployments", []string{"create", "patch"}},
		{"apps", "deployments/status", []string{"patch"}},
		{"", "configmaps", []string{"create", "patch"}},
		{"", "configmaps/status", nil},
		{"", "pods", []string{"list", "watch"}},
		{"", "pods/status", nil},
	} {
		if got := slices.Sorted(maps.Keys(p.cluster[grantKey{tc.group, tc.resource, ""}])); !slices.Equal(got, tc.want) {
			t.Errorf("verbs on %s = %q, want %q", tc.resource, got, tc.want)
		}
	}
}

// TestPlanCRDRules works out the rules of testdata/crdrules, which reads one
// custom type and owns another without reconciling either. The program may
// create the CRD of the type that it owns, and nothing for the type that it
// reads.
func TestPlanCRDRules(t *testing.T) {
	var stderr bytes.Buffer
	o := &generateOptions{program: "crdrules", name: "crdrules", platforms: []v1.Platform{{OS: "linux", Architecture: "amd64"}}, replicas: 1, stderr: &stderr}
	p, err := o.plan(t.Context(), []Controller{For[configMapMeta](nop[configMapMeta]{})}, "github.com/imjasonh/playground/kube/testdata/crdrules")
	if err != nil {
		t.Fatalf("plan: %v\n%s", err, stderr.String())
	}
	got := map[string][]string{}
	for k, verbs := range p.cluster {
		if k.resource == "customresourcedefinitions" {
			got[k.name] = slices.Sorted(maps.Keys(verbs))
		}
	}
	want := map[string][]string{"": {"create"}, "receipts.test.kube.imjasonh.github.io": {"get"}}
	if !reflect.DeepEqual(got, want) {
		t.Errorf("verbs on customresourcedefinitions by name = %v, want %v", got, want)
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

func TestGrantInstalls(t *testing.T) {
	objs, err := parseManifest([]byte(`apiVersion: v1
kind: ConfigMap
metadata:
  name: params
  namespace: policies
---
apiVersion: v1
kind: ConfigMap
metadata:
  name: settings
  namespace: app-system
---
apiVersion: v1
kind: ConfigMap
metadata:
  name: settings
  namespace: team
---
apiVersion: example.dev/v1
kind: Cactus
metadata:
  name: saguaro
  namespace: app-system
---
apiVersion: admissionregistration.k8s.io/v1
kind: ValidatingAdmissionPolicy
metadata:
  name: limits
spec:
  paramKind:
    apiVersion: v1
    kind: ConfigMap
---
apiVersion: admissionregistration.k8s.io/v1
kind: ValidatingAdmissionPolicyBinding
metadata:
  name: limits
spec:
  policyName: limits
  paramRef:
    name: params
    namespace: policies
---
apiVersion: admissionregistration.k8s.io/v1
kind: ValidatingAdmissionPolicyBinding
metadata:
  name: elsewhere
spec:
  policyName: someone-elses
  paramRef:
    name: params
    namespace: policies
`))
	if err != nil {
		t.Fatal(err)
	}
	var stderr bytes.Buffer
	o := &generateOptions{program: "app", name: "app", namespace: "app-system", watchNamespace: "team", stderr: &stderr}
	p := &installPlan{cluster: grants{}, local: grants{}, watched: grants{}, namespaces: map[string]grants{}}
	cactus := &typeInfo{}
	if err := cactus.parseTag("Cactus", "Cactus", "group=example.dev,plural=cacti"); err != nil {
		t.Fatal(err)
	}
	o.grantInstalls(p, objs, map[string]*typeInfo{"example.dev/Cactus": cactus})
	for _, tc := range []struct {
		name string
		g    grants
		want string
	}{
		{"cluster", p.cluster, `[` +
			`{"apiGroups":[""],"resources":["configmaps"],"resourceNames":["*"],"verbs":["get"]},` +
			`{"apiGroups":["admissionregistration.k8s.io"],"resources":["validatingadmissionpolicies","validatingadmissionpolicybindings"],"resourceNames":["limits"],"verbs":["create","patch"]},` +
			`{"apiGroups":["admissionregistration.k8s.io"],"resources":["validatingadmissionpolicybindings"],"resourceNames":["elsewhere"],"verbs":["create","patch"]}]`},
		{"local", p.local, `[` +
			`{"apiGroups":[""],"resources":["configmaps"],"resourceNames":["settings"],"verbs":["create","patch"]},` +
			`{"apiGroups":["example.dev"],"resources":["cacti"],"resourceNames":["saguaro"],"verbs":["create","patch"]}]`},
		{"watched", p.watched, `[` +
			`{"apiGroups":[""],"resources":["configmaps"],"resourceNames":["settings"],"verbs":["create","patch"]}]`},
		{"policies", p.namespaces["policies"], `[` +
			`{"apiGroups":[""],"resources":["configmaps"],"resourceNames":["params"],"verbs":["create","get","patch"]}]`},
	} {
		if b, _ := json.Marshal(tc.g.rules()); string(b) != tc.want {
			t.Errorf("%s rules =\n%s\nwant\n%s", tc.name, b, tc.want)
		}
	}
	if len(p.namespaces) != 1 {
		t.Errorf("namespaces = %v, want only policies", slices.Sorted(maps.Keys(p.namespaces)))
	}
	if !strings.Contains(stderr.String(), "warning: ValidatingAdmissionPolicyBinding elsewhere binds parameters") {
		t.Errorf("stderr = %q, want a warning about the binding whose policy isn't in the manifest", stderr.String())
	}
}

// TestGrantParamKinds grants get on the name "*" only for a paramKind whose
// objects can't have that name.
func TestGrantParamKinds(t *testing.T) {
	objs, err := parseManifest([]byte(`apiVersion: admissionregistration.k8s.io/v1
kind: ValidatingAdmissionPolicy
metadata:
  name: cacti
spec:
  paramKind:
    apiVersion: example.dev/v1
    kind: Cactus
---
apiVersion: admissionregistration.k8s.io/v1
kind: ValidatingAdmissionPolicy
metadata:
  name: roles
spec:
  paramKind:
    apiVersion: rbac.authorization.k8s.io/v1
    kind: ClusterRole
---
apiVersion: admissionregistration.k8s.io/v1
kind: ValidatingAdmissionPolicyBinding
metadata:
  name: roles
spec:
  policyName: roles
  paramRef:
    name: readers
`))
	if err != nil {
		t.Fatal(err)
	}
	cactus := &typeInfo{}
	if err := cactus.parseTag("Cactus", "Cactus", "group=example.dev,plural=cacti"); err != nil {
		t.Fatal(err)
	}
	var stderr bytes.Buffer
	o := &generateOptions{program: "app", name: "app", namespace: "app-system", stderr: &stderr}
	p := &installPlan{cluster: grants{}, local: grants{}, watched: grants{}, namespaces: map[string]grants{}}
	o.grantInstalls(p, objs, map[string]*typeInfo{"example.dev/Cactus": cactus})
	want := `[` +
		`{"apiGroups":["admissionregistration.k8s.io"],"resources":["validatingadmissionpolicies"],"resourceNames":["cacti"],"verbs":["create","patch"]},` +
		`{"apiGroups":["admissionregistration.k8s.io"],"resources":["validatingadmissionpolicies","validatingadmissionpolicybindings"],"resourceNames":["roles"],"verbs":["create","patch"]},` +
		`{"apiGroups":["example.dev"],"resources":["cacti"],"resourceNames":["*"],"verbs":["get"]},` +
		`{"apiGroups":["rbac.authorization.k8s.io"],"resources":["clusterroles"],"resourceNames":["readers"],"verbs":["get"]}]`
	if b, _ := json.Marshal(p.cluster.rules()); string(b) != want {
		t.Errorf("cluster rules =\n%s\nwant\n%s", b, want)
	}
	if !strings.Contains(stderr.String(), "warning: the API server lets only someone who can get every rbac.authorization.k8s.io/v1 ClusterRole create ValidatingAdmissionPolicy roles") {
		t.Errorf("stderr = %q, want a warning about the ClusterRole paramKind", stderr.String())
	}
}

func TestManifestsForInstalledObjects(t *testing.T) {
	o := &generateOptions{program: "app", name: "app", namespace: "app-system", replicas: 1, shards: 1}
	p := &installPlan{cluster: grants{}, local: grants{}, watched: grants{}, namespaces: map[string]grants{"policies": {}, "other": {}}}
	p.namespaces["policies"].add("", "configmaps", "params", "get")
	p.namespaces["other"].add("", "configmaps", "", "create")
	var roles []string
	for _, d := range o.manifests("ref", p) {
		b, _ := json.Marshal(d)
		var m struct {
			Kind     string `json:"kind"`
			Metadata struct {
				Name      string `json:"name"`
				Namespace string `json:"namespace"`
			} `json:"metadata"`
			Subjects []any `json:"subjects"`
		}
		_ = json.Unmarshal(b, &m)
		if m.Kind != "Role" && m.Kind != "RoleBinding" {
			continue
		}
		roles = append(roles, m.Kind+" "+m.Metadata.Namespace+"/"+m.Metadata.Name)
		if b, _ := json.Marshal(m.Subjects); m.Kind == "RoleBinding" && string(b) != `[{"kind":"ServiceAccount","name":"app","namespace":"app-system"}]` {
			t.Errorf("%s subjects = %s", m.Metadata.Namespace, b)
		}
	}
	if want := []string{"Role other/app", "RoleBinding other/app", "Role policies/app", "RoleBinding policies/app"}; !slices.Equal(roles, want) {
		t.Errorf("roles = %q, want %q", roles, want)
	}
}

// TestManifestsForInstalledObjectsAndEventsInDefault checks that objects
// that Install applies in default and events about cluster-scoped objects
// share one Role there, since two Roles with one name would replace each
// other.
func TestManifestsForInstalledObjectsAndEventsInDefault(t *testing.T) {
	o := &generateOptions{program: "app", name: "app", namespace: "app-system", replicas: 1, shards: 1}
	p := &installPlan{cluster: grants{}, local: grants{}, watched: grants{}, namespaces: map[string]grants{"default": {}}, defaultNS: grants{}}
	p.namespaces["default"].add("", "configmaps", "params", "create", "patch")
	p.defaultNS.add("events.k8s.io", "events", "", "create", "patch")
	var roles []string
	for _, d := range o.manifests("ref", p) {
		b, _ := json.Marshal(d)
		var m struct {
			Kind     string `json:"kind"`
			Metadata struct {
				Namespace string `json:"namespace"`
			} `json:"metadata"`
			Rules []struct {
				Resources []string `json:"resources"`
			} `json:"rules"`
		}
		_ = json.Unmarshal(b, &m)
		if m.Kind != "Role" {
			continue
		}
		roles = append(roles, m.Metadata.Namespace)
		var resources []string
		for _, r := range m.Rules {
			resources = append(resources, r.Resources...)
		}
		slices.Sort(resources)
		if want := []string{"configmaps", "events"}; !slices.Equal(resources, want) {
			t.Errorf("the Role in %s covers %q, want %q", m.Metadata.Namespace, resources, want)
		}
	}
	if want := []string{"default"}; !slices.Equal(roles, want) {
		t.Errorf("Roles in %q, want %q", roles, want)
	}
	if got := p.namespaces["default"]; len(got) != 1 {
		t.Errorf("manifests changed the plan's grants in default to %v", got)
	}
}

// installForTest is a program flag for TestParseProgramFlags.
var installForTest = flag.Bool("kube-test-install", true, "install objects")

func TestParseProgramFlags(t *testing.T) {
	t.Cleanup(func() { *installForTest = true })
	if err := parseProgramFlags([]string{"-v", "-namespace=team", "-kube-test-install=false"}); err != nil {
		t.Fatal(err)
	}
	if *installForTest {
		t.Error("the program's flag isn't set")
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
		{[]string{"-registry=ghcr.io/you", "-volume-size=lots"}, "-volume-size \"lots\" isn't a quantity"},
		{[]string{"-registry=ghcr.io/you", "-volume-size=2Gi", "-storage-class=fast"}, "has no kube.Volume, so leave out -storage-class and -volume-size"},
		{[]string{"-registry=ghcr.io/you", "-watch-namespace=Team_A"}, "isn't a namespace name"},
		{[]string{"-registry=ghcr.io/you", "-nope"}, "flag provided but not defined"},
		{[]string{"-registry=ghcr.io/you", "--", "-v", "-nope"}, "the program's flags after --: flag provided but not defined: -nope"},
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

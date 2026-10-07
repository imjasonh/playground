//go:build !kube_nogenerate

package kube

import (
	"bytes"
	"context"
	"encoding/json"
	"errors"
	"flag"
	"fmt"
	"io"
	"log/slog"
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
	o := &generateOptions{program: "web_site", name: "web-site", namespace: "sites", replicas: 3, shards: 1, args: []string{"-log-level=debug"}}
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
		name := "web-site"
		switch m["kind"] {
		case "ClusterRole", "ClusterRoleBinding":
			name = "web-site.sites"
		case "Secret":
			name = "web-site-webhook-tls"
		case "Deployment":
			deployment = m
		case "Service":
			service = m
		}
		if got := m["metadata"].(map[string]any)["name"]; got != name {
			t.Errorf("%s is named %v, want %s", m["kind"], got, name)
		}
		if ref, ok := m["roleRef"].(map[string]any); ok && ref["name"] != name {
			t.Errorf("%s refers to %v, want %s", m["kind"], ref["name"], name)
		}
	}
	want := []string{"ServiceAccount", "ClusterRole", "ClusterRoleBinding", "Role", "RoleBinding", "Secret", "Service", "Deployment", "PodDisruptionBudget"}
	if !slices.Equal(kinds, want) {
		t.Errorf("kinds = %v, want %v", kinds, want)
	}
	b, _ := json.Marshal(deployment)
	for _, s := range []string{
		`"replicas":3`,
		`"image":"ghcr.io/you/web-site@sha256:abc"`,
		`"args":["-metrics-addr=:8080","-leader-elect","-webhook-addr=:9443","-webhook-service=sites/web-site","-log-level=debug"]`,
		`"env":[{"name":"KUBE_IMAGE","value":"ghcr.io/you/web-site@sha256:abc"}]`,
		`"serviceAccountName":"web-site"`,
		`"shareProcessNamespace":true`,
		`"securityContext":{"runAsGroup":65532,"runAsNonRoot":true,"runAsUser":65532,"seccompProfile":{"type":"RuntimeDefault"}}`,
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
	if want := []string{"ServiceAccount", "ClusterRole", "ClusterRoleBinding", "Deployment"}; !slices.Equal(kinds, want) {
		t.Errorf("one replica without webhooks: kinds = %v, want %v", kinds, want)
	}
	b, _ = json.Marshal(docs[len(docs)-1])
	if !strings.Contains(string(b), `"args":["-metrics-addr=:8080","-log-level=debug"]`) {
		t.Errorf("one replica without webhooks: %s", b)
	}
}

// TestManifestsNamespace checks that the YAML creates the namespace only when
// it's the program's own, so that deleting the installation doesn't delete a
// namespace that other programs share.
func TestManifestsNamespace(t *testing.T) {
	for _, tc := range []struct {
		namespace string
		want      []string
	}{
		{namespace: "web-site", want: []string{"web-site"}},
		{namespace: "sites"},
	} {
		o := &generateOptions{program: "web_site", name: "web-site", namespace: tc.namespace, replicas: 1, shards: 1}
		var namespaces []string
		for _, d := range o.manifests("ref", &installPlan{cluster: grants{}, local: grants{}}) {
			if d[1].value == "Namespace" {
				namespaces = append(namespaces, d[2].value.(object)[0].value.(string))
			}
		}
		if !slices.Equal(namespaces, tc.want) {
			t.Errorf("-namespace=%s: the YAML creates the namespaces %q, want %q", tc.namespace, namespaces, tc.want)
		}
	}
}

// TestManifestsWebhookSecret checks that the YAML creates an empty Secret for
// the webhook certificate, which the program may fill in but not create, in
// the namespace where the program keeps it.
func TestManifestsWebhookSecret(t *testing.T) {
	for _, tc := range []struct {
		name, leaseNamespace string
		webhooks             bool
		want                 string
	}{
		{"webhooks", "", true, `{"apiVersion":"v1","kind":"Secret","metadata":{"name":"web-site-webhook-tls","namespace":"sites","labels":{"app.kubernetes.io/name":"web-site"}},"type":"Opaque"}`},
		{"webhooks and a LeaseNamespace", "leases", true, `{"apiVersion":"v1","kind":"Secret","metadata":{"name":"web-site-webhook-tls","namespace":"leases","labels":{"app.kubernetes.io/name":"web-site"}},"type":"Opaque"}`},
		{"no webhooks", "", false, ""},
	} {
		o := &generateOptions{program: "web_site", name: "web-site", namespace: "sites", replicas: 1, shards: 1, manager: Manager{LeaseNamespace: tc.leaseNamespace}}
		var got string
		for _, d := range o.manifests("ref", &installPlan{cluster: grants{}, local: grants{}, webhooks: tc.webhooks}) {
			if d[1].value == "Secret" {
				b, _ := json.Marshal(d)
				got = string(b)
			}
		}
		if got != tc.want {
			t.Errorf("%s: Secret = %s, want %s", tc.name, got, tc.want)
		}
	}
}

// TestManifestsProbes checks that the kubelet probes /readyz every second
// and takes 30 failures in a row to make a ready Pod unready, and probes
// /healthz with Kubernetes' defaults.
func TestManifestsProbes(t *testing.T) {
	o := &generateOptions{program: "prog", name: "prog", namespace: "prog", replicas: 1, shards: 1}
	docs := o.manifests("ref", &installPlan{cluster: grants{}, local: grants{}})
	b, _ := json.Marshal(docs[len(docs)-1])
	for _, s := range []string{
		`"readinessProbe":{"httpGet":{"path":"/readyz","port":"http"},"periodSeconds":1,"failureThreshold":30}`,
		`"livenessProbe":{"httpGet":{"path":"/healthz","port":"http"}}`,
	} {
		if !strings.Contains(string(b), s) {
			t.Errorf("the Deployment lacks %s: %s", s, b)
		}
	}
}

func TestManifestsServe(t *testing.T) {
	o := &generateOptions{program: "probe", name: "probe", namespace: "probe", replicas: 1, shards: 1}
	for _, tc := range []struct {
		webhooks             bool
		kinds                []string
		args, ports, service string
	}{
		{
			false,
			[]string{"Namespace", "ServiceAccount", "ClusterRole", "ClusterRoleBinding", "Service", "Deployment"},
			`"args":["-metrics-addr=:8080","-serve-addr=:8081"]`,
			`"ports":[{"name":"http","containerPort":8080},{"name":"serve","containerPort":8081}]`,
			`"ports":[{"name":"serve","port":80,"targetPort":"serve"}]`,
		},
		{
			true,
			[]string{"Namespace", "ServiceAccount", "ClusterRole", "ClusterRoleBinding", "Secret", "Service", "Deployment"},
			`"args":["-metrics-addr=:8080","-webhook-addr=:9443","-webhook-service=probe/probe","-serve-addr=:8081"]`,
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
		if !slices.Equal(kinds, tc.kinds) {
			t.Errorf("webhooks %v: kinds = %v, want %v", tc.webhooks, kinds, tc.kinds)
		}
		for _, s := range []string{tc.args, tc.ports} {
			if !strings.Contains(byKind["Deployment"], s) {
				t.Errorf("webhooks %v: the Deployment lacks %s: %s", tc.webhooks, s, byKind["Deployment"])
			}
		}
		if !strings.Contains(byKind["Service"], tc.service) {
			t.Errorf("webhooks %v: Service = %s, want %s", tc.webhooks, byKind["Service"], tc.service)
		}
	}
}

// TestManifestsPreStop checks that a program that serves sleeps before it
// stops, so that its Service sends connections to other Pods first, unless
// it has a volume. Then it runs one Pod, which a rollout stops before it
// starts the next.
func TestManifestsPreStop(t *testing.T) {
	const sleep = `"lifecycle":{"preStop":{"sleep":{"seconds":5}}}`
	o := &generateOptions{program: "prog", name: "prog", namespace: "prog", replicas: 1, shards: 1, volumeSize: "1Gi"}
	for _, tc := range []struct {
		name  string
		plan  installPlan
		sleep bool
	}{
		{"a program that serves", installPlan{serves: true}, true},
		{"a program that serves and has webhooks", installPlan{serves: true, webhooks: true}, true},
		{"a program that serves with a volume", installPlan{serves: true, volume: "/var/lib/prog"}, false},
		{"a program with webhooks", installPlan{webhooks: true}, false},
	} {
		tc.plan.cluster, tc.plan.local = grants{}, grants{}
		docs := o.manifests("ref", &tc.plan)
		b, _ := json.Marshal(docs[len(docs)-1])
		if tc.sleep && !strings.Contains(string(b), sleep) {
			t.Errorf("%s: the Deployment lacks %s: %s", tc.name, sleep, b)
		}
		if !tc.sleep && strings.Contains(string(b), "preStop") {
			t.Errorf("%s: the program waits before it stops: %s", tc.name, b)
		}
	}
}

func TestManifestsTokens(t *testing.T) {
	o := &generateOptions{program: "sts", name: "sts", namespace: "sts", replicas: 1, shards: 1, args: []string{"-log-level=debug"}}
	docs := o.manifests("ref", &installPlan{cluster: grants{}, local: grants{}, tokens: []string{"https://octo-sts.dev", "probe"}})
	b, _ := json.Marshal(docs[len(docs)-1])
	for _, s := range []string{
		`"args":["-metrics-addr=:8080","-token-dir=/var/run/secrets/tokens","-log-level=debug"]`,
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
		`"shareProcessNamespace":true`,
		`"securityContext":{"runAsUser":65532,"runAsGroup":65532,"runAsNonRoot":true,"seccompProfile":{"type":"RuntimeDefault"},"fsGroup":65532,"fsGroupChangePolicy":"OnRootMismatch"}`,
		`"volumeMounts":[{"name":"tmp","mountPath":"/tmp"},{"name":"data","mountPath":"/var/lib/eventlog"}]`,
		`"volumes":[{"name":"tmp","emptyDir":{}},{"name":"data","persistentVolumeClaim":{"claimName":"eventlog"}}]`,
		`"args":["-metrics-addr=:8080","-serve-addr=:8081"]`,
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
		{"a local type in a program that watches one namespace", &typeInfo{scope: "Namespaced", local: true}, true, p.local},
		{"a local type in a program that watches every namespace", &typeInfo{scope: "Namespaced", local: true}, false, p.local},
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

// TestPlanCRDRules works out the rules for CustomResourceDefinitions. A
// program applies the CRD of a type that it reconciles, which needs rules
// only for that CRD's name. testdata/crdrules reads one custom type and owns
// another without reconciling either. It may create the CRD of the type that
// it owns, which RBAC can't limit to a name, and gets nothing for the type
// that it reads.
func TestPlanCRDRules(t *testing.T) {
	for _, tc := range []struct {
		name, pkg string
		c         Controller
		want      map[string][]string
	}{
		{
			"reconciled type", "github.com/imjasonh/playground/kube/examples/janitor", For[gizmo](gizmoReconciler{}),
			map[string][]string{"gizmos.test.kube.imjasonh.github.io": {"create", "get", "patch"}},
		},
		{
			"owned and read types", "github.com/imjasonh/playground/kube/testdata/crdrules", For[configMapMeta](nop[configMapMeta]{}),
			map[string][]string{"": {"create"}, "receipts.test.kube.imjasonh.github.io": {"get"}},
		},
	} {
		var stderr bytes.Buffer
		o := &generateOptions{program: "crdrules", name: "crdrules", platforms: []v1.Platform{{OS: "linux", Architecture: "amd64"}}, replicas: 1, stderr: &stderr}
		p, err := o.plan(t.Context(), []Controller{tc.c}, tc.pkg)
		if err != nil {
			t.Fatalf("%s: plan: %v\n%s", tc.name, err, stderr.String())
		}
		got := map[string][]string{}
		for k, verbs := range p.cluster {
			if k.resource == "customresourcedefinitions" {
				got[k.name] = slices.Sorted(maps.Keys(verbs))
			}
		}
		if !reflect.DeepEqual(got, tc.want) {
			t.Errorf("%s: verbs on customresourcedefinitions by name = %v, want %v", tc.name, got, tc.want)
		}
	}
}

// TestPlanWebhookNames checks the names in the rules for webhooks. The
// webhook configurations are cluster-scoped, so their names include the
// program's namespace. The certificate Secret is in that namespace.
func TestPlanWebhookNames(t *testing.T) {
	o := &generateOptions{program: "web_site", name: "web-site", namespace: "sites", replicas: 1, shards: 1, platforms: []v1.Platform{{OS: "linux", Architecture: "amd64"}}, stderr: io.Discard}
	p, err := o.plan(t.Context(), []Controller{For[gizmo](validatingReconciler{})}, "github.com/imjasonh/playground/kube/examples/janitor")
	if err != nil {
		t.Fatal(err)
	}
	got := map[string][]string{}
	for where, g := range map[string]grants{"cluster": p.cluster, "sites": p.local} {
		for k, verbs := range g {
			if strings.HasSuffix(k.resource, "webhookconfigurations") || k.resource == "secrets" {
				got[fmt.Sprintf("%s %s %q", where, k.resource, k.name)] = slices.Sorted(maps.Keys(verbs))
			}
		}
	}
	want := map[string][]string{
		`cluster validatingwebhookconfigurations "web-site.sites"`: {"create", "delete", "get", "patch"},
		`cluster mutatingwebhookconfigurations "web-site.sites"`:   {"delete", "get"},
		`sites secrets "web-site-webhook-tls"`:                     {"get", "update"},
	}
	if !reflect.DeepEqual(got, want) {
		t.Errorf("rules = %v, want %v", got, want)
	}
}

type defaultingReconciler struct{ gizmoReconciler }

func (defaultingReconciler) Default(context.Context, *gizmo, *gizmo) error { return nil }

// TestPlanWebhookConfigurations checks that a program may create and patch
// only the webhook configuration of each kind that it has webhooks of, and
// only by name. It may get and delete both, to remove one that an earlier
// version of the program left. A conversion webhook is in the CRD, so it
// needs neither configuration. Every webhook needs the certificate Secret,
// which the program may read and update but not create.
func TestPlanWebhookConfigurations(t *testing.T) {
	writes, removes := []string{"create", "delete", "get", "patch"}, []string{"delete", "get"}
	for _, tc := range []struct {
		name                 string
		c                    Controller
		validating, mutating []string
		secret               bool
	}{
		{"validating reconciler", For[gizmo](validatingReconciler{}), writes, removes, true},
		{"defaulting reconciler", For[gizmo](defaultingReconciler{}), removes, writes, true},
		{"validating and defaulting webhooks", Webhooks[configMapMeta](labeler{}), writes, writes, true},
		{"validating webhooks", Webhooks[configMapMeta](writer{}), writes, removes, true},
		{"conversion", For[conversionHub](nop[conversionHub]{}, Version[conversionSpoke]()), removes, removes, true},
		{"no webhooks", For[gizmo](gizmoReconciler{}), removes, removes, false},
	} {
		o := &generateOptions{program: "prog", name: "prog", namespace: "prog", replicas: 1, shards: 1, platforms: []v1.Platform{{OS: "linux", Architecture: "amd64"}}, stderr: io.Discard}
		p, err := o.plan(t.Context(), []Controller{tc.c}, "github.com/imjasonh/playground/kube/examples/janitor")
		if err != nil {
			t.Fatal(err)
		}
		got := map[string][]string{}
		for where, g := range map[string]grants{"cluster": p.cluster, "prog": p.local} {
			for k, verbs := range g {
				if strings.HasSuffix(k.resource, "webhookconfigurations") || k.resource == "secrets" {
					got[fmt.Sprintf("%s %s %q", where, k.resource, k.name)] = slices.Sorted(maps.Keys(verbs))
				}
			}
		}
		want := map[string][]string{
			`cluster validatingwebhookconfigurations "prog"`: tc.validating,
			`cluster mutatingwebhookconfigurations "prog"`:   tc.mutating,
		}
		if tc.secret {
			want[`prog secrets "prog-webhook-tls"`] = []string{"get", "update"}
		}
		if !reflect.DeepEqual(got, want) {
			t.Errorf("%s: rules = %v, want %v", tc.name, got, want)
		}
	}
}

// TestPlanLeaseNamespace checks that the rules for the Leases and the
// webhook certificate go in the Manager's LeaseNamespace, which also names
// the webhook configurations, and that a Manager with LeaderElection gets
// the rules for Leases with one replica.
func TestPlanLeaseNamespace(t *testing.T) {
	o := &generateOptions{program: "web_site", name: "web-site", namespace: "sites", replicas: 1, shards: 1, manager: Manager{LeaseNamespace: "leases", LeaderElection: true}, platforms: []v1.Platform{{OS: "linux", Architecture: "amd64"}}, stderr: io.Discard}
	p, err := o.plan(t.Context(), []Controller{For[gizmo](validatingReconciler{})}, "github.com/imjasonh/playground/kube/examples/janitor")
	if err != nil {
		t.Fatal(err)
	}
	if !p.electLeader {
		t.Error("a Manager with LeaderElection doesn't get the rules for Leases")
	}
	got := map[string][]string{}
	for where, g := range map[string]grants{"cluster": p.cluster, "sites": p.local, "leases": p.namespaces["leases"]} {
		for k, verbs := range g {
			if strings.HasSuffix(k.resource, "webhookconfigurations") || k.resource == "secrets" || k.resource == "leases" {
				got[fmt.Sprintf("%s %s %q", where, k.resource, k.name)] = slices.Sorted(maps.Keys(verbs))
			}
		}
	}
	want := map[string][]string{
		`cluster validatingwebhookconfigurations "web-site.leases"`: {"create", "delete", "get", "patch"},
		`cluster mutatingwebhookconfigurations "web-site.leases"`:   {"delete", "get"},
		`leases secrets "web-site-webhook-tls"`:                     {"get", "update"},
		`leases leases ""`:                                          {"create", "delete", "get", "list", "update"},
	}
	if !reflect.DeepEqual(got, want) {
		t.Errorf("rules = %v, want %v", got, want)
	}
}

// TestPlanFetchNames works out the rules of testdata/fetchnames. A Fetch that
// passes a type with a known scope, and constants as the namespace and name,
// may get only that object. Every other Fetch may get every object of its
// type.
func TestPlanFetchNames(t *testing.T) {
	var stderr bytes.Buffer
	o := &generateOptions{program: "prog", name: "prog", namespace: "prog", replicas: 1, shards: 1, platforms: []v1.Platform{{OS: "linux", Architecture: "amd64"}}, stderr: &stderr}
	p, err := o.plan(t.Context(), nil, "github.com/imjasonh/playground/kube/testdata/fetchnames")
	if err != nil {
		t.Fatalf("plan: %v\n%s", err, stderr.String())
	}
	got := map[string][]string{}
	add := func(where string, g grants) {
		for k, verbs := range g {
			if slices.Contains([]string{"configmaps", "namespaces", "secrets", "serviceaccounts", "services", "gadgets"}, k.resource) {
				got[fmt.Sprintf("%s %s %q", where, k.resource, k.name)] = slices.Sorted(maps.Keys(verbs))
			}
		}
	}
	add("cluster", p.cluster)
	add("prog", p.local)
	for ns, g := range p.namespaces {
		add(ns, g)
	}
	want := map[string][]string{
		`config configmaps "settings"`: {"get"},
		`prog configmaps "own"`:        {"get"},
		`cluster namespaces "team"`:    {"get"},
		`cluster secrets ""`:           {"get"},
		`cluster serviceaccounts ""`:   {"get"},
		`cluster gadgets ""`:           {"get"},
		`cluster services ""`:          {"get"},
	}
	if !reflect.DeepEqual(got, want) {
		t.Errorf("rules = %v, want %v", got, want)
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
	if name := role["metadata"].(map[string]any)["name"]; name != "app.app-system" {
		t.Errorf("the Role in team is named %v, want app.app-system", name)
	}
	if ref := binding["roleRef"].(map[string]any)["name"]; ref != "app.app-system" {
		t.Errorf("the RoleBinding in team refers to %v, want app.app-system", ref)
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
	if b, _ := json.Marshal(byKind["Deployment"]); !strings.Contains(string(b), `"args":["-metrics-addr=:8080","-watch-namespace=team"]`) {
		t.Errorf("Deployment = %s, want -watch-namespace=team", b)
	}
}

// TestManifestsFollowManager checks that the Deployment's arguments set the
// program's flags that default to the Manager's fields to the values that
// generate used, even when generate's flags override the fields.
func TestManifestsFollowManager(t *testing.T) {
	for _, tc := range []struct {
		// fieldShards, fieldNamespace, and leaderElection are the Manager's
		// fields, and shards and watch are the values of generate's flags.
		fieldShards    int
		fieldNamespace string
		leaderElection bool
		shards         int
		watch          string
		electLeader    bool
		want           string
	}{
		{shards: 1, want: `"args":["-metrics-addr=:8080"]`},
		{fieldShards: 3, fieldNamespace: "team", shards: 3, watch: "team", electLeader: true, want: `"args":["-metrics-addr=:8080","-shards=3","-watch-namespace=team"]`},
		// generate's -shards=1 and -watch-namespace= override both fields.
		{fieldShards: 3, fieldNamespace: "team", shards: 1, electLeader: true, want: `"args":["-metrics-addr=:8080","-shards=1","-leader-elect","-watch-namespace="]`},
		// A program that reconciles nothing takes no Leases.
		{fieldShards: 3, shards: 3, want: `"args":["-metrics-addr=:8080","-shards=1"]`},
		{leaderElection: true, shards: 1, electLeader: true, want: `"args":["-metrics-addr=:8080","-leader-elect"]`},
	} {
		o := &generateOptions{program: "app", name: "app", namespace: "app", replicas: 1, shards: tc.shards, watchNamespace: tc.watch,
			manager: Manager{Shards: tc.fieldShards, Namespace: tc.fieldNamespace, LeaderElection: tc.leaderElection}}
		docs := o.manifests("ref", &installPlan{cluster: grants{}, local: grants{}, watched: grants{}, electLeader: tc.electLeader})
		if b, _ := json.Marshal(docs[len(docs)-1]); !strings.Contains(string(b), tc.want) {
			t.Errorf("Shards = %d, Namespace = %q, LeaderElection = %v, -shards=%d, and -watch-namespace=%q: the Deployment lacks %s: %s",
				tc.fieldShards, tc.fieldNamespace, tc.leaderElection, tc.shards, tc.watch, tc.want, b)
		}
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
	if want := []string{"Role other/app.app-system", "RoleBinding other/app.app-system", "Role policies/app.app-system", "RoleBinding policies/app.app-system"}; !slices.Equal(roles, want) {
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
	o := &generateOptions{args: []string{"-log-level=debug", "-webhook-url=https://192.0.2.10:9443", "-kube-test-install=false"}}
	if err := o.parseProgramFlags(); err != nil {
		t.Fatal(err)
	}
	if *installForTest {
		t.Error("the program's flag isn't set")
	}
	for _, tc := range []struct {
		args   []string
		logger *slog.Logger
		want   string
	}{
		{[]string{"-metrics-addr=:9090"}, nil, "generate sets -metrics-addr itself"},
		{[]string{"-leader-elect"}, nil, "generate sets -leader-elect itself; generate turns it on when -replicas or -shards is more than 1"},
		{[]string{"-log-level=debug", "-watch-namespace=team"}, nil, "generate sets -watch-namespace itself; set -watch-namespace before -- instead"},
		// Main doesn't define -log-level for a Manager with a Logger.
		{[]string{"-log-level=debug"}, slog.New(slog.DiscardHandler), "flag provided but not defined: -log-level"},
	} {
		o := &generateOptions{args: tc.args, manager: Manager{Logger: tc.logger}}
		if err := o.parseProgramFlags(); err == nil || !strings.Contains(err.Error(), tc.want) {
			t.Errorf("parseProgramFlags with %q = %v, want an error containing %q", tc.args, err, tc.want)
		}
	}
}

// TestParseProgramFlagsDefinedByTheProgram checks that generate fails when
// the program defines a flag that the Deployment sets for kube, and accepts
// one that it doesn't.
func TestParseProgramFlagsDefinedByTheProgram(t *testing.T) {
	saved := flag.CommandLine
	t.Cleanup(func() { flag.CommandLine = saved })
	flag.CommandLine = flag.NewFlagSet("program", flag.ContinueOnError)
	flag.CommandLine.Int("shards", 1, "the program's own shards")
	if err := (&generateOptions{}).parseProgramFlags(); err == nil || !strings.Contains(err.Error(), "the program defines -shards") {
		t.Errorf("parseProgramFlags with the program's own -shards = %v, want an error about -shards", err)
	}
	flag.CommandLine = flag.NewFlagSet("program", flag.ContinueOnError)
	kubeconfig := flag.CommandLine.String("kubeconfig", "", "the program's own kubeconfig")
	if err := (&generateOptions{args: []string{"-kubeconfig=config"}}).parseProgramFlags(); err != nil || *kubeconfig != "config" {
		t.Errorf("parseProgramFlags with the program's own -kubeconfig = %v, and set it to %q; want nil and config", err, *kubeconfig)
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
		{[]string{"-registry=ghcr.io/you", "-namespace=team.a"}, `-namespace "team.a" isn't a namespace name`},
		{[]string{"-registry=ghcr.io/you", "-nope"}, "flag provided but not defined"},
		{[]string{"-registry=ghcr.io/you", "--", "-log-level=debug", "-nope"}, "the program's flags after --: flag provided but not defined: -nope"},
		{[]string{"-registry=ghcr.io/you", "-watch-namespace=a", "--", "-shards=3"}, "the program's flags after --: generate sets -shards itself; set -shards before -- instead"},
	} {
		var stderr bytes.Buffer
		err := (&Manager{}).generate(t.Context(), tc.args, nil, &bytes.Buffer{}, &stderr)
		if err == nil || !strings.Contains(err.Error(), tc.want) {
			t.Errorf("generate %q = %v, want an error containing %q", tc.args, err, tc.want)
		}
	}
	if p, err := v1.ParsePlatform("linux/arm/v7"); err != nil || !reflect.DeepEqual(buildEnv(*p)[len(buildEnv(*p))-1], "GOARM=7") {
		t.Errorf("buildEnv(linux/arm/v7) doesn't set GOARM: %v", err)
	}
}

// TestGenerateFollowsManager checks that generate names the installation
// for the Manager's Name, and that its -watch-namespace and -shards default
// to the Manager's fields, as the program's flags do.
func TestGenerateFollowsManager(t *testing.T) {
	var stderr bytes.Buffer
	m := &Manager{Name: "My_App", Namespace: "team", Shards: 3}
	if err := m.generate(t.Context(), []string{"-h"}, nil, &bytes.Buffer{}, &stderr); !errors.Is(err, flag.ErrHelp) {
		t.Fatalf("generate -h = %v, want flag.ErrHelp", err)
	}
	for _, s := range []string{
		"pushes it to REGISTRY/my-app,",
		`namespace to install the program in (default "my-app")`,
		`go in a Role there (default "team")`,
		"in this many shards (default 3)",
	} {
		if !strings.Contains(stderr.String(), s) {
			t.Errorf("generate -h lacks %q:\n%s", s, stderr.String())
		}
	}
}

func TestDescribeLocal(t *testing.T) {
	for name, c := range map[string]Controller{
		"reconciles": For[localConfigMap](nop[localConfigMap]{}),
		"owns":       For[gizmo](gizmoReconciler{}, Owns[localConfigMap]()),
	} {
		if _, err := c.describe(); err == nil || !strings.Contains(err.Error(), "is local") {
			t.Errorf("a controller that %s a local type: describe err = %v", name, err)
		}
	}
}

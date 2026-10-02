package e2e_test

import (
	"context"
	"encoding/json"
	"io"
	"net/http"
	"reflect"
	"testing"

	"github.com/imjasonh/playground/kube"
	"github.com/imjasonh/playground/kube/internal/client"
	"github.com/imjasonh/playground/kube/internal/e2e"
	"github.com/imjasonh/playground/kube/internal/protobuf"
	"github.com/imjasonh/playground/kube/k8s"
)

const pb = "application/vnd.kubernetes.protobuf"

func readProto(t *testing.T, c *client.Client, path, accept string) []byte {
	t.Helper()
	resp, err := c.Do(t.Context(), client.Request{Method: http.MethodGet, Path: path, Accept: accept})
	if err != nil {
		t.Fatal(err)
	}
	defer resp.Body.Close()
	b, err := io.ReadAll(resp.Body)
	if err != nil {
		t.Fatal(err)
	}
	return b
}

// sameDecoding reads the object at path as JSON and as protobuf and checks
// that both decode into the same T.
func sameDecoding[T any](t *testing.T, c *client.Client, apiVersion, kind, path string) {
	t.Helper()
	var fromJSON T
	if err := e2e.Get(t.Context(), c, path, &fromJSON); err != nil {
		t.Fatal(err)
	}
	gotVersion, gotKind, raw, err := protobuf.Unwrap(readProto(t, c, path, pb))
	if err != nil {
		t.Fatal(err)
	}
	if gotVersion != apiVersion || gotKind != kind {
		t.Errorf("envelope says %s %s, want %s %s", gotVersion, gotKind, apiVersion, kind)
	}
	plan, err := protobuf.For(reflect.TypeFor[T](), apiVersion, kind)
	if err != nil {
		t.Fatal(err)
	}
	var fromProto T
	if err := plan.Unmarshal(raw, &fromProto); err != nil {
		t.Fatal(err)
	}
	setTypeMeta(&fromProto, apiVersion, kind)
	if !reflect.DeepEqual(fromJSON, fromProto) {
		jb, _ := json.Marshal(fromJSON)
		pb, _ := json.Marshal(fromProto)
		t.Errorf("%s decodes differently:\nJSON:     %s\nprotobuf: %s", kind, jb, pb)
	}
}

func setTypeMeta(obj any, apiVersion, kind string) {
	v := reflect.ValueOf(obj).Elem()
	v.FieldByName("APIVersion").SetString(apiVersion)
	v.FieldByName("Kind").SetString(kind)
}

func TestProtobufDecodesLikeJSON(t *testing.T) {
	c := e2e.Client(t)
	ns := e2e.Namespace(t, c)
	ctx := t.Context()
	create := func(apiVersion, plural, namespace string, obj map[string]any) {
		t.Helper()
		if err := c.Create(ctx, client.Path(apiVersion, plural, namespace, ""), obj, nil); err != nil {
			t.Fatalf("creating %s: %v", plural, err)
		}
	}
	status := func(apiVersion, plural, namespace, name, body string) {
		t.Helper()
		if err := c.Patch(ctx, client.Path(apiVersion, plural, namespace, name, "status"), client.MergePatch, nil, []byte(body), nil); err != nil {
			t.Fatalf("writing %s status: %v", plural, err)
		}
	}
	podSpec := map[string]any{
		"serviceAccountName": "default", "nodeName": "node-1", "nodeSelector": map[string]string{"disk": "ssd"},
		"restartPolicy": "Always", "terminationGracePeriodSeconds": 15,
		"imagePullSecrets": []any{map[string]any{"name": "registry"}},
		"initContainers":   []any{map[string]any{"name": "init", "image": "busybox", "command": []string{"sh", "-c", "true"}}},
		"containers": []any{map[string]any{
			"name": "app", "image": "registry.example.com/app:1", "imagePullPolicy": "IfNotPresent",
			"args": []string{"--port=8080"}, "workingDir": "/srv",
			"env": []any{
				map[string]any{"name": "PLAIN", "value": "1"},
				map[string]any{"name": "FROM_CM", "valueFrom": map[string]any{"configMapKeyRef": map[string]any{"name": "settings", "key": "color", "optional": true}}},
				map[string]any{"name": "FROM_SECRET", "valueFrom": map[string]any{"secretKeyRef": map[string]any{"name": "creds", "key": "token"}}},
				map[string]any{"name": "POD_IP", "valueFrom": map[string]any{"fieldRef": map[string]any{"fieldPath": "status.podIP"}}},
			},
			"envFrom":        []any{map[string]any{"prefix": "CM_", "configMapRef": map[string]any{"name": "settings"}}, map[string]any{"secretRef": map[string]any{"name": "creds", "optional": false}}},
			"ports":          []any{map[string]any{"name": "http", "containerPort": 8080, "protocol": "TCP"}, map[string]any{"containerPort": 9090}},
			"resources":      map[string]any{"requests": map[string]string{"cpu": "250m", "memory": "64Mi"}, "limits": map[string]string{"memory": "1Gi"}},
			"volumeMounts":   []any{map[string]any{"name": "config", "mountPath": "/etc/app", "readOnly": true}, map[string]any{"name": "scratch", "mountPath": "/tmp", "subPath": "x"}},
			"readinessProbe": map[string]any{"httpGet": map[string]any{"path": "/ready", "port": 8080}, "initialDelaySeconds": 2, "periodSeconds": 5},
			"livenessProbe":  map[string]any{"tcpSocket": map[string]any{"port": "http"}, "failureThreshold": 4},
		}, map[string]any{
			"name": "sidecar", "image": "proxy:1",
			"livenessProbe": map[string]any{"exec": map[string]any{"command": []string{"healthcheck"}}},
		}},
		"volumes": []any{
			map[string]any{"name": "config", "configMap": map[string]any{"name": "settings", "optional": true}},
			map[string]any{"name": "creds", "secret": map[string]any{"secretName": "creds"}},
			map[string]any{"name": "scratch", "emptyDir": map[string]any{"medium": "Memory", "sizeLimit": "1Gi"}},
			map[string]any{"name": "data", "persistentVolumeClaim": map[string]any{"claimName": "data", "readOnly": true}},
		},
	}
	labels := map[string]string{"app": "web", "tier": "frontend"}
	meta := func(name string) map[string]any {
		return map[string]any{"name": name, "labels": labels, "annotations": map[string]string{"example.com/note": "hello"}}
	}

	create("v1", "pods", ns, map[string]any{"apiVersion": "v1", "kind": "Pod", "metadata": meta("web"), "spec": podSpec})
	status("v1", "pods", ns, "web", `{"status":{"phase":"Running","podIP":"10.0.0.7","conditions":[{"type":"Ready","status":"True","reason":"Ok","message":"ready"}]}}`)
	sameDecoding[k8s.Pod](t, c, "v1", "Pod", client.Path("v1", "pods", ns, "web"))

	create("apps/v1", "deployments", ns, map[string]any{"apiVersion": "apps/v1", "kind": "Deployment", "metadata": meta("web"), "spec": map[string]any{
		"replicas": 3, "paused": true,
		"selector": map[string]any{"matchLabels": labels, "matchExpressions": []any{map[string]any{"key": "tier", "operator": "In", "values": []string{"frontend"}}}},
		"template": map[string]any{"metadata": map[string]any{"labels": labels, "annotations": map[string]string{"a": "b"}}, "spec": podSpec},
	}})
	status("apps/v1", "deployments", ns, "web", `{"status":{"observedGeneration":1,"replicas":3,"updatedReplicas":3,"readyReplicas":2,"availableReplicas":2,"conditions":[{"type":"Available","status":"False"}]}}`)
	sameDecoding[k8s.Deployment](t, c, "apps/v1", "Deployment", client.Path("apps/v1", "deployments", ns, "web"))

	create("v1", "services", ns, map[string]any{"apiVersion": "v1", "kind": "Service", "metadata": meta("web"), "spec": map[string]any{
		"type": "LoadBalancer", "selector": labels,
		"ports": []any{map[string]any{"name": "http", "port": 80, "targetPort": 8080}, map[string]any{"name": "metrics", "port": 9090, "targetPort": "metrics", "protocol": "TCP"}},
	}})
	status("v1", "services", ns, "web", `{"status":{"loadBalancer":{"ingress":[{"ip":"192.0.2.1"},{"hostname":"lb.example.com"}]}}}`)
	sameDecoding[k8s.Service](t, c, "v1", "Service", client.Path("v1", "services", ns, "web"))

	create("v1", "configmaps", ns, map[string]any{"apiVersion": "v1", "kind": "ConfigMap", "metadata": meta("settings"),
		"data": map[string]string{"color": "blue", "empty": ""}, "binaryData": map[string][]byte{"blob": {0, 1, 2, 255}}, "immutable": true})
	sameDecoding[k8s.ConfigMap](t, c, "v1", "ConfigMap", client.Path("v1", "configmaps", ns, "settings"))

	create("v1", "secrets", ns, map[string]any{"apiVersion": "v1", "kind": "Secret", "metadata": meta("creds"), "type": "Opaque",
		"data": map[string][]byte{"token": []byte("s3cret"), "bin": {0, 255}}, "immutable": false})
	sameDecoding[k8s.Secret](t, c, "v1", "Secret", client.Path("v1", "secrets", ns, "creds"))

	create("v1", "serviceaccounts", ns, map[string]any{"apiVersion": "v1", "kind": "ServiceAccount", "metadata": meta("robot")})
	sameDecoding[k8s.ServiceAccount](t, c, "v1", "ServiceAccount", client.Path("v1", "serviceaccounts", ns, "robot"))

	create("v1", "resourcequotas", ns, map[string]any{"apiVersion": "v1", "kind": "ResourceQuota", "metadata": meta("quota"),
		"spec": map[string]any{"hard": map[string]string{"pods": "10", "requests.cpu": "4", "requests.memory": "8Gi"}}})
	sameDecoding[k8s.ResourceQuota](t, c, "v1", "ResourceQuota", client.Path("v1", "resourcequotas", ns, "quota"))

	create("batch/v1", "jobs", ns, map[string]any{"apiVersion": "batch/v1", "kind": "Job", "metadata": meta("once"), "spec": map[string]any{
		"backoffLimit": 2, "ttlSecondsAfterFinished": 60,
		"template": map[string]any{"metadata": map[string]any{"labels": map[string]string{"job": "once"}}, "spec": map[string]any{
			"restartPolicy": "Never", "containers": []any{map[string]any{"name": "run", "image": "busybox"}}}},
	}})
	status("batch/v1", "jobs", ns, "once", `{"status":{"active":1,"failed":2}}`)
	sameDecoding[k8s.Job](t, c, "batch/v1", "Job", client.Path("batch/v1", "jobs", ns, "once"))

	create("rbac.authorization.k8s.io/v1", "roles", ns, map[string]any{"apiVersion": "rbac.authorization.k8s.io/v1", "kind": "Role", "metadata": meta("reader"),
		"rules": []any{map[string]any{"apiGroups": []string{""}, "resources": []string{"pods", "configmaps"}, "resourceNames": []string{"web"}, "verbs": []string{"get", "list"}}}})
	sameDecoding[k8s.Role](t, c, "rbac.authorization.k8s.io/v1", "Role", client.Path("rbac.authorization.k8s.io/v1", "roles", ns, "reader"))

	create("rbac.authorization.k8s.io/v1", "rolebindings", ns, map[string]any{"apiVersion": "rbac.authorization.k8s.io/v1", "kind": "RoleBinding", "metadata": meta("readers"),
		"subjects": []any{map[string]any{"kind": "ServiceAccount", "name": "robot", "namespace": ns}, map[string]any{"kind": "Group", "name": "devs", "apiGroup": "rbac.authorization.k8s.io"}},
		"roleRef":  map[string]any{"apiGroup": "rbac.authorization.k8s.io", "kind": "Role", "name": "reader"}})
	sameDecoding[k8s.RoleBinding](t, c, "rbac.authorization.k8s.io/v1", "RoleBinding", client.Path("rbac.authorization.k8s.io/v1", "rolebindings", ns, "readers"))

	create("networking.k8s.io/v1", "ingresses", ns, map[string]any{"apiVersion": "networking.k8s.io/v1", "kind": "Ingress", "metadata": meta("web"), "spec": map[string]any{
		"ingressClassName": "nginx",
		"tls":              []any{map[string]any{"hosts": []string{"web.example.com"}, "secretName": "web-tls"}},
		"rules": []any{map[string]any{"host": "web.example.com", "http": map[string]any{"paths": []any{
			map[string]any{"path": "/", "pathType": "Prefix", "backend": map[string]any{"service": map[string]any{"name": "web", "port": map[string]any{"number": 80}}}},
			map[string]any{"path": "/metrics", "pathType": "Exact", "backend": map[string]any{"service": map[string]any{"name": "web", "port": map[string]any{"name": "metrics"}}}},
		}}}},
	}})
	sameDecoding[k8s.Ingress](t, c, "networking.k8s.io/v1", "Ingress", client.Path("networking.k8s.io/v1", "ingresses", ns, "web"))

	node := "protobuf-" + ns
	create("v1", "nodes", "", map[string]any{"apiVersion": "v1", "kind": "Node", "metadata": meta(node), "spec": map[string]any{
		"unschedulable": true, "taints": []any{map[string]any{"key": "dedicated", "value": "gpu", "effect": "NoSchedule"}, map[string]any{"key": "spot", "effect": "PreferNoSchedule"}},
	}})
	t.Cleanup(func() {
		_ = c.Delete(context.WithoutCancel(ctx), client.Path("v1", "nodes", "", node), client.DeleteOptions{})
	})
	status("v1", "nodes", "", node, `{"status":{"capacity":{"cpu":"8","memory":"32Gi","pods":"110"},"allocatable":{"cpu":"7500m","memory":"30Gi"},"conditions":[{"type":"Ready","status":"True","reason":"KubeletReady","message":"kubelet is posting ready status"}]}}`)
	sameDecoding[k8s.Node](t, c, "v1", "Node", client.Path("v1", "nodes", "", node))
	sameDecoding[k8s.Namespace](t, c, "v1", "Namespace", client.Path("v1", "namespaces", "", ns))

	t.Log("Lists decode item by item, and metadata-only reads decode too.")
	var jsonList struct {
		Items []k8s.ConfigMap `json:"items"`
	}
	if err := e2e.Get(ctx, c, client.Path("v1", "configmaps", ns, ""), &jsonList); err != nil {
		t.Fatal(err)
	}
	_, _, raw, err := protobuf.Unwrap(readProto(t, c, client.Path("v1", "configmaps", ns, ""), pb))
	if err != nil {
		t.Fatal(err)
	}
	plan, err := protobuf.For(reflect.TypeFor[k8s.ConfigMap](), "v1", "ConfigMap")
	if err != nil {
		t.Fatal(err)
	}
	var protoItems []k8s.ConfigMap
	rv, _, err := protobuf.List(raw, func(item []byte) error {
		var cm k8s.ConfigMap
		if err := plan.Unmarshal(item, &cm); err != nil {
			return err
		}
		protoItems = append(protoItems, cm)
		return nil
	})
	if err != nil || rv == "" || len(protoItems) != len(jsonList.Items) {
		t.Fatalf("protobuf list: resource version %q, %d items, %v; JSON list has %d items", rv, len(protoItems), err, len(jsonList.Items))
	}
	for i := range protoItems {
		if !reflect.DeepEqual(protoItems[i], jsonList.Items[i]) {
			t.Errorf("list item %d decodes differently:\n%+v\n%+v", i, jsonList.Items[i], protoItems[i])
		}
	}

	type podMeta struct {
		kube.Object `kube:"apiVersion=v1,kind=Pod"`
	}
	path := client.Path("v1", "pods", ns, "web")
	var jsonMeta podMeta
	if err := c.Call(ctx, client.Request{Method: http.MethodGet, Path: path, Accept: "application/json;as=PartialObjectMetadata;g=meta.k8s.io;v=v1"}, &jsonMeta); err != nil {
		t.Fatal(err)
	}
	_, kind, raw, err := protobuf.Unwrap(readProto(t, c, path, pb+";as=PartialObjectMetadata;g=meta.k8s.io;v=v1"))
	if err != nil || kind != "PartialObjectMetadata" {
		t.Fatalf("metadata-only protobuf read: kind %q, %v", kind, err)
	}
	metaPlan, err := protobuf.For(reflect.TypeFor[podMeta](), "meta.k8s.io/v1", "PartialObjectMetadata")
	if err != nil {
		t.Fatal(err)
	}
	var protoMeta podMeta
	if err := metaPlan.Unmarshal(raw, &protoMeta); err != nil {
		t.Fatal(err)
	}
	setTypeMeta(&protoMeta, jsonMeta.APIVersion, jsonMeta.Kind)
	if !reflect.DeepEqual(jsonMeta, protoMeta) {
		t.Errorf("metadata-only reads decode differently:\n%+v\n%+v", jsonMeta, protoMeta)
	}
}

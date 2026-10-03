package main

import (
	"encoding/json"
	"fmt"
	"slices"
	"strings"
	"testing"
	"time"

	"github.com/imjasonh/playground/kube"
	"github.com/imjasonh/playground/kube/internal/client"
	"github.com/imjasonh/playground/kube/internal/e2e"
	"github.com/imjasonh/playground/kube/k8s"
)

func TestMain(m *testing.M) { e2e.Main(m) }

func deployment(annotations map[string]string, configMap string) *Deployment {
	d := &Deployment{Object: kube.Meta("web", nil)}
	d.Namespace, d.Annotations = "shop", annotations
	d.Spec.Template.Spec.Containers = []k8s.Container{{
		Name:    "app",
		EnvFrom: []k8s.EnvFromSource{{ConfigMapRef: &k8s.LocalName{Name: configMap}}},
	}}
	return d
}

func configMap(name, value string) *k8s.ConfigMap {
	cm := &k8s.ConfigMap{Object: kube.Meta(name, nil), Data: map[string]string{"level": value}}
	cm.Namespace = "shop"
	return cm
}

func hashFor(t *testing.T, d *Deployment, world ...any) string {
	t.Helper()
	ctx, rec := kube.Fake(t.Context(), d, world...)
	if err := (reloader{}).Reconcile(ctx, d); err != nil {
		t.Fatal(err)
	}
	applied := kube.Applied[Deployment](rec)
	if len(applied) != 1 {
		t.Fatalf("applied %d Deployments, want 1", len(applied))
	}
	return applied[0].Spec.Template.Metadata.Annotations[hashName]
}

func TestHashFollowsConfigMapData(t *testing.T) {
	d := deployment(map[string]string{enabled: "true"}, "settings")
	h1 := hashFor(t, d, configMap("settings", "debug"))
	if h1 != hashFor(t, d, configMap("settings", "debug")) {
		t.Error("hash isn't stable for the same data")
	}
	if h1 == hashFor(t, d, configMap("settings", "info")) {
		t.Error("hash didn't change with the data")
	}
	if h1 == hashFor(t, d) {
		t.Error("hash didn't change when the ConfigMap was deleted")
	}
}

func TestIgnoresDeploymentsThatDidNotOptIn(t *testing.T) {
	d := deployment(nil, "settings")
	ctx, rec := kube.Fake(t.Context(), d, configMap("settings", "debug"))
	if err := (reloader{}).Reconcile(ctx, d); err != nil {
		t.Fatal(err)
	}
	if applied := kube.Applied[Deployment](rec); len(applied) != 0 {
		t.Errorf("applied %+v, want nothing", applied)
	}
}

func TestReferences(t *testing.T) {
	var spec k8s.PodSpec
	if err := json.Unmarshal([]byte(`{
		"volumes": [{"name": "a", "configMap": {"name": "vol-cm"}}, {"name": "b", "secret": {"secretName": "vol-secret"}}],
		"initContainers": [{"name": "init", "envFrom": [{"secretRef": {"name": "init-secret"}}]}],
		"containers": [{"name": "app",
			"envFrom": [{"configMapRef": {"name": "env-cm"}}],
			"env": [{"name": "X", "valueFrom": {"configMapKeyRef": {"name": "vol-cm", "key": "x"}}},
			        {"name": "Y", "valueFrom": {"secretKeyRef": {"name": "key-secret", "key": "y"}}}]}]
	}`), &spec); err != nil {
		t.Fatal(err)
	}
	cms, secrets := references(spec)
	if want := []string{"env-cm", "vol-cm"}; !slices.Equal(cms, want) {
		t.Errorf("ConfigMaps = %v, want %v", cms, want)
	}
	if want := []string{"init-secret", "key-secret", "vol-secret"}; !slices.Equal(secrets, want) {
		t.Errorf("Secrets = %v, want %v", secrets, want)
	}
}

func TestEndToEnd(t *testing.T) {
	c := e2e.Client(t)
	e2e.Run(t, &kube.Manager{Name: "reloader-e2e"}, kube.For[Deployment](reloader{}, kube.Named("reloader")))
	ctx := t.Context()
	ns := e2e.Namespace(t, c)

	create := func(path string, obj map[string]any) {
		t.Helper()
		if err := c.Create(ctx, path, obj, nil); err != nil {
			t.Fatal(err)
		}
	}
	create(client.Path("v1", "configmaps", ns, ""), map[string]any{
		"apiVersion": "v1", "kind": "ConfigMap", "metadata": map[string]any{"name": "settings"}, "data": map[string]string{"level": "debug"},
	})
	create(client.Path("v1", "secrets", ns, ""), map[string]any{
		"apiVersion": "v1", "kind": "Secret", "metadata": map[string]any{"name": "creds"}, "stringData": map[string]string{"token": "a"},
	})
	for name, annotations := range map[string]map[string]string{"web": {enabled: "true"}, "batch": nil} {
		create(client.Path("apps/v1", "deployments", ns, ""), map[string]any{
			"apiVersion": "apps/v1", "kind": "Deployment",
			"metadata": map[string]any{"name": name, "annotations": annotations},
			"spec": map[string]any{
				"selector": map[string]any{"matchLabels": map[string]string{"app": name}},
				"template": map[string]any{
					"metadata": map[string]any{"labels": map[string]string{"app": name}},
					"spec": map[string]any{
						"containers": []any{map[string]any{"name": "app", "image": "nginx:1.27", "envFrom": []any{map[string]any{"configMapRef": map[string]string{"name": "settings"}}}}},
						"volumes":    []any{map[string]any{"name": "creds", "secret": map[string]string{"secretName": "creds"}}},
					},
				},
			},
		})
	}
	hash := func(name string) (string, error) {
		var d k8s.Deployment
		if err := e2e.Get(ctx, c, client.Path("apps/v1", "deployments", ns, name), &d); err != nil {
			return "", err
		}
		return d.Spec.Template.Metadata.Annotations[hashName], nil
	}
	changedFrom := func(old string) (string, error) {
		h, err := hash("web")
		if err != nil {
			return "", err
		}
		if h == "" || h == old {
			return "", fmt.Errorf("hash = %q, want a new value", h)
		}
		return h, nil
	}

	t.Log("An opted-in Deployment gets a hash of its ConfigMaps and Secrets on its pod template.")
	var h1 string
	e2e.Eventually(t, 10*time.Second, func() (err error) { h1, err = changedFrom(""); return err })
	if h, _ := hash("batch"); h != "" {
		t.Errorf("Deployment without the annotation got hash %q", h)
	}

	t.Log("Changing the ConfigMap's data changes the hash, which rolls the pods.")
	if err := c.Patch(ctx, client.Path("v1", "configmaps", ns, "settings"), client.MergePatch, nil, []byte(`{"data":{"level":"info"}}`), nil); err != nil {
		t.Fatal(err)
	}
	var h2 string
	e2e.Eventually(t, 10*time.Second, func() (err error) { h2, err = changedFrom(h1); return err })

	t.Log("So does changing the Secret.")
	if err := c.Patch(ctx, client.Path("v1", "secrets", ns, "creds"), client.MergePatch, nil, []byte(`{"stringData":{"token":"b"}}`), nil); err != nil {
		t.Fatal(err)
	}
	e2e.Eventually(t, 10*time.Second, func() error { _, err := changedFrom(h2); return err })

	t.Log("The controller manages only the hash annotation; it doesn't own any other field.")
	var raw struct {
		Metadata struct {
			ManagedFields []struct {
				Manager  string          `json:"manager"`
				FieldsV1 json.RawMessage `json:"fieldsV1"`
			} `json:"managedFields"`
		} `json:"metadata"`
	}
	if err := c.Get(ctx, client.Path("apps/v1", "deployments", ns, "web"), &raw); err != nil {
		t.Fatal(err)
	}
	for _, mf := range raw.Metadata.ManagedFields {
		if !strings.HasPrefix(mf.Manager, "reloader/") {
			continue
		}
		want := `{"f:spec":{"f:template":{"f:metadata":{"f:annotations":{"f:` + hashName + `":{}}}}}}`
		if string(mf.FieldsV1) != want {
			t.Errorf("reloader manages %s, want only the hash annotation", mf.FieldsV1)
		}
		return
	}
	t.Error("no field manager for the reloader")
}

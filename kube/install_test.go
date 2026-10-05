package kube

import (
	"reflect"
	"strings"
	"testing"
)

const testManifest = `# The policy's parameter.
---
apiVersion: v1
kind: ConfigMap
metadata:
  name: limits
  namespace: policies
  labels:
    team: web
data:
  replicas: "5"
--- # The policy.
---
apiVersion: admissionregistration.k8s.io/v1
kind: ValidatingAdmissionPolicy
metadata:
  name: limits
spec:
  validations:
    - expression: >-
        object.spec.replicas <= int(params.data.replicas)
---
`

func TestParseManifest(t *testing.T) {
	objs, err := parseManifest([]byte(testManifest))
	if err != nil {
		t.Fatal(err)
	}
	if len(objs) != 2 {
		t.Fatalf("got %d objects, want 2: %+v", len(objs), objs)
	}
	for i, want := range []installObject{
		{apiVersion: "v1", kind: "ConfigMap", namespace: "policies", name: "limits"},
		{apiVersion: "admissionregistration.k8s.io/v1", kind: "ValidatingAdmissionPolicy", name: "limits"},
	} {
		got := objs[i]
		got.body = nil
		if !reflect.DeepEqual(got, want) {
			t.Errorf("object %d = %+v, want %+v", i, got, want)
		}
	}
	if got := objs[0].body["data"]; !reflect.DeepEqual(got, map[string]any{"replicas": "5"}) {
		t.Errorf("data = %v", got)
	}
	validations := objs[1].body["spec"].(map[string]any)["validations"].([]any)
	if got := validations[0].(map[string]any)["expression"]; got != "object.spec.replicas <= int(params.data.replicas)" {
		t.Errorf("expression = %q", got)
	}
	if objs, err := parseManifest(nil); err != nil || len(objs) != 0 {
		t.Errorf("parseManifest(nil) = %v, %v", objs, err)
	}
}

func TestParseManifestErrors(t *testing.T) {
	for _, tc := range []struct {
		manifest, want string
	}{
		{"apiVersion: v1\nkind: ConfigMap\n", "document 1 needs apiVersion, kind, and metadata.name"},
		{"apiVersion: v1\nkind: ConfigMap\nmetadata:\n  name: a\n---\nkind: Secret\nmetadata:\n  name: b\n", "document 2 needs apiVersion"},
		{"- a\n- b\n", "document 1 isn't an object"},
		{"apiVersion: v1\nkind: ConfigMap\nmetadata: &meta\n  name: a\n", "anchors, aliases, and tags are not supported"},
	} {
		if _, err := parseManifest([]byte(tc.manifest)); err == nil || !strings.Contains(err.Error(), tc.want) {
			t.Errorf("parseManifest(%q) = %v, want an error containing %q", tc.manifest, err, tc.want)
		}
	}
}

func TestInstall(t *testing.T) {
	manifest := []byte(testManifest)
	c := Install(func() []byte { return manifest })
	d, err := c.describe()
	if err != nil {
		t.Fatal(err)
	}
	if d.reconciles || d.webhooks || len(d.installs) != 2 {
		t.Errorf("describe = %+v, want two objects to install", d)
	}
	in := c.(*installer)
	if err := in.prepare(t.Context(), &Manager{Name: "my_app", Domain: "example.dev"}); err != nil {
		t.Fatal(err)
	}
	for i, want := range []map[string]any{
		{"team": "web", "example.dev/managed-by": "my_app"},
		{"example.dev/managed-by": "my_app"},
	} {
		if got := in.objects[i].body["metadata"].(map[string]any)["labels"]; !reflect.DeepEqual(got, want) {
			t.Errorf("object %d's labels = %v, want %v", i, got, want)
		}
	}

	manifest = nil
	if d, err := c.describe(); err != nil || len(d.installs) != 0 {
		t.Errorf("describe with no manifest = %+v, %v", d, err)
	}
	manifest = []byte("kind: ConfigMap\n")
	if err := in.prepare(t.Context(), &Manager{}); err == nil || !strings.HasPrefix(err.Error(), "kube.Install: document 1") {
		t.Errorf("prepare with a bad manifest = %v", err)
	}
}

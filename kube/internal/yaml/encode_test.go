package yaml

import (
	"encoding/json"
	"reflect"
	"strings"
	"testing"
)

func TestFromJSON(t *testing.T) {
	in := `{
		"apiVersion": "apps/v1",
		"kind": "Deployment",
		"metadata": {"name": "web", "labels": {"app.kubernetes.io/name": "web"}, "annotations": {}},
		"spec": {
			"replicas": 2,
			"paused": false,
			"template": {"spec": {
				"containers": [{
					"name": "web",
					"image": "ghcr.io/you/web@sha256:0123abcd",
					"args": ["-addr=:8080", "-leader-elect"],
					"ports": [{"name": "http", "containerPort": 8080}],
					"env": [],
					"resources": {"requests": {"cpu": "50m", "memory": "64Mi"}}
				}],
				"tolerations": [{}],
				"nested": [[1, 2], []]
			}}
		},
		"tricky": ["on", "yes", "No", "true", "null", "", "1:20", "2026-10-02", "0x1F", ".5", ".inf",
			"a: b", "a #b", "#c", "- x", "x:", "*alias", "&anchor", "!tag", "multi\nline", "tab\tchar", "quote\"d",
			"ünïcode", "=", "<<", "plain-word_1.2", "/path/to", "_under", "k=v", "image@sha256:ab"],
		"nothing": null,
		"float": 1.5
	}`
	out, err := FromJSON([]byte(in))
	if err != nil {
		t.Fatal(err)
	}
	got, err := Parse(out)
	if err != nil {
		t.Fatalf("parsing the output: %v\n%s", err, out)
	}
	var want any
	if err := json.Unmarshal([]byte(in), &want); err != nil {
		t.Fatal(err)
	}
	gotJSON, _ := json.Marshal(got)
	var gotAny any
	_ = json.Unmarshal(gotJSON, &gotAny)
	if !reflect.DeepEqual(gotAny, want) {
		t.Errorf("round trip changed the value:\n%s", out)
	}
	for _, line := range []string{
		"apiVersion: apps/v1\n",
		"  labels:\n    app.kubernetes.io/name: web\n",
		"  annotations: {}\n",
		"      containers:\n      - name: web\n        image: ghcr.io/you/web@sha256:0123abcd\n        args:\n        - \"-addr=:8080\"\n",
		"        ports:\n        - name: http\n          containerPort: 8080\n",
		"        env: []\n",
		"          cpu: \"50m\"\n",
		"- \"on\"\n",
		"- \"1:20\"\n",
		"- plain-word_1.2\n",
		"- image@sha256:ab\n",
	} {
		if !strings.Contains(string(out), line) {
			t.Errorf("output doesn't contain %q:\n%s", line, out)
		}
	}
}

func TestFromJSONKeepsKeyOrder(t *testing.T) {
	out, err := FromJSON([]byte(`{"kind":"A","apiVersion":"v1","metadata":{"z":1,"a":2}}`))
	if err != nil {
		t.Fatal(err)
	}
	want := "kind: A\napiVersion: v1\nmetadata:\n  z: 1\n  a: 2\n"
	if string(out) != want {
		t.Errorf("got\n%s\nwant\n%s", out, want)
	}
}

func TestFromJSONErrors(t *testing.T) {
	for _, in := range []string{`{"a":`, `{} {}`, ``} {
		if _, err := FromJSON([]byte(in)); err == nil {
			t.Errorf("FromJSON(%q) succeeded", in)
		}
	}
}

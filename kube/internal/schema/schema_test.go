package schema

import (
	"encoding/json"
	"reflect"
	"strings"
	"testing"
	"time"
)

type typeMeta struct {
	APIVersion string `json:"apiVersion,omitempty"`
	Kind       string `json:"kind,omitempty"`
}

type objectMeta struct {
	Name   string            `json:"name,omitempty"`
	Labels map[string]string `json:"labels,omitempty"`
}

type object struct {
	typeMeta
	objectMeta `json:"metadata"`
}

type condition struct {
	Type   string `json:"type"`
	Status string `json:"status" kube:"enum=True|False|Unknown"`
}

func (condition) ListMapKeys() []string { return []string{"type"} }

type intOrString struct{}

func (intOrString) OpenAPISchema() map[string]any {
	return map[string]any{"x-kubernetes-int-or-string": true}
}

type website struct {
	object
	Spec struct {
		Image    string            `json:"image" doc:"Container image to serve."`
		Replicas *int32            `json:"replicas,omitempty" kube:"min=1,max=10,default=2"`
		Domain   string            `json:"domain,omitempty" kube:"immutable,format=hostname" pattern:"^[a-z0-9.-]+$"`
		Tier     string            `json:"tier,omitempty" kube:"enum=free|pro"`
		Port     intOrString       `json:"port,omitzero"`
		Env      map[string]string `json:"env,omitempty" kube:"mapType=atomic"`
		Extra    json.RawMessage   `json:"extra,omitempty"`
		Data     []byte            `json:"data,omitempty"`
		Tags     []string          `json:"tags" kube:"listType=set"`
	} `json:"spec"`
	Status struct {
		Ready      bool        `json:"ready" kube:"column=Ready"`
		URL        string      `json:"url,omitempty" kube:"column=URL"`
		Since      *time.Time  `json:"since,omitempty" kube:"column"`
		Conditions []condition `json:"conditions,omitempty"`
	} `json:"status,omitzero"`
	ignored string
	Skip    string `json:"-"`
}

func TestGenerate(t *testing.T) {
	r, err := Generate(reflect.TypeFor[website]())
	if err != nil {
		t.Fatal(err)
	}
	b, _ := json.MarshalIndent(r.Schema, "", "  ")
	got := string(b)
	for _, want := range []string{
		`"apiVersion": {
      "type": "string"
    }`,
		`"metadata": {
      "type": "object"
    }`,
		`"image": {
          "description": "Container image to serve.",
          "type": "string"
        }`,
		`"replicas": {
          "default": 2,
          "format": "int32",
          "maximum": 10,
          "minimum": 1,
          "type": "integer"
        }`,
		`"x-kubernetes-validations": [
            {
              "message": "field is immutable",
              "rule": "self == oldSelf"
            }
          ]`,
		`"pattern": "^[a-z0-9.-]+$"`,
		`"enum": [
            "free",
            "pro"
          ]`,
		`"port": {
          "x-kubernetes-int-or-string": true
        }`,
		`"extra": {
          "x-kubernetes-preserve-unknown-fields": true
        }`,
		`"data": {
          "format": "byte",
          "type": "string"
        }`,
		`"x-kubernetes-list-type": "set"`,
		`"x-kubernetes-map-type": "atomic"`,
		`"required": [
        "image"
      ]`,
		`"x-kubernetes-list-map-keys": [
            "type"
          ]`,
		`"required": [
        "ready"
      ]`,
		`"required": [
    "spec"
  ]`,
	} {
		if !strings.Contains(got, want) {
			t.Errorf("schema is missing\n%s\n\nfull schema:\n%s", want, got)
		}
	}
	_ = website{}.ignored // Unexported fields must not appear in the schema.
	for _, bad := range []string{`"Skip"`, `"ignored"`, `"name"`} {
		if strings.Contains(got, bad) {
			t.Errorf("schema contains %s", bad)
		}
	}
	if !r.HasStatus {
		t.Error("HasStatus = false")
	}
	wantCols := []Column{
		{"Ready", "boolean", ".status.ready"},
		{"URL", "string", ".status.url"},
		{"Since", "date", ".status.since"},
	}
	if !reflect.DeepEqual(r.Columns, wantCols) {
		t.Errorf("columns = %+v", r.Columns)
	}
}

// properties returns the properties of the schema at path, a dotted list of
// property names.
func properties(t *testing.T, s map[string]any, path string) map[string]any {
	t.Helper()
	for name := range strings.SplitSeq(path, ".") {
		if name != "" {
			s, _ = s["properties"].(map[string]any)[name].(map[string]any)
		}
	}
	props, ok := s["properties"].(map[string]any)
	if !ok {
		t.Fatalf("no properties at %q", path)
	}
	return props
}

func TestIntegers(t *testing.T) {
	type integers struct {
		object
		Spec struct {
			I    int    `json:"i"`
			I8   int8   `json:"i8"`
			I16  int16  `json:"i16"`
			I32  int32  `json:"i32"`
			I64  int64  `json:"i64"`
			U    uint   `json:"u"`
			U8   uint8  `json:"u8"`
			U16  uint16 `json:"u16"`
			U32  uint32 `json:"u32"`
			U64  uint64 `json:"u64"`
			Port uint16 `json:"port" kube:"min=1"`
		} `json:"spec"`
	}
	r, err := Generate(reflect.TypeFor[integers]())
	if err != nil {
		t.Fatal(err)
	}
	props := properties(t, r.Schema, "spec")
	for name, want := range map[string]map[string]any{
		"i":    {"type": "integer", "format": "int64"},
		"i8":   {"type": "integer", "format": "int32", "minimum": int64(-128), "maximum": int64(127)},
		"i16":  {"type": "integer", "format": "int32", "minimum": int64(-32768), "maximum": int64(32767)},
		"i32":  {"type": "integer", "format": "int32", "minimum": int64(-2147483648), "maximum": int64(2147483647)},
		"i64":  {"type": "integer", "format": "int64"},
		"u":    {"type": "integer", "format": "int64", "minimum": int64(0)},
		"u8":   {"type": "integer", "format": "int32", "minimum": int64(0), "maximum": int64(255)},
		"u16":  {"type": "integer", "format": "int32", "minimum": int64(0), "maximum": int64(65535)},
		"u32":  {"type": "integer", "format": "int64", "minimum": int64(0), "maximum": int64(4294967295)},
		"u64":  {"type": "integer", "format": "int64", "minimum": int64(0)},
		"port": {"type": "integer", "format": "int32", "minimum": int64(1), "maximum": int64(65535)},
	} {
		if got := props[name]; !reflect.DeepEqual(got, want) {
			t.Errorf("%s: schema = %v, want %v", name, got, want)
		}
	}
}

func TestStatusNotRequired(t *testing.T) {
	type report struct {
		object
		Spec struct {
			Status string `json:"status"`
		} `json:"spec"`
		Status struct {
			Ready bool `json:"ready"`
		} `json:"status"`
	}
	r, err := Generate(reflect.TypeFor[report]())
	if err != nil {
		t.Fatal(err)
	}
	if got := r.Schema["required"]; !reflect.DeepEqual(got, []string{"spec"}) {
		t.Errorf("required = %v, want [spec]", got)
	}
	if !r.HasStatus {
		t.Error("HasStatus = false")
	}
	props := properties(t, r.Schema, "")
	for name, want := range map[string][]string{"spec": {"status"}, "status": {"ready"}} {
		if got := props[name].(map[string]any)["required"]; !reflect.DeepEqual(got, want) {
			t.Errorf("%s.required = %v, want %v", name, got, want)
		}
	}
}

func TestCRD(t *testing.T) {
	crd, err := CRD(reflect.TypeFor[website](), CRDSpec{
		Group: "example.dev", Version: "v1", Kind: "Website", Plural: "websites", Singular: "website",
		ShortNames: []string{"site"}, Namespaced: true, Labels: map[string]string{"managed": "yes"},
	})
	if err != nil {
		t.Fatal(err)
	}
	b, _ := json.Marshal(crd)
	got := string(b)
	for _, want := range []string{
		`"metadata":{"labels":{"managed":"yes"},"name":"websites.example.dev"}`,
		`"names":{"kind":"Website","listKind":"WebsiteList","plural":"websites","shortNames":["site"],"singular":"website"}`,
		`"scope":"Namespaced"`,
		`"subresources":{"status":{}}`,
		`{"name":"Age","type":"date","jsonPath":".metadata.creationTimestamp"}`,
	} {
		if !strings.Contains(got, want) {
			t.Errorf("CRD is missing %s\n%s", want, got)
		}
	}
}

func TestErrors(t *testing.T) {
	type badTag struct {
		object
		Spec struct {
			N int `json:"n" kube:"bogus"`
		} `json:"spec"`
	}
	if _, err := Generate(reflect.TypeFor[badTag]()); err == nil || !strings.Contains(err.Error(), "bogus") {
		t.Errorf("unknown option: err = %v", err)
	}
	type badMap struct {
		object
		M map[int]string `json:"m"`
	}
	if _, err := Generate(reflect.TypeFor[badMap]()); err == nil {
		t.Error("int map keys: want error")
	}
	type node struct {
		Next *node `json:"next,omitempty"`
	}
	type recursive struct {
		object
		Root node `json:"root"`
	}
	if _, err := Generate(reflect.TypeFor[recursive]()); err == nil || !strings.Contains(err.Error(), "recursive") {
		t.Errorf("recursive type: err = %v", err)
	}
}

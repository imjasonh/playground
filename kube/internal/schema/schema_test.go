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

func TestParseKubeTag(t *testing.T) {
	for _, tc := range []struct {
		tag     string
		want    []tagOption
		wantErr string
	}{
		{tag: "", want: nil},
		{tag: "min=1,max=10", want: []tagOption{{"min", []string{"1"}}, {"max", []string{"10"}}}},
		{tag: " min = 1 ,, immutable, ", want: []tagOption{{"min", []string{"1"}}, {"immutable", nil}}},
		{tag: "default='hello, world'", want: []tagOption{{"default", []string{"hello, world"}}}},
		{tag: "default= 'it''s' ,min=1", want: []tagOption{{"default", []string{"it's"}}, {"min", []string{"1"}}}},
		{tag: "default=it's", want: []tagOption{{"default", []string{"it's"}}}},
		{tag: "default=a|b", want: []tagOption{{"default", []string{"a|b"}}}},
		{tag: "default=", want: []tagOption{{"default", []string{""}}}},
		{tag: "default=''", want: []tagOption{{"default", []string{""}}}},
		{tag: "enum=A | B", want: []tagOption{{"enum", []string{"A", "B"}}}},
		{tag: "enum='a,b'|'c|d'|e,default=e", want: []tagOption{{"enum", []string{"a,b", "c|d", "e"}}, {"default", []string{"e"}}}},
		{tag: "default='abc", wantErr: "option default: the quoted value has no closing quote"},
		{tag: "default='a,min=1", wantErr: "no closing quote"},
		{tag: "default='a'b", wantErr: `option default: "b" follows the closing quote`},
		{tag: "enum='a'b|c", wantErr: `"b|c" follows the closing quote`},
	} {
		got, err := parseKubeTag(tc.tag)
		if tc.wantErr != "" {
			if err == nil || !strings.Contains(err.Error(), tc.wantErr) {
				t.Errorf("parseKubeTag(%q) = %v, %v, want error %q", tc.tag, got, err, tc.wantErr)
			}
			continue
		}
		if err != nil || !reflect.DeepEqual(got, tc.want) {
			t.Errorf("parseKubeTag(%q) = %q, %v, want %q", tc.tag, got, err, tc.want)
		}
	}
}

type port struct {
	Name     string `json:"name"`
	Protocol string `json:"protocol"`
}

func TestTagOptions(t *testing.T) {
	type tagged struct {
		object
		Spec struct {
			Ports      []port      `json:"ports,omitempty" kube:"listType=map,listMapKey=name,listMapKey=protocol"`
			Conditions []condition `json:"conditions,omitempty" kube:"listMapKey=status"`
			Greeting   string      `json:"greeting,omitempty" kube:"default='hello, world'"`
			Mode       string      `json:"mode,omitempty" kube:"enum='a,b'|'c|d'|e,default='a,b'"`
		} `json:"spec"`
	}
	r, err := Generate(reflect.TypeFor[tagged]())
	if err != nil {
		t.Fatal(err)
	}
	props := properties(t, r.Schema, "spec")
	for _, tc := range []struct {
		field, key string
		want       any
	}{
		{"ports", "x-kubernetes-list-map-keys", []string{"name", "protocol"}},
		{"conditions", "x-kubernetes-list-map-keys", []string{"status"}},
		{"greeting", "default", "hello, world"},
		{"mode", "enum", []any{"a,b", "c|d", "e"}},
		{"mode", "default", "a,b"},
	} {
		if got := props[tc.field].(map[string]any)[tc.key]; !reflect.DeepEqual(got, tc.want) {
			t.Errorf("%s %s = %#v, want %#v", tc.field, tc.key, got, tc.want)
		}
	}

	for _, tc := range []struct{ tag, wantErr string }{
		{"enum=A|B,default=A,enum=C", "option enum is repeated"},
		{"min=1,min=2", "option min is repeated"},
		{"immutable,immutable", "option immutable is repeated"},
		{"listType=map,listMapKey=name,listMapKey=name", "listMapKey=name is repeated"},
		{"listMapKey", "listMapKey needs a key"},
		{"enum", "enum needs at least one value"},
		{"default=hello, world", `unknown kube tag option "world"`},
		{"default='hello", `.spec.s: kube:"default='hello": option default: the quoted value has no closing quote`},
	} {
		typ := reflect.StructOf([]reflect.StructField{{
			Name: "Spec",
			Type: reflect.StructOf([]reflect.StructField{
				{Name: "S", Type: reflect.TypeFor[string](), Tag: reflect.StructTag(`json:"s" kube:"` + tc.tag + `"`)},
			}),
			Tag: `json:"spec"`,
		}})
		if _, err := Generate(typ); err == nil || !strings.Contains(err.Error(), tc.wantErr) {
			t.Errorf("kube:%q: err = %v, want %q", tc.tag, err, tc.wantErr)
		}
	}
}

type route struct {
	Name   string `json:"name"`
	Target string `json:"target,omitempty" kube:"immutable"`
}

type bucket struct {
	object
	Spec struct {
		Zone     string `json:"zone,omitempty" kube:"immutable"`
		Region   string `json:"region" kube:"immutable"`
		Settings *struct {
			Class        string `json:"class" kube:"immutable"`
			StorageClass string `json:"storage-class,omitempty" kube:"immutable"`
			Namespace    string `json:"namespace,omitempty" kube:"immutable"`
		} `json:"settings,omitempty"`
		Routes []route           `json:"routes,omitempty" kube:"listType=map,listMapKey=name"`
		Peers  map[string]route  `json:"peers,omitempty"`
		Tags   map[string]string `json:"tags,omitempty" kube:"immutable"`
	} `json:"spec"`
	Status struct {
		Routes []route `json:"routes,omitempty" kube:"listType=map,listMapKey=name"`
	} `json:"status,omitzero"`
}

type draft struct {
	object
	Spec struct {
		Zone string `json:"zone" kube:"immutable"`
	} `json:"spec,omitzero"`
}

func TestImmutable(t *testing.T) {
	r, err := Generate(reflect.TypeFor[bucket]())
	if err != nil {
		t.Fatal(err)
	}
	spec := r.Schema["properties"].(map[string]any)["spec"].(map[string]any)
	props := spec["properties"].(map[string]any)
	fieldRule := []any{map[string]any{"rule": "self == oldSelf", "message": "field is immutable"}}
	presence := func(rule, fieldPath string) map[string]any {
		return map[string]any{"rule": rule, "message": "field is immutable", "fieldPath": fieldPath}
	}
	for _, tc := range []struct {
		name   string
		schema map[string]any
		want   []any
	}{
		{"spec", spec, []any{
			presence("has(self.zone) == has(oldSelf.zone)", ".zone"),
			presence("(has(self.settings) && has(self.settings.class)) == (has(oldSelf.settings) && has(oldSelf.settings.class))", ".settings.class"),
			presence("(has(self.settings) && has(self.settings.storage__dash__class)) == (has(oldSelf.settings) && has(oldSelf.settings.storage__dash__class))", ".settings.storage-class"),
			presence("(has(self.settings) && has(self.settings.__namespace__)) == (has(oldSelf.settings) && has(oldSelf.settings.__namespace__))", ".settings.namespace"),
			presence("has(self.tags) == has(oldSelf.tags)", ".tags"),
		}},
		{"spec.zone", props["zone"].(map[string]any), fieldRule},
		{"spec.region", props["region"].(map[string]any), fieldRule},
		{"spec.settings", props["settings"].(map[string]any), nil},
		{"spec.tags", props["tags"].(map[string]any), fieldRule},
		{"spec.routes[*]", props["routes"].(map[string]any)["items"].(map[string]any), []any{presence("has(self.target) == has(oldSelf.target)", ".target")}},
		{"spec.peers.*", props["peers"].(map[string]any)["additionalProperties"].(map[string]any), []any{presence("has(self.target) == has(oldSelf.target)", ".target")}},
		{"root", r.Schema, nil},
	} {
		if got, _ := tc.schema["x-kubernetes-validations"].([]any); !reflect.DeepEqual(got, tc.want) {
			t.Errorf("%s rules = %v, want %v", tc.name, got, tc.want)
		}
	}

	r, err = Generate(reflect.TypeFor[draft]())
	if err != nil {
		t.Fatal(err)
	}
	want := []any{presence("(has(self.spec) && has(self.spec.zone)) == (has(oldSelf.spec) && has(oldSelf.spec.zone))", ".spec.zone")}
	if got := r.Schema["x-kubernetes-validations"]; !reflect.DeepEqual(got, want) {
		t.Errorf("root rules of a type with an optional spec = %v, want %v", got, want)
	}

	type inStatus struct {
		object
		Status struct {
			ID string `json:"id" kube:"immutable"`
		} `json:"status,omitzero"`
	}
	type immutableStatus struct {
		object
		Status struct {
			ID string `json:"id"`
		} `json:"status" kube:"immutable"`
	}
	type unnamable struct {
		object
		Spec struct {
			First string `json:"1st,omitempty" kube:"immutable"`
		} `json:"spec"`
	}
	for _, tc := range []struct {
		typ     reflect.Type
		wantErr string
	}{
		{reflect.TypeFor[inStatus](), "schema: .status.id: the top-level status and its fields can't be immutable"},
		{reflect.TypeFor[immutableStatus](), "schema: .status: the top-level status and its fields can't be immutable"},
		{reflect.TypeFor[unnamable](), `schema: .spec.1st: immutable needs a CEL rule, and CEL can't name the field "1st"`},
	} {
		if _, err := Generate(tc.typ); err == nil || !strings.Contains(err.Error(), tc.wantErr) {
			t.Errorf("%v: err = %v, want %q", tc.typ, err, tc.wantErr)
		}
	}
}

func TestCELName(t *testing.T) {
	for name, want := range map[string]string{
		"zone":      "zone",
		"_zone":     "_zone",
		"a_b":       "a_b",
		"a__b":      "a__underscores__b",
		"a___b":     "a__underscores___b",
		"a.b":       "a__dot__b",
		"a-b/c":     "a__dash__b__slash__c",
		"namespace": "__namespace__",
		"if":        "__if__",
		"1st":       "",
		"":          "",
		"a b":       "",
		"zoné":      "",
	} {
		got, ok := celName(name)
		if got != want || ok != (want != "") {
			t.Errorf("celName(%q) = %q, %v, want %q", name, got, ok, want)
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

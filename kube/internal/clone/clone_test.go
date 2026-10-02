package clone

import (
	"encoding/json"
	"reflect"
	"testing"
	"time"
)

type meta struct {
	Name        string
	Labels      map[string]string
	Finalizers  []string
	Deleted     *time.Time
	Owners      []owner
	Created     time.Time
	Annotations map[string]*string
}

type owner struct {
	Kind       string
	Controller *bool
}

type tree struct {
	Value    int
	Children []*tree
	Next     *tree
}

type withAny struct {
	Extra any
	Raw   json.RawMessage
	Grid  [2][]int
	hidden []int
}

func TestDeepCopy(t *testing.T) {
	yes := true
	now := time.Now()
	s := "x"
	in := &meta{
		Name:        "a",
		Labels:      map[string]string{"app": "web"},
		Finalizers:  []string{"f"},
		Deleted:     &now,
		Owners:      []owner{{Kind: "Website", Controller: &yes}},
		Created:     now,
		Annotations: map[string]*string{"k": &s},
	}
	out := Of(in)
	if !reflect.DeepEqual(in, out) {
		t.Fatalf("copy differs:\n%+v\n%+v", in, out)
	}
	out.Labels["app"] = "changed"
	out.Finalizers[0] = "changed"
	*out.Owners[0].Controller = false
	*out.Annotations["k"] = "changed"
	*out.Deleted = time.Time{}
	if in.Labels["app"] != "web" || in.Finalizers[0] != "f" || !*in.Owners[0].Controller || *in.Annotations["k"] != "x" || in.Deleted.IsZero() {
		t.Errorf("mutating the copy changed the original: %+v", in)
	}
}

func TestRecursiveTypes(t *testing.T) {
	leaf := &tree{Value: 2}
	in := &tree{Value: 1, Children: []*tree{leaf}, Next: &tree{Value: 3, Next: &tree{Value: 4}}}
	out := Of(in)
	if !reflect.DeepEqual(in, out) {
		t.Fatal("copy differs")
	}
	out.Children[0].Value = 99
	out.Next.Next.Value = 99
	if leaf.Value != 2 || in.Next.Next.Value != 4 {
		t.Error("recursive copy is shallow")
	}
}

func TestInterfacesAndArrays(t *testing.T) {
	in := &withAny{
		Extra:  map[string]any{"list": []any{"a", map[string]any{"b": 1.0}}},
		Raw:    json.RawMessage(`{"a":1}`),
		Grid:   [2][]int{{1}, {2}},
		hidden: []int{7},
	}
	out := Of(in)
	if !reflect.DeepEqual(in, out) {
		t.Fatal("copy differs")
	}
	out.Extra.(map[string]any)["list"].([]any)[1].(map[string]any)["b"] = 2.0
	out.Raw[1] = 'X'
	out.Grid[0][0] = 9
	if in.Extra.(map[string]any)["list"].([]any)[1].(map[string]any)["b"] != 1.0 || in.Raw[1] != '"' || in.Grid[0][0] != 1 {
		t.Errorf("interface or array copy is shallow: %+v", in)
	}
	if &out.hidden[0] != &in.hidden[0] {
		t.Error("unexported fields should be copied shallowly")
	}
	if Of[meta](nil) != nil {
		t.Error("Of(nil) != nil")
	}
}

func BenchmarkClone(b *testing.B) {
	yes := true
	in := &meta{
		Name:       "web-7d4b9c8f6-x2x9z",
		Labels:     map[string]string{"app": "web", "pod-template-hash": "7d4b9c8f6", "tier": "frontend"},
		Finalizers: []string{"example.dev/cleanup"},
		Owners:     []owner{{Kind: "ReplicaSet", Controller: &yes}},
		Created:    time.Now(),
	}
	b.Run("reflect", func(b *testing.B) {
		for b.Loop() {
			_ = Of(in)
		}
	})
	b.Run("json-roundtrip", func(b *testing.B) {
		for b.Loop() {
			data, _ := json.Marshal(in)
			var out meta
			_ = json.Unmarshal(data, &out)
		}
	})
}

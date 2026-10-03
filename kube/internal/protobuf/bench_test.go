package protobuf

import (
	"encoding/base64"
	"encoding/json"
	"maps"
	"reflect"
	"slices"
	"testing"
	"time"
)

// encodeJSON encodes a JSON object as message m, the way the API server
// encodes the object it decoded from that JSON.
func encodeJSON(t testing.TB, m *Message, v map[string]any) enc {
	var out enc
	for _, f := range m.Fields {
		if f.JSON == "" {
			if sub := encodeJSON(t, f.Type.msg, v); len(sub) > 0 {
				out = out.msg(f.Num, sub)
			}
			continue
		}
		if val, ok := v[f.JSON]; ok && val != nil {
			out = encodeValue(t, out, f.Num, f.Type, val)
		}
	}
	return out
}

func encodeValue(t testing.TB, out enc, num int, ty *Type, val any) enc {
	switch ty.kind {
	case kString:
		return out.str(num, val.(string))
	case kBytes:
		b, err := base64.StdEncoding.DecodeString(val.(string))
		if err != nil {
			t.Fatal(err)
		}
		return out.str(num, string(b))
	case kBool:
		if val.(bool) {
			return out.uint(num, 1)
		}
		return out.uint(num, 0)
	case kInt32, kInt64, kUint32, kUint64:
		return out.uint(num, uint64(int64(val.(float64))))
	case kDouble:
		return out.double(num, val.(float64))
	case kRepeated:
		for _, e := range val.([]any) {
			out = encodeValue(t, out, num, ty.elem, e)
		}
		return out
	case kMap:
		mm := val.(map[string]any)
		for _, k := range slices.Sorted(maps.Keys(mm)) {
			out = out.msg(num, encodeValue(t, enc{}.str(1, k), 2, ty.val, mm[k]))
		}
		return out
	}
	switch ty.msg.Name {
	case "meta.v1.Time", "meta.v1.MicroTime":
		tm, err := time.Parse(time.RFC3339Nano, val.(string))
		if err != nil {
			t.Fatal(err)
		}
		return out.msg(num, enc{}.uint(1, uint64(tm.Unix())).uint(2, uint64(tm.Nanosecond())))
	case "resource.Quantity":
		return out.msg(num, enc{}.str(1, val.(string)))
	case "intstr.IntOrString":
		if s, ok := val.(string); ok {
			return out.msg(num, enc{}.uint(1, 1).str(3, s))
		}
		return out.msg(num, enc{}.uint(1, 0).uint(2, uint64(int64(val.(float64)))))
	case "runtime.RawExtension", "meta.v1.FieldsV1":
		b, _ := json.Marshal(val)
		return out.msg(num, enc{}.str(1, string(b)))
	}
	if ty.msg.Wrapper {
		var items enc
		for _, e := range val.([]any) {
			items = encodeValue(t, items, 1, ty.msg.byNum[1].Type.elem, e)
		}
		return out.msg(num, items)
	}
	return out.msg(num, encodeJSON(t, ty.msg, val.(map[string]any)))
}

// benchPod is a Pod as a real cluster returns it, including managedFields.
func benchPod() []byte {
	env := []any{}
	for _, k := range []string{"LOG_LEVEL", "PORT", "DB_HOST", "DB_NAME", "CACHE_URL", "REGION", "FEATURE_FLAGS", "OTEL_ENDPOINT"} {
		env = append(env, map[string]any{"name": k, "value": k + "-value"})
	}
	b, _ := json.Marshal(map[string]any{
		"metadata": map[string]any{
			"name": "service-001-7d4b9c8f6-x0001", "namespace": "shop", "uid": "0b6c6c39-8f0e-4b5e-9d7c-000000000001",
			"resourceVersion": "1001", "creationTimestamp": "2026-10-01T08:00:00Z",
			"labels":          map[string]string{"app.kubernetes.io/name": "service-001", "app.kubernetes.io/part-of": "shop", "pod-template-hash": "7d4b9c8f6", "team": "payments"},
			"annotations":     map[string]string{"prometheus.io/scrape": "true", "prometheus.io/port": "9090"},
			"ownerReferences": []any{map[string]any{"apiVersion": "apps/v1", "kind": "ReplicaSet", "name": "service-7d4b9c8f6", "uid": "4f1c", "controller": true, "blockOwnerDeletion": true}},
			"managedFields": []any{
				map[string]any{"manager": "kube-controller-manager", "operation": "Update", "apiVersion": "v1", "time": "2026-10-01T08:00:00Z", "fieldsType": "FieldsV1",
					"fieldsV1": map[string]any{"f:metadata": map[string]any{"f:labels": map[string]any{".": map[string]any{}, "f:app": map[string]any{}, "f:pod-template-hash": map[string]any{}}}, "f:spec": map[string]any{"f:containers": map[string]any{`k:{"name":"app"}`: map[string]any{".": map[string]any{}, "f:env": map[string]any{}, "f:image": map[string]any{}, "f:name": map[string]any{}, "f:ports": map[string]any{}, "f:resources": map[string]any{}}}}}},
				map[string]any{"manager": "kubelet", "operation": "Update", "apiVersion": "v1", "time": "2026-10-01T08:00:05Z", "fieldsType": "FieldsV1", "subresource": "status",
					"fieldsV1": map[string]any{"f:status": map[string]any{"f:conditions": map[string]any{}, "f:containerStatuses": map[string]any{}, "f:hostIP": map[string]any{}, "f:phase": map[string]any{}, "f:podIP": map[string]any{}, "f:startTime": map[string]any{}}}},
			},
		},
		"spec": map[string]any{
			"nodeName": "node-001", "serviceAccountName": "service",
			"containers": []any{map[string]any{
				"name": "app", "image": "registry.example.com/shop/service:v1.42.0", "env": env,
				"ports":     []any{map[string]any{"name": "http", "containerPort": 8080, "protocol": "TCP"}},
				"resources": map[string]any{"requests": map[string]string{"cpu": "250m", "memory": "256Mi"}},
			}},
		},
		"status": map[string]any{
			"phase": "Running", "podIP": "10.244.3.17", "hostIP": "10.0.1.7", "startTime": "2026-10-01T08:00:00Z",
			"conditions":        []any{map[string]any{"type": "Ready", "status": "True"}, map[string]any{"type": "ContainersReady", "status": "True"}},
			"containerStatuses": []any{map[string]any{"name": "app", "ready": true, "restartCount": 0, "imageID": "registry.example.com/shop/service@sha256:0123456789abcdef0123456789abcdef", "containerID": "containerd://0123456789abcdef"}},
		},
	})
	return b
}

// objectMeta mirrors kube.ObjectMeta, which this package can't import.
type objectMeta struct {
	Name              string            `json:"name,omitempty"`
	Namespace         string            `json:"namespace,omitempty"`
	UID               string            `json:"uid,omitempty"`
	ResourceVersion   string            `json:"resourceVersion,omitempty"`
	Generation        int64             `json:"generation,omitempty"`
	CreationTimestamp time.Time         `json:"creationTimestamp,omitzero"`
	DeletionTimestamp *time.Time        `json:"deletionTimestamp,omitempty"`
	Labels            map[string]string `json:"labels,omitempty"`
	Annotations       map[string]string `json:"annotations,omitempty"`
	OwnerReferences   []struct {
		APIVersion         string `json:"apiVersion"`
		Kind               string `json:"kind"`
		Name               string `json:"name"`
		UID                string `json:"uid"`
		Controller         *bool  `json:"controller,omitempty"`
		BlockOwnerDeletion *bool  `json:"blockOwnerDeletion,omitempty"`
	} `json:"ownerReferences,omitempty"`
	Finalizers []string `json:"finalizers,omitempty"`
}

type podFull struct {
	Metadata objectMeta `json:"metadata"`
	Spec     struct {
		NodeName   string `json:"nodeName,omitempty"`
		Containers []struct {
			Name  string `json:"name"`
			Image string `json:"image,omitempty"`
			Env   []struct {
				Name  string `json:"name"`
				Value string `json:"value,omitempty"`
			} `json:"env,omitempty"`
		} `json:"containers,omitempty"`
	} `json:"spec"`
	Status struct {
		Phase string `json:"phase,omitempty"`
		PodIP string `json:"podIP,omitempty"`
	} `json:"status"`
}

type podSmall struct {
	Metadata objectMeta `json:"metadata"`
	Spec     struct {
		NodeName string `json:"nodeName,omitempty"`
	} `json:"spec"`
}

func encodedPod(t testing.TB) ([]byte, []byte) {
	js := benchPod()
	var v map[string]any
	if err := json.Unmarshal(js, &v); err != nil {
		t.Fatal(err)
	}
	return js, encodeJSON(t, ForKind("v1", "Pod"), v)
}

func TestPodDecodesLikeJSON(t *testing.T) {
	js, pb := encodedPod(t)
	for _, tc := range []struct {
		name string
		new  func() any
	}{
		{"full", func() any { return new(podFull) }},
		{"small", func() any { return new(podSmall) }},
	} {
		fromJSON, fromProto := tc.new(), tc.new()
		if err := json.Unmarshal(js, fromJSON); err != nil {
			t.Fatal(err)
		}
		p, err := For(reflect.TypeOf(fromProto).Elem(), "v1", "Pod")
		if err != nil {
			t.Fatal(err)
		}
		if err := p.Unmarshal(pb, fromProto); err != nil {
			t.Fatal(err)
		}
		if !reflect.DeepEqual(fromJSON, fromProto) {
			t.Errorf("%s: JSON %+v\nprotobuf %+v", tc.name, fromJSON, fromProto)
		}
	}
	t.Logf("the Pod is %d bytes of JSON and %d of protobuf", len(js), len(pb))
}

func BenchmarkDecodePod(b *testing.B) {
	js, pb := encodedPod(b)
	full, _ := For(reflect.TypeFor[podFull](), "v1", "Pod")
	small, _ := For(reflect.TypeFor[podSmall](), "v1", "Pod")
	for _, bc := range []struct {
		name string
		size int
		fn   func()
	}{
		{"json-full", len(js), func() { var p podFull; _ = json.Unmarshal(js, &p) }},
		{"protobuf-full", len(pb), func() { var p podFull; _ = full.Unmarshal(pb, &p) }},
		{"json-small", len(js), func() { var p podSmall; _ = json.Unmarshal(js, &p) }},
		{"protobuf-small", len(pb), func() { var p podSmall; _ = small.Unmarshal(pb, &p) }},
	} {
		b.Run(bc.name, func(b *testing.B) {
			b.SetBytes(int64(bc.size))
			b.ReportAllocs()
			for b.Loop() {
				bc.fn()
			}
		})
	}
}

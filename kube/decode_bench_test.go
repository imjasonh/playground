package kube

import (
	"encoding/json"
	"fmt"
	"testing"

	"github.com/imjasonh/playground/kube/internal/client"
)

// benchPod is a Pod as a real cluster returns it, including managedFields.
func benchPod(i int) []byte {
	env := []any{}
	for _, k := range []string{"LOG_LEVEL", "PORT", "DB_HOST", "DB_NAME", "CACHE_URL", "REGION", "FEATURE_FLAGS", "OTEL_ENDPOINT"} {
		env = append(env, map[string]any{"name": k, "value": k + "-value"})
	}
	pod := map[string]any{
		"kind": "Pod", "apiVersion": "v1",
		"metadata": map[string]any{
			"name": fmt.Sprintf("service-%03d-7d4b9c8f6-x%04d", i/50, i), "namespace": "shop", "uid": fmt.Sprintf("0b6c6c39-8f0e-4b5e-9d7c-%012d", i),
			"resourceVersion": fmt.Sprint(1000 + i), "creationTimestamp": "2026-10-01T08:00:00Z",
			"labels":          map[string]string{"app.kubernetes.io/name": fmt.Sprintf("service-%03d", i/50), "app.kubernetes.io/part-of": "shop", "pod-template-hash": "7d4b9c8f6", "team": "payments"},
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
			"nodeName": fmt.Sprintf("node-%03d", i%100), "serviceAccountName": "service",
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
	}
	b, _ := json.Marshal(pod)
	return b
}

type benchPodFull struct {
	Object `kube:"apiVersion=v1,kind=Pod"`
	Spec   struct {
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

type benchPodSmall struct {
	Object `kube:"apiVersion=v1,kind=Pod"`
	Spec   struct {
		NodeName string `json:"nodeName,omitempty"`
	} `json:"spec"`
}

func BenchmarkDecodeWatchEvent(b *testing.B) {
	obj := benchPod(1)
	event, _ := json.Marshal(map[string]any{"type": "ADDED", "object": json.RawMessage(obj)})
	b.Run("envelope-then-object", func(b *testing.B) {
		b.SetBytes(int64(len(event)))
		for b.Loop() {
			var e client.Event
			_ = json.Unmarshal(event, &e)
			var p benchPodFull
			_ = json.Unmarshal(e.Object, &p)
		}
	})
	b.Run("object-only", func(b *testing.B) {
		b.SetBytes(int64(len(event)))
		for b.Loop() {
			var p benchPodFull
			_ = json.Unmarshal(obj, &p)
		}
	})
	b.Run("object-small-projection", func(b *testing.B) {
		b.SetBytes(int64(len(event)))
		for b.Loop() {
			var p benchPodSmall
			_ = json.Unmarshal(obj, &p)
		}
	})
	b.Run("intern", func(b *testing.B) {
		var p benchPodFull
		_ = json.Unmarshal(obj, &p)
		for b.Loop() {
			intern(&p.ObjectMeta)
		}
	})
}

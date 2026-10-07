package main

import (
	"context"
	"errors"
	"net"
	"strings"
	"testing"
	"time"

	"github.com/imjasonh/playground/kube"
	"github.com/imjasonh/playground/kube/internal/client"
	"github.com/imjasonh/playground/kube/internal/e2e"
	"github.com/imjasonh/playground/kube/k8s"
)

func TestMain(m *testing.M) { e2e.Main(m) }

var testPolicy = policy{
	registries: []string{"registry.example.com/", "ghcr.io/example/"},
	requests:   map[string]k8s.Quantity{"cpu": "100m", "memory": "128Mi"},
}

func newPod(images ...string) *Pod {
	pod := &Pod{Object: kube.Meta("web", nil)}
	for i, img := range images {
		pod.Spec.Containers = append(pod.Spec.Containers, Container{Name: "c" + string(rune('0'+i)), Image: img})
	}
	return pod
}

func TestValidate(t *testing.T) {
	ctx := t.Context()
	if err := testPolicy.Validate(ctx, newPod("registry.example.com/app:1", "ghcr.io/example/proxy:2"), nil); err != nil {
		t.Errorf("allowed images: %v", err)
	}
	pod := newPod("registry.example.com/app:1")
	pod.Spec.InitContainers = []Container{{Name: "init", Image: "docker.io/library/busybox"}}
	if err := testPolicy.Validate(ctx, pod, nil); err == nil || !strings.Contains(err.Error(), `container "init" uses image "docker.io/library/busybox"`) {
		t.Errorf("an init container from another registry: %v", err)
	}
}

func TestDefaultOnlyOnCreate(t *testing.T) {
	pod := newPod("registry.example.com/app:1", "registry.example.com/proxy:1")
	pod.Spec.Containers[1].Resources.Requests = map[string]k8s.Quantity{"cpu": "2"}
	if err := testPolicy.Default(t.Context(), pod, nil); err != nil {
		t.Fatal(err)
	}
	if got := pod.Spec.Containers[0].Resources.Requests; got["cpu"] != "100m" || got["memory"] != "128Mi" {
		t.Errorf("container without requests got %v", got)
	}
	if got := pod.Spec.Containers[1].Resources.Requests; got["cpu"] != "2" || got["memory"] != "128Mi" {
		t.Errorf("container with a CPU request got %v", got)
	}
	update := newPod("registry.example.com/app:1")
	if err := testPolicy.Default(t.Context(), update, update); err != nil || update.Spec.Containers[0].Resources.Requests != nil {
		t.Errorf("an update got requests %v, %v", update.Spec.Containers[0].Resources.Requests, err)
	}
}

func freeAddr(t *testing.T) string {
	t.Helper()
	ln, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	defer ln.Close()
	return ln.Addr().String()
}

func createPod(ctx context.Context, c *client.Client, ns, name, image string, requests map[string]string) error {
	container := map[string]any{
		"name": "app", "image": image,
		"env":   []any{map[string]any{"name": "MODE", "value": "prod"}},
		"ports": []any{map[string]any{"containerPort": 8080}},
	}
	if requests != nil {
		container["resources"] = map[string]any{"requests": requests}
	}
	return c.Create(ctx, client.Path("v1", "pods", ns, ""), map[string]any{
		"apiVersion": "v1", "kind": "Pod", "metadata": map[string]any{"name": name},
		"spec": map[string]any{"containers": []any{container}},
	}, nil)
}

func TestEndToEnd(t *testing.T) {
	c := e2e.Client(t)
	ns := e2e.Namespace(t, c)
	ctx := t.Context()

	t.Log("Pods created before the webhook runs have no requests, and one has an untrusted image.")
	if err := createPod(ctx, c, ns, "before", "registry.example.com/app:1", nil); err != nil {
		t.Fatal(err)
	}
	if err := createPod(ctx, c, ns, "legacy", "docker.io/library/nginx", nil); err != nil {
		t.Fatal(err)
	}

	addr := freeAddr(t)
	t.Cleanup(func() {
		ctx := context.WithoutCancel(ctx)
		for _, r := range []string{"validatingwebhookconfigurations", "mutatingwebhookconfigurations"} {
			// The test's kubeconfig puts the manager in the namespace default.
			_ = c.Delete(ctx, client.Path("admissionregistration.k8s.io/v1", r, "", "podpolicy-e2e.default"), client.DeleteOptions{})
		}
	})
	e2e.Run(t, &kube.Manager{Name: "podpolicy-e2e", Namespace: ns, WebhookAddr: addr, WebhookURL: "https://" + addr}, kube.Webhooks[Pod](&testPolicy))

	t.Log("The webhook rejects an image from another registry.")
	var err error
	e2e.Eventually(t, 30*time.Second, func() error {
		if err = createPod(ctx, c, ns, "untrusted", "docker.io/library/nginx", nil); err == nil {
			_ = c.Delete(ctx, client.Path("v1", "pods", ns, "untrusted"), client.DeleteOptions{})
			return errors.New("the webhook isn't enforced yet")
		}
		return nil
	})
	if !strings.Contains(err.Error(), `uses image "docker.io/library/nginx", which isn't from an allowed registry`) {
		t.Errorf("creating an untrusted Pod: %v", err)
	}

	t.Log("It fills in missing requests and leaves the rest of the Pod alone.")
	var pod k8s.Pod
	e2e.Eventually(t, 30*time.Second, func() error {
		if err := createPod(ctx, c, ns, "trusted", "registry.example.com/app:1", map[string]string{"cpu": "2"}); err != nil {
			return err
		}
		if err := e2e.Get(ctx, c, client.Path("v1", "pods", ns, "trusted"), &pod); err != nil {
			return err
		}
		if pod.Spec.Containers[0].Resources.Requests["memory"] == "" {
			_ = c.Delete(ctx, client.Path("v1", "pods", ns, "trusted"), client.DeleteOptions{})
			return errors.New("the mutating webhook isn't enforced yet")
		}
		return nil
	})
	got := pod.Spec.Containers[0]
	if got.Resources.Requests["cpu"] != "2" || got.Resources.Requests["memory"] != "128Mi" {
		t.Errorf("requests = %v, want the CPU request kept and memory defaulted", got.Resources.Requests)
	}
	if len(got.Env) != 1 || got.Env[0].Value != "prod" || len(got.Ports) != 1 || got.Ports[0].ContainerPort != 8080 {
		t.Errorf("fields the webhook's Pod type doesn't declare changed: env %v, ports %v", got.Env, got.Ports)
	}

	t.Log("Older Pods can still be labeled: Default leaves updates alone, since a Pod's requests are fixed.")
	label := []byte(`{"metadata":{"labels":{"team":"web"}}}`)
	if err := c.Patch(ctx, client.Path("v1", "pods", ns, "before"), client.MergePatch, nil, label, nil); err != nil {
		t.Errorf("labeling a Pod from before the webhook: %v", err)
	}
	if err := e2e.Get(ctx, c, client.Path("v1", "pods", ns, "before"), &pod); err != nil {
		t.Fatal(err)
	}
	if pod.Labels["team"] != "web" || pod.Spec.Containers[0].Resources.Requests != nil {
		t.Errorf("after labeling: labels %v, requests %v", pod.Labels, pod.Spec.Containers[0].Resources.Requests)
	}

	t.Log("Validate runs on updates too, so a Pod with an untrusted image can't be changed.")
	if err := c.Patch(ctx, client.Path("v1", "pods", ns, "legacy"), client.MergePatch, nil, label, nil); err == nil || !strings.Contains(err.Error(), "isn't from an allowed registry") {
		t.Errorf("labeling a Pod with an untrusted image: %v", err)
	}
}

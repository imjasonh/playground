package e2e_test

import (
	"context"
	"fmt"
	"maps"
	"strings"
	"testing"
	"time"

	"github.com/imjasonh/playground/kube"
	"github.com/imjasonh/playground/kube/internal/client"
	"github.com/imjasonh/playground/kube/internal/e2e"
	"github.com/imjasonh/playground/kube/internal/image/imagetest"
	"github.com/imjasonh/playground/kube/k8s"
)

// The k8s package doesn't declare these workload kinds.

type statefulSet struct {
	kube.Object `kube:"apiVersion=apps/v1,kind=StatefulSet,plural=statefulsets,scope=Namespaced"`
	Spec        struct {
		Selector    *k8s.LabelSelector  `json:"selector,omitempty"`
		ServiceName string              `json:"serviceName,omitempty"`
		Template    k8s.PodTemplateSpec `json:"template,omitzero"`
	} `json:"spec,omitzero"`
}

type daemonSet struct {
	kube.Object `kube:"apiVersion=apps/v1,kind=DaemonSet,plural=daemonsets,scope=Namespaced"`
	Spec        workloadSpec `json:"spec,omitzero"`
}

type replicaSet struct {
	kube.Object `kube:"apiVersion=apps/v1,kind=ReplicaSet,plural=replicasets,scope=Namespaced"`
	Spec        workloadSpec `json:"spec,omitzero"`
}

type workloadSpec struct {
	Selector *k8s.LabelSelector  `json:"selector,omitempty"`
	Template k8s.PodTemplateSpec `json:"template,omitzero"`
}

type cronJob struct {
	kube.Object `kube:"apiVersion=batch/v1,kind=CronJob,plural=cronjobs,scope=Namespaced"`
	Spec        struct {
		Schedule    string `json:"schedule"`
		JobTemplate struct {
			Spec k8s.JobSpec `json:"spec,omitzero"`
		} `json:"jobTemplate"`
	} `json:"spec,omitzero"`
}

// pinner owns a workload of each kind, whose containers name an image by
// tag, by digest, and by tag and digest. For the Widget named missing, it
// owns only a Deployment, whose image names a tag that doesn't exist.
type pinner struct{ tagged, pinned, taggedAndPinned, missing string }

func (p pinner) Reconcile(ctx context.Context, w *Widget) error {
	labels := map[string]string{"app": w.Name}
	selector := &k8s.LabelSelector{MatchLabels: labels}
	if w.Name == "missing" {
		kube.Own(ctx, &k8s.Deployment{Object: kube.Meta(w.Name, nil), Spec: k8s.DeploymentSpec{
			Selector: selector,
			Template: k8s.PodTemplateSpec{
				Metadata: k8s.TemplateMeta{Labels: labels},
				Spec:     k8s.PodSpec{Containers: []k8s.Container{{Name: "app", Image: p.missing}}},
			},
		}})
		return nil
	}
	spec := func(restartPolicy string) k8s.PodSpec {
		return k8s.PodSpec{
			InitContainers: []k8s.Container{{Name: "init", Image: p.tagged}},
			Containers: []k8s.Container{
				{Name: "app", Image: p.tagged},
				{Name: "pinned", Image: p.pinned},
				{Name: "tagged-and-pinned", Image: p.taggedAndPinned},
			},
			RestartPolicy: restartPolicy,
		}
	}
	template := func(restartPolicy string) k8s.PodTemplateSpec {
		return k8s.PodTemplateSpec{Metadata: k8s.TemplateMeta{Labels: labels}, Spec: spec(restartPolicy)}
	}
	kube.Own(ctx, &k8s.Pod{Object: kube.Meta(w.Name, nil), Spec: spec("")})
	kube.Own(ctx, &k8s.Deployment{Object: kube.Meta(w.Name, nil), Spec: k8s.DeploymentSpec{Selector: selector, Template: template("")}})
	ss := &statefulSet{Object: kube.Meta(w.Name, nil)}
	ss.Spec.Selector, ss.Spec.ServiceName, ss.Spec.Template = selector, w.Name, template("")
	kube.Own(ctx, ss)
	kube.Own(ctx, &daemonSet{Object: kube.Meta(w.Name, nil), Spec: workloadSpec{Selector: selector, Template: template("")}})
	kube.Own(ctx, &replicaSet{Object: kube.Meta(w.Name, nil), Spec: workloadSpec{Selector: selector, Template: template("")}})
	kube.Own(ctx, &k8s.Job{Object: kube.Meta(w.Name, nil), Spec: k8s.JobSpec{Template: template("Never")}})
	cj := &cronJob{Object: kube.Meta(w.Name, nil)}
	cj.Spec.Schedule, cj.Spec.JobTemplate.Spec.Template = "0 0 1 1 *", template("Never")
	kube.Own(ctx, cj)
	return nil
}

// containerImages returns the image of each init and regular container in
// the Pod spec at path in obj, by container name.
func containerImages(obj map[string]any, path ...string) map[string]string {
	spec := obj
	for _, key := range path {
		spec, _ = spec[key].(map[string]any)
	}
	out := map[string]string{}
	for _, list := range []string{"initContainers", "containers"} {
		containers, _ := spec[list].([]any)
		for _, c := range containers {
			c, _ := c.(map[string]any)
			name, _ := c["name"].(string)
			out[name], _ = c["image"].(string)
		}
	}
	return out
}

// TestImagesByDigest checks that the API server gets the image by digest in
// every workload that a controller owns and every object that Install
// applies, even when the program names the image by tag.
func TestImagesByDigest(t *testing.T) {
	c := e2e.Client(t)
	ns := e2e.Namespace(t, c)
	reg := imagetest.Registry(t)
	digest := imagetest.Base(t, reg+"/app:v1", "linux/amd64")
	// A reference with a digest needs no registry, so these name a
	// registry that doesn't exist.
	const otherDigest = "sha256:0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"
	p := pinner{
		tagged:          reg + "/app:v1",
		pinned:          "registry.invalid/sidecar@" + otherDigest,
		taggedAndPinned: "registry.invalid/sidecar:v2@" + otherDigest,
		missing:         reg + "/app:missing",
	}
	installed := func(image string) []byte {
		return fmt.Appendf(nil, `apiVersion: apps/v1
kind: Deployment
metadata:
  name: installed
  namespace: %s
spec:
  selector:
    matchLabels:
      app: installed
  template:
    metadata:
      labels:
        app: installed
    spec:
      containers:
      - name: app
        image: %s
`, ns, image)
	}

	t.Log("A program whose Install manifest names a tag that doesn't exist fails when it starts.")
	err := failedRelease(t, &kube.Manager{Name: "pinner-e2e", Namespace: ns}, kube.Install(func() []byte { return installed(p.missing) }))
	if want := "installing Deployment installed: container app: resolving image " + p.missing + ": "; !strings.Contains(err.Error(), want) {
		t.Errorf("Run() = %v, want an error that has %q", err, want)
	}
	if err := e2e.Get(t.Context(), c, client.Path("apps/v1", "deployments", ns, "installed"), &map[string]any{}); err == nil {
		t.Error("Install applied the Deployment with a tag that didn't resolve")
	}

	addr := freeAddr(t)
	e2e.Run(t, &kube.Manager{Name: "pinner-e2e", Namespace: ns, Addr: addr},
		kube.For[Widget](p, kube.Named("pinner")),
		kube.Install(func() []byte { return installed(p.tagged) }))
	createWidget(t, c, ns, "w", 1)
	createWidget(t, c, ns, "missing", 1)

	t.Log("Each workload's containers name the image by digest, and references with a digest stay as they are.")
	byDigest := reg + "/app@" + digest
	want := map[string]string{"init": byDigest, "app": byDigest, "pinned": p.pinned, "tagged-and-pinned": p.taggedAndPinned}
	for _, o := range []struct {
		apiVersion, resource string
		path                 []string
	}{
		{"v1", "pods", []string{"spec"}},
		{"apps/v1", "deployments", []string{"spec", "template", "spec"}},
		{"apps/v1", "statefulsets", []string{"spec", "template", "spec"}},
		{"apps/v1", "daemonsets", []string{"spec", "template", "spec"}},
		{"apps/v1", "replicasets", []string{"spec", "template", "spec"}},
		{"batch/v1", "jobs", []string{"spec", "template", "spec"}},
		{"batch/v1", "cronjobs", []string{"spec", "jobTemplate", "spec", "template", "spec"}},
	} {
		e2e.Eventually(t, 30*time.Second, func() error {
			var obj map[string]any
			if err := e2e.Get(t.Context(), c, client.Path(o.apiVersion, o.resource, ns, "w"), &obj); err != nil {
				return err
			}
			if got := containerImages(obj, o.path...); !maps.Equal(got, want) {
				return fmt.Errorf("%s: images = %v, want %v", o.resource, got, want)
			}
			return nil
		})
	}

	t.Log("Install applies its Deployment with the image by digest.")
	e2e.Eventually(t, 30*time.Second, func() error {
		var obj map[string]any
		if err := e2e.Get(t.Context(), c, client.Path("apps/v1", "deployments", ns, "installed"), &obj); err != nil {
			return err
		}
		if got := containerImages(obj, "spec", "template", "spec"); got["app"] != byDigest {
			return fmt.Errorf("installed Deployment's images = %v, want app: %s", got, byDigest)
		}
		return nil
	})

	t.Log("A tag that doesn't exist fails the reconcile, Synced names the image, and nothing is applied with the tag.")
	e2e.Eventually(t, 30*time.Second, func() error {
		w, err := widget(t, c, ns, "missing")
		if err != nil {
			return err
		}
		want := "applying Deployment.apps/v1 " + ns + "/missing: container app: resolving image " + p.missing + ": "
		if s := kube.FindCondition(w.Status.Conditions, "Synced"); s == nil || s.Status != kube.False || !strings.HasPrefix(s.Message, want) {
			return fmt.Errorf("Synced = %+v, want a message that starts %q", s, want)
		}
		return nil
	})
	if err := e2e.Get(t.Context(), c, client.Path("apps/v1", "deployments", ns, "missing"), &map[string]any{}); err == nil {
		t.Error("the controller applied the Deployment with a tag that didn't resolve")
	}

	t.Log("A later reconcile that declares the same objects doesn't apply them again.")
	if err := c.Patch(t.Context(), client.Path(group+"/v1", "widgets", ns, "w"), client.MergePatch, nil, []byte(`{"spec":{"size":2}}`), nil); err != nil {
		t.Fatal(err)
	}
	e2e.Eventually(t, 30*time.Second, func() error {
		w, err := widget(t, c, ns, "w")
		if err != nil {
			return err
		}
		if s := kube.FindCondition(w.Status.Conditions, "Synced"); s == nil || s.Status != kube.True || s.ObservedGeneration != 2 {
			return fmt.Errorf("Synced = %+v, want True for generation 2", s)
		}
		return nil
	})
	if got := scrape(t, addr, `kube_apply_total{controller="pinner",result="applied"}`); got != 7 {
		t.Errorf("applied %v times, want once for each of the 7 objects", got)
	}
	if got := scrape(t, addr, `kube_apply_total{controller="pinner",result="skipped"}`); got < 7 {
		t.Errorf("skipped %v applies, want at least one for each of the 7 objects", got)
	}
}

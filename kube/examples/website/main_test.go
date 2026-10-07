package main

import (
	"fmt"
	"slices"
	"testing"
	"time"

	"github.com/imjasonh/playground/kube"
	"github.com/imjasonh/playground/kube/internal/client"
	"github.com/imjasonh/playground/kube/internal/e2e"
	"github.com/imjasonh/playground/kube/internal/image/imagetest"
	"github.com/imjasonh/playground/kube/k8s"
)

func TestMain(m *testing.M) { e2e.Main(m) }

func newSite(port int32) *Website {
	site := &Website{Spec: WebsiteSpec{Image: "nginx:1.27", Replicas: 3, Port: port}}
	site.Name, site.Namespace, site.Generation = "blog", "default", 1
	return site
}

func TestReconcileCreatesDeploymentAndService(t *testing.T) {
	site := newSite(8080)
	ctx, rec := kube.Fake(t.Context(), site)
	if err := (reconciler{}).Reconcile(ctx, site); err != nil {
		t.Fatal(err)
	}
	deps := kube.Owned[k8s.Deployment](rec)
	if len(deps) != 1 {
		t.Fatalf("owned %d Deployments, want 1", len(deps))
	}
	d := deps[0]
	if d.Name != "blog" || *d.Spec.Replicas != 3 || d.Spec.Template.Spec.Containers[0].Image != "nginx:1.27" {
		t.Errorf("Deployment = %+v", d)
	}
	svcs := kube.Owned[k8s.Service](rec)
	if len(svcs) != 1 || svcs[0].Spec.Ports[0].TargetPort != k8s.Int(8080) {
		t.Fatalf("Services = %+v", svcs)
	}
	if site.Status.URL != "http://blog.default.svc" {
		t.Errorf("URL = %q", site.Status.URL)
	}
	if c := kube.FindCondition(site.Status.Conditions, "Ready"); c == nil || c.Status != kube.False || c.Reason != "Creating" {
		t.Errorf("Ready = %+v", c)
	}
	if got, want := rec.Events(), []kube.Event{{Type: kube.Normal, Reason: "Creating", Note: "0 of 3 replicas are ready"}}; !slices.Equal(got, want) {
		t.Errorf("Events = %+v, want %+v", got, want)
	}
}

func TestReconcileWithoutPortHasNoService(t *testing.T) {
	site := newSite(0)
	ctx, rec := kube.Fake(t.Context(), site)
	if err := (reconciler{}).Reconcile(ctx, site); err != nil {
		t.Fatal(err)
	}
	if svcs := kube.Owned[k8s.Service](rec); len(svcs) != 0 {
		t.Errorf("owned Services %+v, want none", svcs)
	}
	if site.Status.URL != "" {
		t.Errorf("URL = %q, want empty", site.Status.URL)
	}
}

func TestReconcileReportsReadiness(t *testing.T) {
	site := newSite(8080)
	running := &k8s.Deployment{Object: kube.Meta("blog", nil)}
	running.Namespace, running.Generation = "default", 4
	running.Status = k8s.DeploymentStatus{ObservedGeneration: 4, UpdatedReplicas: 3, ReadyReplicas: 2}
	ctx, rec := kube.Fake(t.Context(), site, running)
	if err := (reconciler{}).Reconcile(ctx, site); err != nil {
		t.Fatal(err)
	}
	if c := kube.FindCondition(site.Status.Conditions, "Ready"); c.Status != kube.False || c.Message != "2 of 3 replicas are ready" {
		t.Errorf("Ready = %+v", c)
	}
	if got, want := rec.Events(), []kube.Event{{Type: kube.Normal, Reason: "Starting", Note: "2 of 3 replicas are ready"}}; !slices.Equal(got, want) {
		t.Errorf("Events = %+v, want %+v", got, want)
	}

	running.Status.ReadyReplicas = 3
	ctx, rec = kube.Fake(t.Context(), site, running)
	if err := (reconciler{}).Reconcile(ctx, site); err != nil {
		t.Fatal(err)
	}
	if c := kube.FindCondition(site.Status.Conditions, "Ready"); c.Status != kube.True || site.Status.ReadyReplicas != 3 {
		t.Errorf("Ready = %+v, readyReplicas = %d", c, site.Status.ReadyReplicas)
	}
	if got, want := rec.Events(), []kube.Event{{Type: kube.Normal, Reason: "Serving", Note: "3 of 3 replicas are ready"}}; !slices.Equal(got, want) {
		t.Errorf("Events = %+v, want %+v", got, want)
	}

	ctx, rec = kube.Fake(t.Context(), site, running)
	if err := (reconciler{}).Reconcile(ctx, site); err != nil {
		t.Fatal(err)
	}
	if got := rec.Events(); len(got) != 0 {
		t.Errorf("with the same reason, Events = %+v, want none", got)
	}
}

func TestEndToEnd(t *testing.T) {
	c := e2e.Client(t)
	e2e.Run(t, &kube.Manager{Name: "website-e2e"}, kube.For[Website](reconciler{}))
	ctx := t.Context()
	ns := e2e.Namespace(t, c)
	reg := imagetest.Registry(t)
	nginx127 := imagetest.Base(t, reg+"/nginx:1.27", "linux/amd64")
	nginx128 := imagetest.Base(t, reg+"/nginx:1.28", "linux/arm64")

	sitePath := client.Path("examples.kube.imjasonh.github.io/v1", "websites", ns, "blog")
	depPath := client.Path("apps/v1", "deployments", ns, "blog")
	svcPath := client.Path("v1", "services", ns, "blog")
	var site Website
	e2e.Eventually(t, 30*time.Second, func() error {
		return c.Create(ctx, client.Path("examples.kube.imjasonh.github.io/v1", "websites", ns, ""), map[string]any{
			"apiVersion": "examples.kube.imjasonh.github.io/v1",
			"kind":       "Website",
			"metadata":   map[string]any{"name": "blog"},
			"spec":       map[string]any{"image": reg + "/nginx:1.27", "replicas": 2, "port": 8080},
		}, &site)
	})

	t.Log("The controller creates a Deployment, with the image by digest, and a Service that the Website owns.")
	var dep k8s.Deployment
	e2e.Eventually(t, 10*time.Second, func() error {
		if err := e2e.Get(ctx, c, depPath, &dep); err != nil {
			return err
		}
		if *dep.Spec.Replicas != 2 || dep.Spec.Template.Spec.Containers[0].Image != reg+"/nginx@"+nginx127 {
			return fmt.Errorf("deployment spec = %+v", dep.Spec)
		}
		if len(dep.OwnerReferences) != 1 || dep.OwnerReferences[0].UID != site.UID || !*dep.OwnerReferences[0].Controller {
			return fmt.Errorf("ownerReferences = %+v", dep.OwnerReferences)
		}
		return e2e.Get(ctx, c, svcPath, &k8s.Service{})
	})

	t.Log("Status reports the URL, Synced, and Ready=False until replicas are ready.")
	e2e.Eventually(t, 10*time.Second, func() error {
		if err := e2e.Get(ctx, c, sitePath, &site); err != nil {
			return err
		}
		synced := kube.FindCondition(site.Status.Conditions, "Synced")
		ready := kube.FindCondition(site.Status.Conditions, "Ready")
		if site.Status.URL == "" || synced == nil || synced.Status != kube.True || ready == nil || ready.Status != kube.False || site.Status.ObservedGeneration != 1 {
			return fmt.Errorf("status = %+v", site.Status)
		}
		return nil
	})

	t.Log("When the Deployment reports ready replicas, so does the Website.")
	status := fmt.Sprintf(`{"status":{"observedGeneration":%d,"replicas":2,"updatedReplicas":2,"readyReplicas":2,"availableReplicas":2}}`, dep.Generation)
	if err := c.Patch(ctx, depPath+"/status", client.MergePatch, nil, []byte(status), nil); err != nil {
		t.Fatal(err)
	}
	e2e.Eventually(t, 10*time.Second, func() error {
		if err := e2e.Get(ctx, c, sitePath, &site); err != nil {
			return err
		}
		if ready := kube.FindCondition(site.Status.Conditions, "Ready"); site.Status.ReadyReplicas != 2 || ready.Status != kube.True {
			return fmt.Errorf("status = %+v", site.Status)
		}
		return nil
	})

	t.Log("The controller records an event about the Website when its Ready reason changes.")
	e2e.Eventually(t, 10*time.Second, func() error {
		var events struct {
			Items []struct {
				Type                string `json:"type"`
				Reason              string `json:"reason"`
				Note                string `json:"note"`
				ReportingController string `json:"reportingController"`
				Regarding           struct {
					Kind string `json:"kind"`
					Name string `json:"name"`
					UID  string `json:"uid"`
				} `json:"regarding"`
			} `json:"items"`
		}
		if err := e2e.Get(ctx, c, client.Path("events.k8s.io/v1", "events", ns, ""), &events); err != nil {
			return err
		}
		for _, e := range events.Items {
			if e.Type == kube.Normal && e.Reason == "Serving" && e.Note == "2 of 2 replicas are ready" && e.ReportingController == "website" &&
				e.Regarding.Kind == "Website" && e.Regarding.Name == "blog" && e.Regarding.UID == site.UID {
				return nil
			}
		}
		return fmt.Errorf("events = %+v", events.Items)
	})

	t.Log("Changing the image updates the Deployment; removing the port deletes the Service.")
	if err := c.Patch(ctx, sitePath, client.MergePatch, nil, []byte(`{"spec":{"image":"`+reg+`/nginx:1.28","port":null}}`), nil); err != nil {
		t.Fatal(err)
	}
	e2e.Eventually(t, 10*time.Second, func() error {
		if err := e2e.Get(ctx, c, depPath, &dep); err != nil {
			return err
		}
		if img := dep.Spec.Template.Spec.Containers[0].Image; img != reg+"/nginx@"+nginx128 {
			return fmt.Errorf("image = %s", img)
		}
		if len(dep.Spec.Template.Spec.Containers[0].Ports) != 0 {
			return fmt.Errorf("container ports = %+v", dep.Spec.Template.Spec.Containers[0].Ports)
		}
		return e2e.Gone(ctx, c, svcPath)
	})

	t.Log("A manual change to a field the controller owns is reverted.")
	if err := c.Patch(ctx, depPath, client.MergePatch, nil, []byte(`{"spec":{"replicas":5}}`), nil); err != nil {
		t.Fatal(err)
	}
	e2e.Eventually(t, 10*time.Second, func() error {
		if err := e2e.Get(ctx, c, depPath, &dep); err != nil {
			return err
		}
		if *dep.Spec.Replicas != 2 {
			return fmt.Errorf("replicas = %d", *dep.Spec.Replicas)
		}
		return nil
	})
}

package main

import (
	"fmt"
	"slices"
	"testing"
	"time"

	"github.com/imjasonh/playground/kube"
	"github.com/imjasonh/playground/kube/internal/client"
	"github.com/imjasonh/playground/kube/internal/e2e"
)

func TestMain(m *testing.M) { e2e.Main(m) }

func pod(namespace, name string, images ...string) *Pod {
	p := &Pod{Object: kube.Meta(name, nil)}
	p.Namespace = namespace
	for _, image := range images {
		p.Spec.Containers = append(p.Spec.Containers, Container{Image: image})
	}
	return p
}

func TestCountsPodsPerImage(t *testing.T) {
	ns := &Namespace{Object: kube.Meta("shop", nil)}
	api := pod("shop", "api", "ghcr.io/example/api:1", "ghcr.io/example/proxy:2")
	api.Spec.InitContainers = []Container{{Image: "ghcr.io/example/proxy:2"}}
	ctx, rec := kube.Fake(t.Context(), ns, api,
		pod("shop", "web", "ghcr.io/example/web:1", "ghcr.io/example/proxy:2"),
		pod("db", "postgres", "postgres:17"))
	if err := (reporter{}).Reconcile(ctx, ns); err != nil {
		t.Fatal(err)
	}
	want := []ImageCount{{"ghcr.io/example/api:1", 1}, {"ghcr.io/example/proxy:2", 2}, {"ghcr.io/example/web:1", 1}}
	reports := kube.Owned[ImageReport](rec)
	if len(reports) != 1 || reports[0].Namespace != "shop" || reports[0].Name != "images" || reports[0].Pods != 2 || !slices.Equal(reports[0].Images, want) {
		t.Errorf("reports = %+v, want shop/images with 2 Pods and images %v", reports, want)
	}
}

func TestNoReportWithoutPods(t *testing.T) {
	empty := &Namespace{Object: kube.Meta("empty", nil)}
	deleting := &Namespace{Object: kube.Meta("deleting", nil)}
	now := time.Now()
	deleting.DeletionTimestamp = &now
	for _, ns := range []*Namespace{empty, deleting} {
		ctx, rec := kube.Fake(t.Context(), ns, pod("db", "postgres", "postgres:17"), pod("deleting", "web", "nginx:1.27"))
		if err := (reporter{}).Reconcile(ctx, ns); err != nil {
			t.Fatal(err)
		}
		if reports := kube.Owned[ImageReport](rec); len(reports) != 0 {
			t.Errorf("%s: reports = %+v, want none", ns.Name, reports)
		}
	}
}

func TestEndToEnd(t *testing.T) {
	c := e2e.Client(t)
	ctx := t.Context()
	crdPath := "/apis/apiextensions.k8s.io/v1/customresourcedefinitions/imagereports.examples.kube.imjasonh.github.io"
	if err := e2e.Gone(ctx, c, crdPath); err != nil {
		t.Fatal(err)
	}
	e2e.Run(t, &kube.Manager{Name: "imagereport-e2e"}, kube.For[Namespace](reporter{}, kube.Named("imagereport"), kube.Owns[ImageReport]()))

	t.Log("The program creates the ImageReport CRD when it starts.")
	e2e.Eventually(t, 30*time.Second, func() error {
		var crd struct {
			Metadata struct {
				Labels map[string]string `json:"labels"`
			} `json:"metadata"`
		}
		if err := e2e.Get(ctx, c, crdPath, &crd); err != nil {
			return err
		}
		if got := crd.Metadata.Labels["kube.imjasonh.github.io/managed-by"]; got != "imagereport-e2e" {
			return fmt.Errorf("the CRD is managed by %q", got)
		}
		return nil
	})

	ns := e2e.Namespace(t, c)
	podPath := func(name string) string { return client.Path("v1", "pods", ns, name) }
	reportPath := client.Path("examples.kube.imjasonh.github.io/v1", "imagereports", ns, "images")
	hasReport := func(pods int32, want ...ImageCount) error {
		var r ImageReport
		if err := e2e.Get(ctx, c, reportPath, &r); err != nil {
			return err
		}
		if r.Pods != pods || !slices.Equal(r.Images, want) {
			return fmt.Errorf("report = %d Pods, %+v", r.Pods, r.Images)
		}
		return nil
	}

	t.Log("A namespace with Pods gets a report of their images.")
	for name, images := range map[string][]string{"web": {"nginx:1.27", "ghcr.io/example/proxy:2"}, "api": {"ghcr.io/example/api:1", "ghcr.io/example/proxy:2"}} {
		var containers []any
		for i, image := range images {
			containers = append(containers, map[string]any{"name": fmt.Sprintf("c%d", i), "image": image})
		}
		if err := c.Create(ctx, client.Path("v1", "pods", ns, ""), map[string]any{
			"apiVersion": "v1", "kind": "Pod", "metadata": map[string]any{"name": name},
			"spec": map[string]any{"containers": containers},
		}, nil); err != nil {
			t.Fatal(err)
		}
	}
	e2e.Eventually(t, 10*time.Second, func() error {
		return hasReport(2, ImageCount{"ghcr.io/example/api:1", 1}, ImageCount{"ghcr.io/example/proxy:2", 2}, ImageCount{"nginx:1.27", 1})
	})

	t.Log("The report follows the Pods, and goes away with the last one.")
	if err := c.Delete(ctx, podPath("api"), client.DeleteOptions{}); err != nil {
		t.Fatal(err)
	}
	e2e.Eventually(t, 10*time.Second, func() error {
		return hasReport(1, ImageCount{"ghcr.io/example/proxy:2", 1}, ImageCount{"nginx:1.27", 1})
	})
	if err := c.Delete(ctx, podPath("web"), client.DeleteOptions{}); err != nil {
		t.Fatal(err)
	}
	e2e.Eventually(t, 10*time.Second, func() error { return e2e.Gone(ctx, c, reportPath) })
}

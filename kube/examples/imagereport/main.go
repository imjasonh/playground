// Command imagereport keeps an ImageReport in each namespace that lists the
// images that the namespace's Pods run, like the reports that
// aquasecurity/trivy-operator writes for people and other tools to read:
//
//	$ kubectl get imagereports -A
//	NAMESPACE     NAME     PODS   AGE
//	kube-system   images   8      2m
//
// It shows a type that a program defines and owns but doesn't reconcile.
// Nothing reconciles ImageReports, so the program creates their
// CustomResourceDefinition if the cluster doesn't have it, and never changes
// it after that. kube.Owns starts the ImageReport cache when the program
// starts. So the program creates the CRD then, and after a restart it still
// deletes the report of a namespace that has lost its Pods.
package main

import (
	"context"
	"maps"
	"slices"

	"github.com/imjasonh/playground/kube"
)

// Namespace declares no fields besides metadata, so the controller watches
// namespaces' metadata only.
type Namespace struct {
	kube.Object `kube:"apiVersion=v1,kind=Namespace,scope=Cluster"`
}

// Pod declares only its containers' images, so the cache holds little of
// each Pod.
type Pod struct {
	kube.Object `kube:"apiVersion=v1,kind=Pod,scope=Namespaced"`
	Spec        struct {
		InitContainers []Container `json:"initContainers,omitempty"`
		Containers     []Container `json:"containers"`
	} `json:"spec"`
}

// Container is the image of one of a Pod's containers.
type Container struct {
	Image string `json:"image"`
}

// ImageReport lists the images that a namespace's Pods run.
type ImageReport struct {
	kube.Object `kube:"group=examples.kube.imjasonh.github.io"`
	Pods        int32        `json:"pods" kube:"column=Pods" doc:"Pods in the namespace."`
	Images      []ImageCount `json:"images,omitempty" kube:"listType=map,listMapKey=image"`
}

// ImageCount is the number of Pods that run an image.
type ImageCount struct {
	Image string `json:"image"`
	Pods  int32  `json:"pods"`
}

type reporter struct{}

func (reporter) Reconcile(ctx context.Context, ns *Namespace) error {
	// The API server refuses new objects in a namespace that's being deleted.
	if ns.Deleting() {
		return nil
	}
	pods := kube.List[Pod](ctx, kube.InNamespace(ns.Name))
	if len(pods) == 0 {
		return nil
	}
	counts := map[string]int32{}
	for _, p := range pods {
		images := map[string]bool{}
		for _, c := range slices.Concat(p.Spec.InitContainers, p.Spec.Containers) {
			images[c.Image] = true
		}
		for image := range images {
			counts[image]++
		}
	}
	report := &ImageReport{Object: kube.Meta("images", nil), Pods: int32(len(pods))}
	report.Namespace = ns.Name
	for _, image := range slices.Sorted(maps.Keys(counts)) {
		report.Images = append(report.Images, ImageCount{Image: image, Pods: counts[image]})
	}
	kube.Own(ctx, report)
	return nil
}

func main() {
	kube.Main(kube.For[Namespace](reporter{}, kube.Named("imagereport"), kube.Owns[ImageReport]()))
}

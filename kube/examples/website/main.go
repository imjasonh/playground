// Command website runs a controller for Website objects. A Website is a
// container image to serve: the controller runs it with a Deployment,
// exposes it with a Service when it has a port, and reports how many
// replicas are ready.
//
// This is the most common shape of operator: one custom type that owns a
// few built-in objects. It shows Own, pruning (remove the port and the
// Service goes away), status computed from an owned object, an event each
// time the Ready condition's reason changes, and printer columns:
//
//	$ kubectl get websites
//	NAME   READY   URL                         AGE
//	blog   3       http://blog.default.svc     2m
package main

import (
	"context"
	"fmt"

	"github.com/imjasonh/playground/kube"
	"github.com/imjasonh/playground/kube/k8s"
)

// Website is the desired state, written by people; its status is the real
// state, written by the controller.
type Website struct {
	kube.Object `kube:"group=examples.kube.imjasonh.github.io,shortName=site"`
	Spec        WebsiteSpec   `json:"spec"`
	Status      WebsiteStatus `json:"status,omitzero"`
}

// WebsiteSpec is what to serve.
type WebsiteSpec struct {
	Image    string `json:"image" doc:"Container image that serves the site."`
	Replicas int32  `json:"replicas,omitempty" kube:"min=0,max=20,default=1"`
	Port     int32  `json:"port,omitempty" kube:"min=1,max=65535" doc:"Port the container listens on. When set, a Service exposes it on port 80."`
}

// WebsiteStatus is what's running.
type WebsiteStatus struct {
	ReadyReplicas      int32            `json:"readyReplicas" kube:"column=Ready"`
	URL                string           `json:"url,omitempty" kube:"column=URL"`
	ObservedGeneration int64            `json:"observedGeneration,omitempty"`
	Conditions         []kube.Condition `json:"conditions,omitempty"`
}

type reconciler struct{}

func (reconciler) Reconcile(ctx context.Context, site *Website) error {
	labels := map[string]string{"app.kubernetes.io/name": site.Name}
	container := k8s.Container{Name: "web", Image: site.Spec.Image}
	if site.Spec.Port != 0 {
		container.Ports = []k8s.ContainerPort{{Name: "http", ContainerPort: site.Spec.Port}}
	}
	dep := kube.Own(ctx, &k8s.Deployment{
		Object: kube.Meta(site.Name, labels),
		Spec: k8s.DeploymentSpec{
			Replicas: new(site.Spec.Replicas),
			Selector: &k8s.LabelSelector{MatchLabels: labels},
			Template: k8s.PodTemplateSpec{
				Metadata: k8s.TemplateMeta{Labels: labels},
				Spec:     k8s.PodSpec{Containers: []k8s.Container{container}},
			},
		},
	})

	site.Status.URL = ""
	if site.Spec.Port != 0 {
		kube.Own(ctx, &k8s.Service{
			Object: kube.Meta(site.Name, labels),
			Spec: k8s.ServiceSpec{
				Selector: labels,
				Ports:    []k8s.ServicePort{{Name: "http", Port: 80, TargetPort: k8s.Int(site.Spec.Port)}},
			},
		})
		site.Status.URL = fmt.Sprintf("http://%s.%s.svc", site.Name, site.Namespace)
	}

	ready := kube.Condition{Type: "Ready", Status: kube.False, Reason: "Creating"}
	site.Status.ReadyReplicas = 0
	if dep != nil {
		site.Status.ReadyReplicas = dep.Status.ReadyReplicas
		switch {
		case dep.Status.ObservedGeneration < dep.Generation || dep.Status.UpdatedReplicas < site.Spec.Replicas:
			ready.Reason = "Updating"
		case dep.Status.ReadyReplicas < site.Spec.Replicas:
			ready.Reason = "Starting"
			ready.Message = fmt.Sprintf("%d of %d replicas are ready", dep.Status.ReadyReplicas, site.Spec.Replicas)
		default:
			ready.Status, ready.Reason = kube.True, "Serving"
		}
	}
	if old := kube.FindCondition(site.Status.Conditions, "Ready"); old == nil || old.Reason != ready.Reason {
		kube.Eventf(ctx, kube.Normal, ready.Reason, "%d of %d replicas are ready", site.Status.ReadyReplicas, site.Spec.Replicas)
	}
	kube.SetCondition(&site.Status.Conditions, ready)
	return nil
}

func main() {
	kube.Main(kube.For[Website](reconciler{}))
}

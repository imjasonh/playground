// Command applystatus is a program for generate's tests. It applies a type
// that has a status and a type that doesn't, and reads a type that has a
// status.
package main

import (
	"context"

	"github.com/imjasonh/playground/kube"
	"github.com/imjasonh/playground/kube/k8s"
)

type deploymentStatus struct {
	kube.Object `kube:"apiVersion=apps/v1,kind=Deployment,plural=deployments,scope=Namespaced"`
	Status      struct {
		Conditions []kube.Condition `json:"conditions,omitempty"`
	} `json:"status"`
}

type configMap struct {
	kube.Object `kube:"apiVersion=v1,kind=ConfigMap,plural=configmaps,scope=Namespaced"`
	Data        map[string]string `json:"data,omitempty"`
}

type reconciler struct{}

func (reconciler) Reconcile(ctx context.Context, cm *configMap) error {
	kube.Get[k8s.Pod](ctx, cm.Namespace, cm.Name)
	kube.Apply(ctx, &deploymentStatus{Object: kube.Meta(cm.Name, nil)})
	kube.Apply(ctx, &configMap{Object: kube.Meta(cm.Name+"-copy", nil)})
	return nil
}

func main() {
	kube.Main(kube.For[configMap](reconciler{}, kube.Named("applystatus")))
}

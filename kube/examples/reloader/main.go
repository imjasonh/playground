// Command reloader restarts a Deployment's pods when a ConfigMap or Secret
// that they use changes, like stakater/Reloader. Opt a Deployment in with an
// annotation:
//
//	kubectl annotate deployment web reloader.examples.kube.imjasonh.github.io/enabled=true
//
// The controller keeps a hash of the referenced ConfigMaps and Secrets in an
// annotation on the pod template, so a change to any of them rolls the
// pods. Opting in rolls the pods once, when the annotation first appears.
//
// It shows dependency tracking. With controller-runtime, this controller
// needs a watch on ConfigMaps, a map function, and a field index from each
// ConfigMap to the Deployments that use it. Here, Reconcile reads the
// ConfigMaps it references, and a change to any of them runs the reconcile
// again. It also shows Apply on an object the controller doesn't own: the
// controller manages one annotation on someone else's Deployment and leaves
// every other field alone.
package main

import (
	"context"
	"crypto/sha256"
	"encoding/hex"
	"fmt"
	"maps"
	"slices"

	"github.com/imjasonh/playground/kube"
	"github.com/imjasonh/playground/kube/k8s"
)

const (
	enabled  = "reloader.examples.kube.imjasonh.github.io/enabled"
	hashName = "reloader.examples.kube.imjasonh.github.io/config-hash"
)

// Deployment holds only the fields the controller reads and writes, so the
// cache doesn't store the rest of every Deployment in the cluster.
type Deployment struct {
	kube.Object `kube:"apiVersion=apps/v1,kind=Deployment"`
	Spec        struct {
		Template k8s.PodTemplateSpec `json:"template"`
	} `json:"spec"`
}

// SecretMeta is a Secret without its data. Hashing a Secret's resource
// version instead of its data means the controller never holds Secret data
// in memory, at the cost of restarting pods when only the Secret's labels
// or annotations change.
type SecretMeta struct {
	kube.Object `kube:"apiVersion=v1,kind=Secret"`
}

type reloader struct{}

func (reloader) Reconcile(ctx context.Context, d *Deployment) error {
	if d.Annotations[enabled] != "true" {
		return nil
	}
	configMaps, secrets := references(d.Spec.Template.Spec)
	h := sha256.New()
	for _, name := range configMaps {
		if cm := kube.Get[k8s.ConfigMap](ctx, d.Namespace, name); cm != nil {
			fmt.Fprintf(h, "configmap %s\n", name)
			for _, k := range slices.Sorted(maps.Keys(cm.Data)) {
				fmt.Fprintf(h, "%s=%s\n", k, cm.Data[k])
			}
			for _, k := range slices.Sorted(maps.Keys(cm.BinaryData)) {
				fmt.Fprintf(h, "%s=%x\n", k, cm.BinaryData[k])
			}
		}
	}
	for _, name := range secrets {
		if s := kube.Get[SecretMeta](ctx, d.Namespace, name); s != nil {
			fmt.Fprintf(h, "secret %s %s %s\n", name, s.UID, s.ResourceVersion)
		}
	}
	patch := &Deployment{Object: kube.Meta(d.Name, nil)}
	patch.Namespace = d.Namespace
	patch.Spec.Template.Metadata.Annotations = map[string]string{hashName: hex.EncodeToString(h.Sum(nil))[:16]}
	kube.Apply(ctx, patch)
	return nil
}

// references returns the names of the ConfigMaps and Secrets that a pod
// uses in volumes, envFrom, and env.
func references(spec k8s.PodSpec) (configMaps, secrets []string) {
	add := func(list *[]string, name string) {
		if !slices.Contains(*list, name) {
			*list = append(*list, name)
		}
	}
	for _, v := range spec.Volumes {
		if v.ConfigMap != nil {
			add(&configMaps, v.ConfigMap.Name)
		}
		if v.Secret != nil {
			add(&secrets, v.Secret.SecretName)
		}
	}
	for _, c := range slices.Concat(spec.InitContainers, spec.Containers) {
		for _, e := range c.EnvFrom {
			if e.ConfigMapRef != nil {
				add(&configMaps, e.ConfigMapRef.Name)
			}
			if e.SecretRef != nil {
				add(&secrets, e.SecretRef.Name)
			}
		}
		for _, e := range c.Env {
			if e.ValueFrom != nil && e.ValueFrom.ConfigMapKeyRef != nil {
				add(&configMaps, e.ValueFrom.ConfigMapKeyRef.Name)
			}
			if e.ValueFrom != nil && e.ValueFrom.SecretKeyRef != nil {
				add(&secrets, e.ValueFrom.SecretKeyRef.Name)
			}
		}
	}
	slices.Sort(configMaps)
	slices.Sort(secrets)
	return configMaps, secrets
}

func main() {
	kube.Main(kube.For[Deployment](reloader{}, kube.Named("reloader")))
}

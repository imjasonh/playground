// Command replicator copies Secrets into other namespaces, like
// emberstack/reflector and mittwald/kubernetes-replicator. Annotate a
// Secret with a namespace label selector and the controller keeps a copy in
// every matching namespace:
//
//	kubectl annotate secret registry-creds \
//	  replicator.examples.kube.imjasonh.github.io/namespaces='team in (web,api)'
//
// An empty selector matches every namespace. Copies follow changes to the
// Secret's data, appear in namespaces created later, disappear from
// namespaces that stop matching, and are deleted with the Secret or when
// the annotation is removed.
//
// It shows how a type's fields set the cost of watching it. The controller
// reconciles every Secret in the cluster but declares a Secret type with no
// fields, so the API server sends metadata only and the cache never holds
// Secret data. It reads the data of the few Secrets it replicates with
// Fetch. Copies live in other namespaces, where owner references can't
// reach, so the framework adds a finalizer to the source Secret and removes
// it once no copies remain.
package main

import (
	"context"

	"github.com/imjasonh/playground/kube"
	"github.com/imjasonh/playground/kube/k8s"
)

const annotation = "replicator.examples.kube.imjasonh.github.io/namespaces"

// SecretMeta is a Secret without its data.
type SecretMeta struct {
	kube.Object `kube:"apiVersion=v1,kind=Secret"`
}

type replicator struct{}

func (replicator) Reconcile(ctx context.Context, s *SecretMeta) error {
	selector, ok := s.Annotations[annotation]
	if !ok {
		return nil
	}
	src, err := kube.Fetch[k8s.Secret](ctx, s.Namespace, s.Name)
	if err != nil || src == nil {
		return err
	}
	for _, ns := range kube.List[k8s.Namespace](ctx, kube.MatchingSelector(selector)) {
		if ns.Name == s.Namespace || ns.Deleting() {
			continue
		}
		copied := &k8s.Secret{Object: kube.Meta(s.Name, nil), Type: src.Type, Data: src.Data}
		copied.Namespace = ns.Name
		kube.Own(ctx, copied)
	}
	return nil
}

func main() {
	kube.Main(kube.For[SecretMeta](replicator{}, kube.Named("replicator")))
}

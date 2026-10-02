// Command janitor deletes namespaces when their time to live runs out, like
// hjacobs/kube-janitor. It suits short-lived environments such as pull
// request previews:
//
//	kubectl annotate namespace preview-1234 janitor.examples.kube.imjasonh.github.io/ttl=72h
//
// It shows a desired state that depends on time. Nothing in the cluster
// changes when a namespace expires, so Reconcile asks to run again when the
// time to live ends, then deletes the namespace. A malformed annotation is a
// permanent error: retrying won't fix it, and editing the annotation runs
// the reconcile again.
package main

import (
	"context"
	"fmt"
	"time"

	"github.com/imjasonh/playground/kube"
)

const ttlAnnotation = "janitor.examples.kube.imjasonh.github.io/ttl"

// Namespace declares no fields besides metadata, so the controller watches
// namespaces' metadata only.
type Namespace struct {
	kube.Object `kube:"apiVersion=v1,kind=Namespace,scope=Cluster"`
}

type janitor struct {
	now func() time.Time
}

func (j janitor) Reconcile(ctx context.Context, ns *Namespace) error {
	value, ok := ns.Annotations[ttlAnnotation]
	if !ok {
		return nil
	}
	ttl, err := time.ParseDuration(value)
	if err != nil || ttl <= 0 {
		return kube.Permanent(fmt.Errorf("%s=%q must be a positive duration such as 72h", ttlAnnotation, value))
	}
	if left := ns.CreationTimestamp.Add(ttl).Sub(j.now()); left > 0 {
		kube.RequeueAfter(ctx, left)
		return nil
	}
	kube.Delete(ctx, ns)
	return nil
}

func main() {
	kube.Main(kube.For[Namespace](janitor{now: time.Now}, kube.Named("janitor")))
}

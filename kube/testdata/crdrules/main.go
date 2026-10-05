// Command crdrules reads one custom type and owns another without
// reconciling either, for the test of the CustomResourceDefinition rules that
// generate writes.
package main

import (
	"context"

	"github.com/imjasonh/playground/kube"
)

// Note is a type that the program only reads.
type Note struct {
	kube.Object `kube:"group=test.kube.imjasonh.github.io"`
}

// Receipt is a type that the program owns.
type Receipt struct {
	kube.Object `kube:"group=test.kube.imjasonh.github.io"`
	Spec        struct {
		Notes int `json:"notes"`
	} `json:"spec"`
}

// ConfigMap is the type that the program reconciles.
type ConfigMap struct {
	kube.Object `kube:"apiVersion=v1,kind=ConfigMap"`
}

type receipts struct{}

func (receipts) Reconcile(ctx context.Context, cm *ConfigMap) error {
	n := len(kube.List[Note](ctx, kube.InNamespace(cm.Namespace)))
	if kube.Get[Note](ctx, cm.Namespace, cm.Name) == nil {
		note, err := kube.Fetch[Note](ctx, cm.Namespace, cm.Name)
		if err != nil {
			return err
		}
		if note != nil {
			n++
		}
	}
	r := &Receipt{Object: kube.Meta(cm.Name, nil)}
	r.Spec.Notes = n
	kube.Own(ctx, r)
	return nil
}

func main() {
	kube.Main(kube.For[ConfigMap](receipts{}))
}

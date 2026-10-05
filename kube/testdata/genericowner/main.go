// Command genericowner calls kube.Own from a method of a generic type, so
// generate can't tell which types it owns.
package main

import (
	"context"

	"github.com/imjasonh/playground/kube"
	"github.com/imjasonh/playground/kube/k8s"
)

type owner[T any, P kube.Resource[T]] struct{}

func (owner[T, P]) own(ctx context.Context, p P) { kube.Own[T, P](ctx, p) }

func main() {
	owner[k8s.ConfigMap, *k8s.ConfigMap]{}.own(context.Background(), &k8s.ConfigMap{})
}

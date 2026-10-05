// Command fetchnames fetches objects with constant and variable namespaces
// and names, for generate's tests. It's never run.
package main

import (
	"context"
	"os"

	"github.com/imjasonh/playground/kube"
	"github.com/imjasonh/playground/kube/k8s"
)

const settings = "settings"

// Gadget's kube tag doesn't give its scope.
type Gadget struct {
	kube.Object `kube:"apiVersion=example.dev/v1,kind=Gadget"`
}

func fetch[T any, P kube.Resource[T]](ctx context.Context) {
	_, _ = kube.Fetch[T, P](ctx, "config", "through-a-helper")
}

func main() {
	ctx := context.Background()
	_, _ = kube.Fetch[k8s.ConfigMap](ctx, "config", settings)
	_, _ = kube.Fetch[k8s.ConfigMap](ctx, "config", settings)
	_, _ = (kube.Fetch[k8s.ConfigMap, *k8s.ConfigMap])(ctx, "prog", "own")
	_, _ = kube.Fetch[k8s.Namespace](ctx, "ignored", "team")
	_, _ = kube.Fetch[k8s.Secret](ctx, "config", os.Getenv("NAME"))
	_, _ = kube.Fetch[k8s.ServiceAccount](ctx, "", "no-namespace")
	_, _ = kube.Fetch[Gadget](ctx, "config", "gadget")
	fetch[k8s.Service](ctx)
}

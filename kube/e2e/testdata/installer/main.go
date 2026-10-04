// The installer program installs, with kube.Install, an admission policy
// that reads a ConfigMap, and a Cactus. It reconciles Cactus objects only so
// that it installs their CustomResourceDefinition, which the Cactus in its
// manifest needs. The end-to-end tests install it with generate.
package main

import (
	"context"
	_ "embed"
	"flag"

	"github.com/imjasonh/playground/kube"
)

//go:embed manifest.yaml
var manifest []byte

// Cactus has a plural that generate can't guess from its kind.
type Cactus struct {
	kube.Object `kube:"group=e2e.kube.imjasonh.github.io,plural=cacti"`
	Spec        CactusSpec `json:"spec"`
}

// CactusSpec is how tall a cactus is.
type CactusSpec struct {
	Height int32 `json:"height,omitempty"`
}

type reconciler struct{}

func (reconciler) Reconcile(context.Context, *Cactus) error { return nil }

func main() {
	install := flag.Bool("install", true, "install the objects in manifest.yaml")
	kube.Main(
		kube.Install(func() []byte {
			if !*install {
				return nil
			}
			return manifest
		}),
		kube.For[Cactus](reconciler{}),
	)
}

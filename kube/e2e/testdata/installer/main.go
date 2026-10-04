// The installer program installs an admission policy that reads a ConfigMap,
// with kube.Install. The end-to-end tests install it with generate.
package main

import (
	_ "embed"
	"flag"

	"github.com/imjasonh/playground/kube"
)

//go:embed policy.yaml
var policy []byte

func main() {
	install := flag.Bool("install", true, "install the policy")
	kube.Main(kube.Install(func() []byte {
		if !*install {
			return nil
		}
		return policy
	}))
}

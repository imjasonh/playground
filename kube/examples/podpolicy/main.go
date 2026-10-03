// Command podpolicy is an admission webhook for Pods, modeled on the first
// policies that Kyverno and OPA Gatekeeper users usually write: allow images
// only from trusted registries, and give containers default resource
// requests. It reconciles nothing; another program runs Pods.
//
// Its Pod type declares only container names, images, and resource requests.
// The webhook decodes Pods into it, and the framework sends the API server a
// patch of only the requests that Default adds, so the rest of each Pod is
// untouched. Pods can't change their containers' requests after they're
// created, so Default fills them in only on creation.
//
//	podpolicy -webhook-service=podpolicy -registries=registry.example.com/,ghcr.io/example/
package main

import (
	"context"
	"flag"
	"fmt"
	"slices"
	"strings"

	"github.com/imjasonh/playground/kube"
	"github.com/imjasonh/playground/kube/k8s"
)

type Pod struct {
	kube.Object `kube:"apiVersion=v1,kind=Pod"`
	Spec        struct {
		InitContainers []Container `json:"initContainers,omitempty"`
		Containers     []Container `json:"containers"`
	} `json:"spec"`
}

type Container struct {
	Name      string `json:"name"`
	Image     string `json:"image"`
	Resources struct {
		Requests map[string]k8s.Quantity `json:"requests,omitempty"`
	} `json:"resources,omitzero"`
}

type policy struct {
	// registries are the image prefixes to allow.
	registries []string
	// requests are the default resource requests.
	requests map[string]k8s.Quantity
}

func (p policy) Validate(_ context.Context, pod, _ *Pod) error {
	for _, c := range slices.Concat(pod.Spec.InitContainers, pod.Spec.Containers) {
		if !slices.ContainsFunc(p.registries, func(r string) bool { return strings.HasPrefix(c.Image, r) }) {
			return fmt.Errorf("container %q uses image %q, which isn't from an allowed registry: %s", c.Name, c.Image, strings.Join(p.registries, ", "))
		}
	}
	return nil
}

func (p policy) Default(_ context.Context, pod, old *Pod) error {
	if old != nil {
		return nil
	}
	for _, cs := range [][]Container{pod.Spec.InitContainers, pod.Spec.Containers} {
		for i := range cs {
			for name, q := range p.requests {
				if _, ok := cs[i].Resources.Requests[name]; ok {
					continue
				}
				if cs[i].Resources.Requests == nil {
					cs[i].Resources.Requests = map[string]k8s.Quantity{}
				}
				cs[i].Resources.Requests[name] = q
			}
		}
	}
	return nil
}

func main() {
	p := &policy{
		registries: []string{"registry.example.com/"},
		requests:   map[string]k8s.Quantity{"cpu": "100m", "memory": "128Mi"},
	}
	// kube.Main parses the command line, which runs these.
	flag.Func("registries", "comma-separated image prefixes to allow (default registry.example.com/)", func(s string) error {
		p.registries = strings.Split(s, ",")
		return nil
	})
	flag.Func("default-cpu", "CPU request for containers without one (default 100m)", func(s string) error {
		p.requests["cpu"] = k8s.Quantity(s)
		return nil
	})
	flag.Func("default-memory", "memory request for containers without one (default 128Mi)", func(s string) error {
		p.requests["memory"] = k8s.Quantity(s)
		return nil
	})
	kube.Main(kube.Webhooks[Pod](p))
}

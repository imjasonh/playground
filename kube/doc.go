// Package kube is a Kubernetes controller runtime built on the standard
// library. It doesn't import client-go, apimachinery, k8s.io/api, or
// controller-runtime.
//
// A controller reconciles objects of a struct type with a [Reconciler]. Its
// Reconcile method reads the real state with [Get], [List], and [Fetch], and
// declares the desired state with [Own], [Apply], and [Delete]. For a type
// that the program defines, the framework generates a
// CustomResourceDefinition from the struct and installs it. The framework
// caches and watches every type that a reconcile reads. When an object that a
// reconcile read changes, the framework runs that reconcile again.
//
// After Reconcile returns nil, the framework applies the objects that
// Reconcile declared with server-side apply, deletes the owned objects that
// Reconcile stopped declaring, and writes the status that Reconcile set. If
// Reconcile returns an error, the framework writes only the status, and
// retries with backoff.
//
// This program runs each Website's container image with a Deployment that the
// Website owns. It also sets an annotation on a Service that the Website names
// and someone else manages:
//
//	type Website struct {
//		kube.Object `kube:"group=example.dev"`
//		Spec        WebsiteSpec   `json:"spec"`
//		Status      WebsiteStatus `json:"status,omitzero"`
//	}
//
//	type reconciler struct{}
//
//	func (reconciler) Reconcile(ctx context.Context, site *Website) error {
//		dep := kube.Own(ctx, &k8s.Deployment{
//			Object: kube.Meta(site.Name, nil),
//			Spec:   deploymentSpec(site),
//		})
//		if dep != nil {
//			site.Status.ReadyReplicas = dep.Status.ReadyReplicas
//		}
//		svc := &k8s.Service{Object: kube.Meta(site.Spec.Service, nil)}
//		svc.Annotations = map[string]string{"example.dev/website": site.Name}
//		kube.Apply(ctx, svc)
//		return nil
//	}
//
//	func main() {
//		kube.Main(kube.For[Website](reconciler{}))
//	}
//
// [Main] reads flags and runs controllers until the program receives SIGINT or
// SIGTERM. These functions return controllers for it to run:
//
//   - [For] reconciles objects of one type with a [Reconciler].
//   - [Serve] serves HTTP requests, for an API that other programs call.
//   - [Webhooks] serves admission webhooks for a type that another program
//     reconciles, such as Pods.
//   - [Volume] declares a persistent volume, for a program that keeps state on
//     disk.
//   - [Install] applies objects that the program needs but doesn't reconcile,
//     such as admission policies.
//
// A reconciler can also implement [Validator] and [Defaulter], which the
// framework serves as admission webhooks. To clean up outside Kubernetes
// before an object goes away, implement [Finalizer]. To test a reconciler
// without a cluster, call its Reconcile method with a context from [Fake].
//
// To install the program in a cluster, run its generate command from its
// module:
//
//	go run . generate -registry=REGISTRY | kubectl apply -f -
//
// The program builds itself into an image, pushes the image to REGISTRY, and
// writes YAML for the Deployment and the RBAC rules that the program needs,
// which it finds by type-checking its own source.
//
// For a guide to the API, see the [README]. For the research behind kube, its
// internals, and measurements against client-go and controller-runtime, see
// the [design document].
//
// [README]: https://github.com/imjasonh/playground/blob/main/kube/README.md
// [design document]: https://github.com/imjasonh/playground/blob/main/kube/docs/design.md
package kube

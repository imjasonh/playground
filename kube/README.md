# kube

kube is a Kubernetes controller runtime for Go, written on the standard
library alone. It doesn't import `client-go`, `apimachinery`, `k8s.io/api`, or
`controller-runtime`. You write a controller as one struct for your type and
one `Reconcile` method that reads the real state and declares the desired
state. The framework generates and installs the CustomResourceDefinition,
caches and watches every type that `Reconcile` reads, applies what `Reconcile`
declares with server-side apply, deletes what it stops declaring, and writes
status back.

For the research behind it, the internals, and measurements against
`client-go` and `controller-runtime`, see [the design document](docs/design.md).

## A controller

This program runs a Website controller. A Website names a container image, and
the controller runs it with a Deployment and reports how many replicas are
ready. It's a shortened copy of [`examples/website`](examples/website/main.go):

```go
package main

import (
	"context"

	"github.com/imjasonh/playground/kube"
	"github.com/imjasonh/playground/kube/k8s"
)

type Website struct {
	kube.Object `kube:"group=example.dev"`
	Spec        WebsiteSpec   `json:"spec"`
	Status      WebsiteStatus `json:"status,omitzero"`
}

type WebsiteSpec struct {
	Image    string `json:"image"`
	Replicas int32  `json:"replicas,omitempty" kube:"min=0,max=20,default=1"`
}

type WebsiteStatus struct {
	ReadyReplicas      int32            `json:"readyReplicas" kube:"column=Ready"`
	ObservedGeneration int64            `json:"observedGeneration,omitempty"`
	Conditions         []kube.Condition `json:"conditions,omitempty"`
}

type reconciler struct{}

func (reconciler) Reconcile(ctx context.Context, site *Website) error {
	labels := map[string]string{"app.kubernetes.io/name": site.Name}
	dep := kube.Own(ctx, &k8s.Deployment{
		Object: kube.Meta(site.Name, labels),
		Spec: k8s.DeploymentSpec{
			Replicas: new(site.Spec.Replicas),
			Selector: &k8s.LabelSelector{MatchLabels: labels},
			Template: k8s.PodTemplateSpec{
				Metadata: k8s.TemplateMeta{Labels: labels},
				Spec:     k8s.PodSpec{Containers: []k8s.Container{{Name: "web", Image: site.Spec.Image}}},
			},
		},
	})
	if dep != nil {
		site.Status.ReadyReplicas = dep.Status.ReadyReplicas
	}
	return nil
}

func main() {
	kube.Main(kube.For[Website](reconciler{}))
}
```

When the program starts, it does the following:

1. Installs a CustomResourceDefinition for `websites.example.dev`, generated
   from the struct. The `kube` field tags become validation, a default, and a
   **Ready** column in `kubectl get websites`.
1. Lists and watches Websites, and calls `Reconcile` for each one.
1. Creates or updates the Deployment with server-side apply. When the cached
   Deployment already has the declared fields, it skips the write.
1. Watches Deployments, because `Reconcile` owns one, and calls `Reconcile`
   again when the Deployment changes, including its status.
1. Writes the Website's status, with `observedGeneration` and a `Synced`
   condition that reports the last reconcile's error.
1. Deletes the Deployment when the Website is deleted, and when a later
   reconcile stops declaring it.

The program has no scheme, no generated deep-copy code, no CRD manifest, and
no watch setup. Its stripped binary is 7.7 MiB.

## Read the real state, declare the desired state

`Reconcile` reads with `Get`, `List`, and `Fetch`, and declares with `Own`,
`Apply`, and `Delete`. The framework carries out the declarations after
`Reconcile` returns `nil`. If `Reconcile` returns an error, the framework
writes only status, and retries with exponential backoff from 50 ms to 5
minutes.

| Function | What it does |
| --- | --- |
| `kube.Get[T](ctx, namespace, name)` | Returns one object from a cache, or `nil` |
| `kube.List[T](ctx, options...)` | Returns objects from a cache, sorted, filtered by namespace or label selector |
| `kube.Fetch[T](ctx, namespace, name)` | Returns one object from the API server without caching its type |
| `kube.Own(ctx, desired)` | Declares an object that the reconciled object owns, and returns it as observed |
| `kube.Apply(ctx, desired)` | Declares fields on an object that something else owns |
| `kube.Delete(ctx, object)` | Declares that an object must be deleted |
| `kube.RequeueAfter(ctx, duration)` | Asks for another reconcile after a delay |
| `kube.Permanent(err)` | Marks an error that retrying won't fix |

The framework records every `Get` and `List`. When an object that a reconcile
read changes, or an object starts or stops matching a `List`, the framework
runs that reconcile again. You don't write watches, map functions, or field
indexes, and each type's cache starts the first time a reconcile reads it.
`Fetch` isn't recorded. Use it for large objects that you read rarely, such as
the data of one Secret, so that the framework doesn't cache every object of
the type.

`Own` makes the reconciled object the owner of the declared object. When
both objects are in the same namespace, or the owner is cluster-scoped, the
framework sets an owner reference, so Kubernetes garbage collection deletes
the owned object with its owner. Owner references can't point across
namespaces or from a cluster-scoped object to a namespaced one, so in those
cases the framework adds a finalizer to the owner and deletes the owned
objects itself. Either way, objects that a reconcile declared before and
doesn't declare now are deleted.

`Apply` manages only the fields you set on an object that the controller
doesn't own, such as one annotation on someone else's Deployment. Fields that
a later reconcile stops applying are removed, and the object isn't deleted
with the reconciled object.

`Reconcile` can change the reconciled object's status. The framework writes
status changes with server-side apply and ignores changes to other fields. If
the status has an `ObservedGeneration` field, the framework sets it. If the
status has a `Conditions []kube.Condition` field, the framework keeps a
`Synced` condition in it. `kube.SetCondition` keeps a condition's
`lastTransitionTime` when its status doesn't change, so a reconcile that
observes the same state doesn't write status.

A reconciler that also has a `Finalize(ctx context.Context, obj *T) error`
method gets a finalizer on each object. The framework calls `Finalize` when the
object is deleted and removes the finalizer when `Finalize` returns `nil`. Use
it to clean up outside Kubernetes, as [`examples/dnsrecord`](examples/dnsrecord/main.go)
does for DNS records.

## Types

Any struct that embeds `kube.Object` is a Kubernetes type. Its `kube` struct
tag names the type, and its `json` tags name the fields.

### Your own types

To define a type, give it a group:

```go
type Website struct {
	kube.Object `kube:"group=example.dev,shortName=site"`
	Spec        WebsiteSpec   `json:"spec"`
	Status      WebsiteStatus `json:"status,omitzero"`
}
```

The kind defaults to the Go type name, the version to `v1`, and the scope to
`Namespaced`. Other `kube.Object` tag options are `kind`, `version`,
`plural`, `singular`, `scope=Cluster`, `shortName`, and `category`.

A field is required when its `json` tag has neither `omitempty` nor `omitzero`
and it isn't a pointer, slice, map, or interface. These field tags add
validation and display hints to the generated schema:

| Tag | Effect |
| --- | --- |
| `kube:"min=1,max=10"` | Numeric bounds |
| `kube:"minLength=1,maxLength=63"` | String length bounds |
| `kube:"minItems=1,maxItems=5"` | List length bounds |
| `kube:"enum=A\|AAAA\|CNAME"` | Allowed values |
| `kube:"default=80"` | Default that the API server fills in |
| `kube:"format=hostname"` | OpenAPI string format |
| `kube:"immutable"` | A validation rule that rejects changes after creation |
| `kube:"optional"`, `kube:"required"` | Overrides the rule based on `json` tags |
| `kube:"listType=map,listMapKey=name"` | Merges the list by key in server-side apply |
| `kube:"column=Ready"` | A `kubectl get` column |
| `pattern:"^[a-z]+$"` | Regular expression for a string |
| `doc:"..."` | Description shown by `kubectl explain` |

### Built-in types

The [`k8s`](k8s/k8s.go) package has types for common built-in objects,
including `Deployment`, `Service`, `Pod`, `ConfigMap`, `Secret`, `Namespace`,
`Job`, `Ingress`, `Role`, and `RoleBinding`. Each declares the fields that
controllers commonly use, not every field the API has.

The cache decodes and stores only the fields that a struct declares, so you
can declare your own smaller type for any built-in kind:

```go
type Pod struct {
	kube.Object `kube:"apiVersion=v1,kind=Pod"`
	Spec        struct {
		NodeName string `json:"nodeName,omitempty"`
	} `json:"spec"`
}
```

This type uses about a tenth of the memory per cached Pod that `client-go`
uses. Writing with a partial type is safe because every write is a server-side
apply of the fields you set. The framework never sends a whole object with an
update, so it can't clear fields that your struct doesn't declare.

A struct that declares no fields besides `kube.Object` gets metadata only. The
API server sends `PartialObjectMetadata`, so a controller that reconciles
every Secret by its annotations never receives or caches Secret data.

## Run a controller

`kube.Main` runs controllers with these flags:

- `-kubeconfig`: the kubeconfig file. Without it, kube uses `$KUBECONFIG`,
  then the pod's service account, then `$HOME/.kube/config`.
- `-namespace`: watch only one namespace.
- `-leader-elect`: run controllers only while this replica holds a Lease.
  Standby replicas don't start caches.
- `-addr`: serve `/healthz`, `/readyz`, and Prometheus `/metrics`, for
  example on `:8080`.
- `-v`: log debug messages.

For more control, set the fields of a `kube.Manager` and call its `Run`
method. `kube.For` takes options such as `kube.Workers(n)`,
`kube.WatchSelector(selector)`, and `kube.Resync(duration)`.

kube doesn't generate RBAC rules. The controller's service account needs
these permissions:

- `get`, `list`, and `watch` on every type that it reads.
- `create`, `patch`, and `delete` on every type that it declares with `Own`,
  `Apply`, or `Delete`. Server-side apply needs `create` for objects that
  don't exist yet.
- `patch` on the reconciled type and its `status` subresource, for finalizers
  and status.
- `get`, `create`, and `patch` on `customresourcedefinitions`, for its own
  types.
- `get`, `create`, and `update` on `leases`, with `-leader-elect`.

## Test a controller

`kube.Fake` returns a context for calling `Reconcile` directly. Pass the
objects that `Get` and `List` see, then check what the reconciler declared.
No API server or client is involved:

```go
func TestReconcile(t *testing.T) {
	site := &Website{Spec: WebsiteSpec{Image: "nginx:1.27", Replicas: 3}}
	site.Name, site.Namespace = "blog", "default"
	ctx, rec := kube.Fake(t.Context(), site)
	if err := (reconciler{}).Reconcile(ctx, site); err != nil {
		t.Fatal(err)
	}
	deps := kube.Owned[k8s.Deployment](rec)
	if len(deps) != 1 || *deps[0].Spec.Replicas != 3 {
		t.Errorf("owned Deployments = %+v", deps)
	}
}
```

The end-to-end tests run each example against a real `kube-apiserver` and
`etcd`, without a kubelet or controller manager. To run them, download the
binaries with the `fetch-envtest.sh` script:

```sh
export KUBEBUILDER_ASSETS="$(bash fetch-envtest.sh)"
go test -race ./...
```

Without `KUBEBUILDER_ASSETS`, the end-to-end tests skip. CI downloads the
binaries and runs them.

## Examples

Each example is a controller modeled on a project that people run, with unit
tests and end-to-end tests:

| Example | Modeled on | Shows |
| --- | --- | --- |
| [`website`](examples/website/main.go) | Most operators | Owned Deployment and Service, pruning, status from an owned object |
| [`replicator`](examples/replicator/main.go) | emberstack/reflector, mittwald/kubernetes-replicator | Metadata-only cache, `Fetch`, owned objects in other namespaces |
| [`reloader`](examples/reloader/main.go) | stakater/Reloader | Dependency tracking through `Get`, `Apply` on someone else's object |
| [`dnsrecord`](examples/dnsrecord/main.go) | external-dns, Crossplane | External resources, `Finalize`, `Permanent`, drift checks |
| [`janitor`](examples/janitor/main.go) | hjacobs/kube-janitor | Time-based desired state with `RequeueAfter`, `Delete` |

## Measurements

On a local `kube-apiserver` with 5,000 Pods of 8.2 KB each, compared with
`client-go` v0.37.1 and `controller-runtime` v0.25.2:

| Measurement | client-go | kube |
| --- | --- | --- |
| Heap per cached Pod | 14,687 B; 10,894 B without `managedFields` | 5,314 B with `k8s.Pod`; 1,453 B with a two-field type; 1,399 B for metadata only |
| Initial sync of 5,000 Pods | 0.20 s | 0.49 s |
| Stripped controller binary | 30.6 MiB | 7.7 MiB |
| Modules in the build | 61 | 1 |

`client-go` syncs built-in types faster because it asks for protobuf, and the
API server sends protobuf faster than JSON. The API server alone takes 0.47 s
to send these Pods as a JSON streaming list, so kube's sync time is the
server's encoding time. For the methodology and more results, see
[Measurements](docs/design.md#measurements) in the design document. To run
the benchmark, use the separate module in `bench/`:

```sh
cd bench
KUBEBUILDER_ASSETS="$(bash ../fetch-envtest.sh)" go run . -pods 5000
```

## Limitations

- kube speaks JSON only. It doesn't use protobuf, even for built-in types.
- Custom types have one version. There are no conversion or admission
  webhooks.
- kube doesn't generate RBAC rules or deployment manifests.
- One replica runs each controller at a time. There's no sharding across
  replicas.
- A manager connects to one cluster.
- `kube.WatchSelector` and `Finalize` don't combine. An object whose labels
  stop matching looks deleted to the controller, so its finalizer is never
  removed.

## Layout

| Path | Contents |
| --- | --- |
| `*.go` | The `kube` package: types, caches, dependency tracking, controllers, status, leader election, metrics, and fakes |
| `k8s/` | Types for common built-in objects |
| `examples/` | Example controllers with unit and end-to-end tests |
| `e2e/` | End-to-end tests of the framework: leader election, steady-state writes, panics, permanent errors |
| `internal/client/` | REST client, kubeconfig, authentication, discovery, and watch decoding |
| `internal/queue/` | Prioritized, deduplicating work queue |
| `internal/schema/` | OpenAPI schemas and CustomResourceDefinitions from Go types |
| `internal/clone/` | Deep copy of any Go value, compiled once per type |
| `internal/subset/` | Checks whether one JSON document's fields are a subset of another's |
| `internal/yaml/` | The YAML subset that kubeconfig files use |
| `internal/envtest/`, `internal/e2e/` | Start `etcd` and `kube-apiserver` for tests |
| `bench/` | Benchmark against `client-go` and `controller-runtime`, in its own module |

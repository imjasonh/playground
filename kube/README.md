# kube

kube is a Kubernetes controller runtime for Go, written on the standard
library alone. It doesn't import `client-go`, `apimachinery`, `k8s.io/api`, or
`controller-runtime`. You write a controller as one struct for your type and
one `Reconcile` method that reads the real state and declares the desired
state. The framework generates and installs the CustomResourceDefinition,
caches and watches every type that `Reconcile` reads, applies what `Reconcile`
declares with server-side apply, deletes what it stops declaring, and writes
status back.

The same program can validate and default objects with admission webhooks,
serve older versions of its types, and split its work across replicas. The
framework makes and renews the webhook certificates, puts every version in the
CustomResourceDefinition, and holds the Leases that divide the work. Caches
read built-in types as protobuf without generated code.

To install a program, run `go run . generate -registry=REGISTRY | kubectl
apply -f -`. The program builds itself into an image, pushes it, and writes
the Deployment and the RBAC rules that it needs, which it finds by
type-checking its own source.

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
no watch setup. The stripped binary in its image is 8.4 MiB.

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

Several writers can share one status, each with its own fields. A status
write manages every field that the status has when `Reconcile` returns, so
clear the fields that other writers own before returning. The framework
writes status only when a field that the controller sets changes, so reading
the other writers' fields costs no writes.

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

### More than one version

When a type's fields change, clients of the old version can keep using it.
Declare the old version as its own struct, with the same group and kind and
its own version, and pass it to `kube.Version`:

```go
type WebsiteV1alpha1 struct {
	kube.Object `kube:"group=example.dev,kind=Website,version=v1alpha1,deprecated"`
	Spec        struct {
		Image string `json:"image"`
		Count int32  `json:"count,omitempty"`
	} `json:"spec"`
}

func (w *WebsiteV1alpha1) ConvertTo(site *Website) error {
	site.Spec.Image, site.Spec.Replicas = w.Spec.Image, w.Spec.Count
	return nil
}

func (w *WebsiteV1alpha1) ConvertFrom(site *Website) error {
	w.Spec.Image, w.Spec.Count = site.Spec.Image, site.Spec.Replicas
	return nil
}

func main() {
	kube.Main(kube.For[Website](reconciler{}, kube.Version[WebsiteV1alpha1]()))
}
```

The CustomResourceDefinition serves both versions and stores the one that the
controller reconciles, and `Reconcile` only ever sees that one. When a client
reads or writes the other version, the API server sends the objects to a
conversion webhook that the manager serves, which calls `ConvertTo` or
`ConvertFrom` and copies metadata unchanged. The manager needs the webhook
settings that [Validate and default](#validate-and-default) describes. A
version without the two methods needs no webhook. The API server then changes
only the `apiVersion`, which works when both versions have the same fields.
`deprecated` makes the API server warn clients that use the version.

### Change a type

The manager installs each CustomResourceDefinition when it starts, so a new
release of the program updates it. Before it does, the manager compares the
new CRD with the one in the cluster and with the objects that exist, and
changes the CRD only in ways that lose no data:

- If objects set a field that the new type doesn't declare, or whose type the
  new type changes, the CRD keeps the field as it was, and the manager logs a
  warning. A field that leaves the CRD loses its values the next time anything
  writes each object. To remove such a field, clear it in the objects first,
  or add a version without it.
- If the CRD has a version newer than every version the program declares, the
  manager leaves the CRD as it is. That happens when an older release starts
  after a newer one, in a rollback or a rolling update.
- If the new type requires a field that objects don't set, the manager logs a
  warning, because changes to those objects' `spec` fail until they set it.
  Give the field a default with `kube:"default=..."`, or make it optional.

Other changes, such as new optional fields, new versions, and new validation,
apply as they are. Since Kubernetes 1.33, [validation
ratcheting](https://kubernetes.io/docs/tasks/extend-kubernetes/custom-resources/custom-resource-definitions/#validation-ratcheting)
accepts an update that leaves an invalid value unchanged.

To change the version that the API server stores and retire the old one, ship
these releases in order, each after the previous one has run:

1. Reconcile the old version and add the new one with `kube.Version`. Clients
   can start to use the new version, and a rollback from the next release
   still has a program that converts both.
2. Reconcile the new version and pass the old one to `kube.Version`. The API
   server stores the new version from then on. The manager rewrites objects
   stored in older versions, then removes those versions from the CRD's
   `status.storedVersions`, and logs `migrated stored objects`.
3. Add `unserved` to the old version's tag. The API server stops serving it,
   and the manager removes the entries that name it from each object's
   `metadata.managedFields`. Once a version is gone from the CRD, server-side
   apply fails on any object with such an entry, and the entry can't be
   removed anymore
   ([kubernetes/kubernetes#111937](https://github.com/kubernetes/kubernetes/issues/111937)).
4. Delete the old version. If objects might still be stored in it or have
   `managedFields` entries for it, the manager doesn't start, and its error
   names the release to run first.

The first release is optional, but without it a rollback from the second has
no program that knows the new version. If something else installed the CRD,
such as Helm, the manager doesn't change it, and that tool or a
[StorageVersionMigration](https://kubernetes.io/docs/tasks/manage-kubernetes-objects/storage-version-migration/)
handles the upgrade.

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

A smaller type also runs fewer reconciles. A change to an object runs a
reconcile again only if it changes a field that the type declares, so a
controller that reads this `Pod` type doesn't reconcile again when a Pod's
status changes.

A struct that declares no fields besides `kube.Object` gets metadata only. The
API server sends `PartialObjectMetadata`, so a controller that reconciles
every Secret by its annotations never receives or caches Secret data. Every
change to a metadata-only object counts, because the type can't see the
fields that its reconciler fetches.

Caches read built-in types as protobuf, which the API server encodes in about
half the time of JSON. kube has no generated protobuf code. A schema of the
field numbers of built-in kinds, generated from `k8s.io/api`, matches your
struct's fields by their JSON names, and the decoder skips fields that the
struct doesn't declare. If the struct declares a field that the schema lacks,
such as one that a later Kubernetes version added, or the kind is an alpha or
beta version, the cache reads that type as JSON. Custom types are always JSON.

## Validate and default

A reconciler can check objects before the API server stores them, for rules
that a field tag can't express. Add a `Validate` method to reject an object,
and a `Default` method to change it:

```go
func (reconciler) Validate(ctx context.Context, site, old *Website) error {
	if !strings.Contains(site.Spec.Image, ":") {
		return errors.New("spec.image needs a tag, such as nginx:1.27")
	}
	return nil
}

func (reconciler) Default(ctx context.Context, site, old *Website) error {
	if site.Labels["app.kubernetes.io/name"] == "" {
		if site.Labels == nil {
			site.Labels = map[string]string{}
		}
		site.Labels["app.kubernetes.io/name"] = site.Name
	}
	return nil
}
```

The framework registers a validating and a mutating admission webhook for the
type and calls the methods for every create and update. On a create, `old` is
`nil`. The person or program that made the request sees the error that
`Validate` returns. `Default` changes the object in place, and the framework
sends the API server a JSON patch of only the fields that changed, so a type
that declares a few fields can't drop the others. On an update, `Default`
must change only fields that an update may change. The methods can read with
`Get`, `List`, and `Fetch`, and calling `Own`, `Apply`, or `Delete` rejects
the request.

To validate or default a type that another program reconciles, pass a value
with the methods to `kube.Webhooks`:

```go
kube.Main(kube.For[Website](reconciler{}), kube.Webhooks[k8s.Pod](podPolicy{}))
```

A webhook for a built-in type skips `kube-system` and the namespace of the
webhook's Service, so that the controller's own Pods can start while its
webhook is down. With `-namespace`, webhooks apply only in that namespace.
[`examples/podpolicy`](examples/podpolicy/main.go) is a webhook for Pods.

Every replica serves the webhooks over HTTPS, whether or not it holds a lease.
The manager makes a certificate authority and a serving certificate, keeps
them in a Secret that replicas share, renews the serving certificate before it
expires, and registers the webhooks with the CA bundle. You provide the
Service. Set `-webhook-service` to a Service that selects the controller's
Pods and routes port 443 to port 9443. Outside a cluster, set `-webhook-url`
to an `https` URL at which the API server reaches the program. When a later
version of the program has fewer webhooks, the manager deletes the webhook
configuration it no longer needs.

## Run a controller

`kube.Main` runs controllers with these flags:

- `-kubeconfig`: the kubeconfig file. Without it, kube uses `$KUBECONFIG`,
  then the pod's service account, then `$HOME/.kube/config`.
- `-namespace`: watch only one namespace.
- `-leader-elect`: reconcile only while this replica holds a Lease.
- `-shards`: split reconciles across replicas into this many shards.
- `-webhook-service`: the Service, as `name` or `namespace/name`, through
  which the API server reaches the webhooks.
- `-webhook-url`: an `https` URL through which the API server reaches the
  webhooks of a program outside the cluster.
- `-webhook-addr`: where to serve webhooks. The default is `:9443`.
- `-addr`: serve `/healthz`, `/readyz`, and Prometheus `/metrics`, for
  example on `:8080`.
- `-v`: log debug messages.

For more control, set the fields of a `kube.Manager` and call its `Run`
method. `kube.For` takes options such as `kube.Workers(n)`,
`kube.WatchSelector(selector)`, and `kube.Resync(duration)`.

### Install in a cluster

`kube.Main` also has a `generate` command, which pushes an image of the
program and writes the YAML that installs it. Run it from the program's module
with `go run`, and pipe its output to `kubectl`:

```sh
go run ./examples/website generate -registry=ghcr.io/you | kubectl apply -f -
```

The command does the following:

1. Finds the types that the program reads and writes. Each controller reports
   its type, the types that it owns, and its webhooks. The command also
   type-checks the program's packages to find every call to `Get`, `List`,
   `Fetch`, `Own`, `Apply`, and `Delete`, and the type that each call uses,
   including calls inside generic helpers.
1. Builds the program for each platform with `CGO_ENABLED=0`.
1. Builds an image for each platform on `cgr.dev/chainguard/static`, with the
   program at `/app/PROGRAM` as the entrypoint, running as user 65532. It
   pushes the images and an index of them to `REGISTRY/PROGRAM` with
   [go-containerregistry](https://github.com/google/go-containerregistry),
   using the credentials from `docker login` or `podman login`.
1. Writes YAML that installs the image by digest: a Namespace, a
   ServiceAccount, a ClusterRole and a Role with only the rules that the
   program needs, their bindings, a Deployment, a PodDisruptionBudget, and a
   Service for webhooks. With more than one replica, the Deployment runs the
   program with `-leader-elect`, or with `-shards` when you set `-shards`.
   The container's root file system is read-only, with an `emptyDir` volume
   at `/tmp` for temporary files. `-tmp-size` limits the volume's size.

The images have fixed timestamps, so the same source gives the same digest,
and running `generate` again without changes leaves the cluster as it was.
When the program starts in the cluster, it installs its own
CustomResourceDefinitions and webhook configurations.

A program watches every namespace unless you set `-watch-namespace`. Then
it watches one namespace, and the rules for namespaced resources go in a
Role there instead of the ClusterRole, so a program that reads Secrets, for
example, can read them only in that namespace. Rules for cluster-scoped
resources, such as CustomResourceDefinitions, stay in the ClusterRole. So do
the rules for a reconciled type with more than one version, because the
program migrates its stored objects in every namespace, and for a type whose
`kube` tag doesn't say `scope=Namespaced` or `scope=Cluster`.

A type whose `kube` tag says `local`, such as
`kube:"apiVersion=v1,kind=ConfigMap,local"`, is one that the program reads and
writes only in its own namespace, for example to keep state there. Its rules
go in the Role in the program's namespace, wherever the program watches. Use
a local type only with `Fetch`, `Apply`, and `Delete`. `Get`, `List`, and
`Own` read caches that watch every namespace that the program watches, so they
fail the reconcile with a local type, and `generate` rejects a controller that
reconciles or owns one. Give each local object the program's namespace:
`Fetch` and `Apply` fail the reconcile when it's empty, rather than use the
namespace of the object being reconciled, which the Role doesn't cover.

| Flag | Default | Description |
| --- | --- | --- |
| `-registry` | Required | Registry, and optionally a repository prefix, to push to |
| `-base` | `cgr.dev/chainguard/static:latest` | Base image |
| `-platform` | `linux/amd64,linux/arm64` | Platforms to build for |
| `-namespace` | The program's name | Namespace to install in |
| `-replicas` | 2 | Pods to run |
| `-shards` | 1 | Shards to split reconciles across |
| `-tag` | `latest` | Tag for the image, in addition to its digest |
| `-tmp-size` | No limit | Size limit of the `emptyDir` volume at `/tmp`, such as `1Gi` |
| `-watch-namespace` | Every namespace | Namespace for the program to watch; the rules for namespaced resources go in a Role there |

Flags after `--` go to the program in the Deployment:

```sh
go run ./examples/podpolicy generate -registry=ghcr.io/you -- -registries=ghcr.io/you/ |
  kubectl apply -f -
```

go-containerregistry is kube's only dependency, and only `generate` uses it.
The command builds the copy of the program for the image with the
`kube_nogenerate` build tag, which leaves the command out, so the program in
the cluster links only kube and the standard library.

### Replicas

With `-leader-elect`, replicas take turns. The replica that holds a Lease
reconciles, and the others wait without starting caches. A replica that stops
releases the Lease, so another takes over in about 2 seconds. If a replica
crashes, another takes over when its Lease expires, 15 seconds later.

With `-shards=N`, replicas share the work. The framework splits each
controller's objects into N shards by a hash of their namespace and name, and
guards each shard with its own Lease. Each replica also renews a Lease that
says it's alive, and every replica assigns the shards to the live replicas
with rendezvous hashing, so a replica that joins or leaves moves only its own
share. A replica gives up a shard by finishing the reconciles in it first, so
two replicas never reconcile one object at the same time. Shards divide
reconciles and the API calls they make, not memory, because every replica
caches every object. Each held shard writes its Lease every 2 seconds, so pick
N a few times the number of replicas, such as 16 for 4 replicas.

A replica that loses its Leases stops reconciling and tries to take them back.
It keeps serving webhooks, and `/readyz` reports ready once the webhooks serve
and the controllers it runs have synced, so the webhook Service sends requests
to standby replicas too.

### Permissions

The `generate` command writes these rules. If you install the program another
way, its service account needs these permissions:

- `get`, `list`, and `watch` on every type that it reads.
- `create`, `patch`, and `delete` on every type that it declares with `Own`,
  `Apply`, or `Delete`. Server-side apply needs `create` for objects that
  don't exist yet.
- `patch` on the reconciled type and its `status` subresource, for finalizers
  and status.
- `get`, `create`, and `patch` on `customresourcedefinitions`, and `patch` on
  `customresourcedefinitions/status`, for its own types. To check and migrate
  objects when a type changes, it also needs `list` on its own types in every
  namespace.
- `get`, `list`, `create`, `update`, and `delete` on `leases`, with
  `-leader-elect` or `-shards`.
- `get`, `create`, and `update` on `secrets` in its namespace, and `get`,
  `patch`, and `delete` on `validatingwebhookconfigurations` and
  `mutatingwebhookconfigurations`, for webhooks.

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

As in a cluster, a read sees the objects of every type of its kind. A
reconcile that reads your own smaller `Deployment` type sees each
`k8s.Deployment` that you pass to `kube.Fake`.

To test `Validate`, `Default`, `ConvertTo`, and `ConvertFrom`, call them
directly. With a context from `kube.Fake`, `Validate` and `Default` can read
objects with `Get` and `List`.

The end-to-end tests run each example against a real `kube-apiserver` and
`etcd`, without a kubelet or controller manager. To run them, download the
binaries with the `fetch-envtest.sh` script:

```sh
export KUBEBUILDER_ASSETS="$(bash fetch-envtest.sh)"
go test -race ./...
```

Without `KUBEBUILDER_ASSETS`, the end-to-end tests skip. CI downloads the
binaries and runs them.

One more test installs the website and podpolicy examples with `generate` in a
[kind](https://kind.sigs.k8s.io/) cluster, and pushes their images to a local
registry. It needs Docker and `kubectl`, and installs kind if it's missing:

```sh
KUBE_KIND_E2E=1 go test -v -count=1 ./e2e/kind/
```

The test runs a script and the examples in other processes, so `go test`
can't tell when they change. `-count=1` keeps it from reusing a cached
result.

CI runs it when kube changes. To keep the cluster afterward, set
`KUBE_KIND_KEEP=1`. If your network can't reach `cgr.dev`, set
`KUBE_KIND_CHAINGUARD=docker.io/chainguard` to pull Chainguard's images
from Docker Hub.

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
| [`podpolicy`](examples/podpolicy/main.go) | Kyverno and OPA Gatekeeper policies | Admission webhooks for Pods with `kube.Webhooks`, a patch that keeps undeclared fields |

## Measurements

On a local `kube-apiserver` with 5,000 Pods of 8.2 KB each, compared with
`client-go` v0.37.1 and `controller-runtime` v0.25.2:

| Measurement | client-go | kube |
| --- | --- | --- |
| Heap per cached Pod | 14,685 B; 10,894 B without `managedFields` | 5,442 B with `k8s.Pod`; 1,551 B with a two-field type; 1,390 B for metadata only |
| Initial sync of 5,000 Pods | 0.20 s | 0.18 s; 0.51 s with protobuf off |
| Stripped controller binary | 30.6 MiB | 8.4 MiB in its image; 11.7 MiB with `generate` |
| Modules in the build | 61 | 1 in its image; 10 with `generate` |

Both read the Pods as protobuf, which the API server sends in 0.18 s as a
streaming list, against 0.49 s as JSON. For the methodology and more results,
see [Measurements](docs/design.md#measurements) in the design document. To
run the benchmark, use the separate module in `bench/`:

```sh
cd bench
KUBEBUILDER_ASSETS="$(bash ../fetch-envtest.sh)" go run . -pods 5000
```

## Limitations

- `generate` follows the type parameters of generic functions to the types
  that the program calls them with. It can't follow the type parameter of a
  generic type, as in a method of `reconciler[T]`, or a type argument that
  contains a type parameter, such as `Item[T]`. For those calls it prints a
  warning, and you add the permissions yourself.
- `generate` needs the program's source and the `go` command, so the copy of
  the program in the image can't run it. The image holds only the program.
  To ship other files, embed them with `embed`.
- Shards divide reconciles, not memory. Every replica caches every object.
- Webhooks run on create and update. There's no validation of deletes.
- Conversion can't change metadata.
- Before it updates a CRD, the manager compares field names, types, and
  required fields, not validation such as enums and bounds.
- The manager makes its own webhook certificates and doesn't use
  cert-manager. Its certificate authority lasts ten years. In the last year,
  the manager replaces it and trusts both until the old one expires.
- Protobuf covers the stable versions of built-in types in the schema that
  ships with kube. A type that declares a newer field, and every custom type,
  is read as JSON.
- A manager connects to one cluster.
- `kube.WatchSelector` and `Finalize` don't combine. An object whose labels
  stop matching looks deleted to the controller, so its finalizer is never
  removed.

## Layout

| Path | Contents |
| --- | --- |
| `*.go` | The `kube` package: types, caches, dependency tracking, controllers, status, webhooks, versions, shards, metrics, and fakes |
| `k8s/` | Types for common built-in objects |
| `examples/` | Example controllers and webhooks with unit and end-to-end tests |
| `e2e/` | End-to-end tests of the framework: shards and leader election, webhooks, versions, protobuf, steady-state writes, shared status, changes that types can't see, panics, permanent errors, and `generate`; `e2e/kind/` installs the examples in a kind cluster |
| `internal/client/` | REST client, kubeconfig, authentication, discovery, and JSON and protobuf watch decoding |
| `internal/protobuf/` | Protobuf decoding of built-in types into partial structs, and its schema; `gen/` is the separate module that generates the schema |
| `internal/certs/` | Certificate authority and serving certificates for webhooks |
| `internal/jsonpatch/` | JSON patches for mutating webhooks |
| `internal/queue/` | Prioritized, deduplicating work queue |
| `internal/schema/` | OpenAPI schemas and CustomResourceDefinitions from Go types |
| `internal/clone/` | Deep copy of any Go value, compiled once per type |
| `internal/subset/` | Checks whether one JSON document's fields are a subset of another's |
| `internal/yaml/` | The YAML subset that kubeconfig files use, and the YAML that `generate` writes |
| `internal/analysis/` | Type-checks a program to find the types that it passes to kube's generic functions, for `generate`'s RBAC rules |
| `internal/image/` | Builds and pushes images with go-containerregistry, for `generate` |
| `internal/envtest/`, `internal/e2e/` | Start `etcd` and `kube-apiserver` for tests |
| `bench/` | Benchmark against `client-go` and `controller-runtime`, in its own module |

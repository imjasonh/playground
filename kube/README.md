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
serve older versions of its types, run an HTTP API that checks its callers'
service account tokens, keep state on a persistent volume, and split its work
across replicas. The
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
minutes. If a declaration fails, for example because an admission policy
rejects an object, the framework writes the status that `Reconcile` set and
retries in the same way. In the retry, `kube.LastError` returns the error, so
the reconcile can report it in the status. Each process keeps the errors in
memory, so `kube.LastError` returns `nil` after a restart or a shard move. An
error from the API server can quote the values that it rejected, so if those
values are secret, don't copy the error into a status.

| Function | What it does |
| --- | --- |
| `kube.Get[T](ctx, namespace, name)` | Returns one object from a cache, or `nil` |
| `kube.List[T](ctx, options...)` | Returns objects from a cache, sorted, filtered by namespace or label selector |
| `kube.Fetch[T](ctx, namespace, name)` | Returns one object from the API server without caching its type |
| `kube.Own(ctx, desired)` | Declares an object that the reconciled object owns, and returns it as observed |
| `kube.Apply(ctx, desired)` | Declares fields on an object that something else owns |
| `kube.Delete(ctx, object)` | Declares that an object must be deleted |
| `kube.Eventf(ctx, eventType, reason, format, args...)` | Records an event about the reconciled object; see [Record events](#record-events) |
| `kube.RequeueAfter(ctx, duration)` | Asks for another reconcile after a delay |
| `kube.Permanent(err)` | Marks an error that retrying won't fix |
| `kube.LastError(ctx)` | Returns the error that the previous reconcile of the object failed with, or `nil` |

The framework records every `Get` and `List`. When an object that a reconcile
read changes, or an object starts or stops matching a `List`, the framework
runs that reconcile again. You don't write watches, map functions, or field
indexes, and each type's cache starts the first time a reconcile reads it.
`Fetch` isn't recorded. Use it for large objects that you read rarely, such as
the data of one Secret, so that the framework doesn't cache every object of
the type. A `Fetch` with a constant namespace and name needs permission to
get only that object, as [Install in a cluster](#install-in-a-cluster)
describes.

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

If the type that you pass to `Apply` has a status, the framework applies the
status too, so a controller can write its own fields in another controller's
status. The status goes to the object's status subresource in a second
request, with the same field manager, unless the first request fails. The
framework applies the status with force, so the controller takes over every
field in it, including zero values in fields without `omitempty` or
`omitzero`. A value that another manager also set becomes shared, and neither
manager can remove it alone. So set only your own fields, and build a fresh
object rather than editing one that `Get` returned.

When a later reconcile stops applying a status field, the controller gives it
up, and the API server removes it unless another manager also set it. So an
empty status gives up every status field that an earlier reconcile applied,
even one that failed or that ran in an earlier run of the program. When there
are none, the framework sends no status request. If the cluster doesn't serve
a status subresource for the object, a status that isn't empty fails the
reconcile.

Applying a status needs permission to patch the object's status subresource,
and `generate` grants it for each type with a status that the program
applies. In `kube/k8s`, `Deployment`, `Job`, `Namespace`, `Node`, `Pod`, and
`Service` have a status. To leave status alone and keep `generate` from
granting the permission, apply a type that declares no status, as
[`examples/reloader`](examples/reloader/main.go) does. The framework sends
no request for a status that no version of the program has set, so that
status needs no permission. Without the permission, a reconcile that gives up
status fields fails, and the fields stay until the controller can patch the
status.

A reconcile can pass each object to `Own` or `Apply` only once, whatever type
it uses, and a second call fails the reconcile. To apply fields and a status
to one object, pass one type that declares both to `Apply`, because `Own`
doesn't apply a status. Two `Apply` calls for one object would share a field
manager, so the second request would remove the fields that the first applied.

The framework writes the reconciled object's status from the object that
`Reconcile` received, not with `Apply`. When the reconciled type has a
status, applying a status to the reconciled object itself fails the
reconcile, unless the status is empty.

`Reconcile` can change the reconciled object's status. The framework writes
status changes with server-side apply and ignores changes to other fields. If
the status has an `ObservedGeneration` field, the framework sets it. If the
status has a `Conditions []kube.Condition` field, the framework keeps a
`Synced` condition in it. `kube.SetCondition` keeps a condition's
`lastTransitionTime` when its status doesn't change, so a reconcile that
observes the same state doesn't write status. It can keep only a time that
the slice already holds. So for a condition that you apply to another object,
start from your own condition as the cached target has it, which
`kube.FindCondition` returns, rather than from the target's whole list, which
would apply other managers' conditions too.

Several writers can share one status, each with its own fields, including
controllers that write their fields with `Apply`. A status write manages
every field that the status has when `Reconcile` returns, so clear the fields
that other writers own before returning. The framework writes status only
when a field that the controller sets changes, so reading the other writers'
fields costs no writes.

A reconciler that also has a `Finalize(ctx context.Context, obj *T) error`
method gets a finalizer on each object. The framework calls `Finalize` when the
object is deleted and removes the finalizer when `Finalize` returns `nil`. Use
it to clean up outside Kubernetes, as [`examples/dnsrecord`](examples/dnsrecord/main.go)
does for DNS records.

When you remove `Finalize` from a reconciler, objects keep the finalizer that
an earlier version of the program added, such as
`kube.imjasonh.github.io/dnsrecord`, and the framework removes it the next
time that it reconciles each object. Removing a finalizer takes permission to
patch the reconciled type, which `generate` grants only to controllers that
need it. Until no object has the finalizer, pass `kube.RemovesFinalizer()` to
`kube.For`. Without the option, the program might not have that permission.
Then a deleted object stays, and the reconcile fails with an error that names
the option.

Reads return what the framework wrote. After the framework writes status,
applies or deletes an object, or changes a finalizer, `Get`, `List`, and `Own`
return what the API server stored, even before the cache's watch delivers the
change. A reconcile that runs right after a write, such as one that
`RequeueAfter` asks for, reads the written object and doesn't repeat the
write. Changes that other clients make appear when the watch delivers them.
Other replicas are other clients, so after a [shard](#replicas) moves, the
first reconciles in it can repeat the previous holder's last writes. For the
exceptions, see [Limitations](#limitations).

## Record events

`kube.Eventf` records an event about the object being reconciled, which
`kubectl describe` and `kubectl get events` show. Record an event when the
controller does something that people want to know about, such as a change
outside Kubernetes, rather than on every reconcile. The
[`website`](examples/website/main.go) example records one each time the
reason of its `Ready` condition changes:

```go
if old := kube.FindCondition(site.Status.Conditions, "Ready"); old == nil || old.Reason != ready.Reason {
	kube.Eventf(ctx, kube.Normal, ready.Reason, "%d of %d replicas are ready", site.Status.ReadyReplicas, site.Spec.Replicas)
}
```

The event's type is `kube.Normal` or `kube.Warning`, and its reason is a
CamelCase word such as `Serving`. If the type is anything else, or the reason is
empty or longer than 128 bytes, `Eventf` records nothing and logs a warning,
because the API server would reject the event. The framework formats the note
with `fmt.Sprintf`, replaces invalid UTF-8 in it with U+FFFD, and cuts it to
1,024 bytes.

After `Reconcile` or `Finalize` returns, the framework writes the events as
`events.k8s.io/v1` Events in the object's namespace, or in `default` for a
cluster-scoped object. It writes them when the reconcile returns an error too,
so a Warning can explain the error. Each Event names the controller as its
reporting controller, and `Reconcile` or `Finalize` as its action. In
`kubectl describe website blog`, the events look like this:

```
Events:
  Type    Reason    Age   From     Message
  ----    ------    ----  ----     -------
  Normal  Creating  12s   website  0 of 2 replicas are ready
  Normal  Updating  12s   website  0 of 2 replicas are ready
  Normal  Starting  12s   website  0 of 2 replicas are ready
  Normal  Serving   10s   website  2 of 2 replicas are ready
```

An event with the same type, reason, and note as one that the controller
recorded about the same object less than 6 minutes earlier is a repeat. The
first repeat sets the Event's count to 2 right away. The framework counts
later repeats in memory, and writes the count every 6 minutes and when the
manager stops. `kubectl describe` shows the count, as in `3m (x35 over 2h)`.
However often a reconcile repeats an event, for example while it fails and
retries, the framework makes two writes for it and then at most one every 6
minutes. A note that changes every time, such as one with a timestamp, makes
every event a new Event, so keep values like that in status.

Recording an event never fails or delays a reconcile. The framework writes
events in the background from a queue of 1,000 events. When the queue is
full, it drops events, and when a write fails, it logs the error. The
`kube_events_total` metric counts events by controller and result: `created`,
`updated` with a new count, `failed`, or `dropped`.

Events are only about the reconciled object, which is the object that people
describe to see what the controller did. To report something about an owned
object, name it in the note. Once a call such as `Get` has failed the
reconcile, `Eventf` does nothing, because what the reconcile saw is
incomplete. In a webhook, `Eventf` fails the request, as `Own` does.

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
| `kube:"mapType=atomic"` | Replaces the whole map or struct in server-side apply, so one manager owns it |
| `kube:"column=Ready"` | A `kubectl get` column |
| `pattern:"^[a-z]+$"` | Regular expression for a string |
| `doc:"..."` | Description shown by `kubectl explain` |

A controller that reconciles the type installs its CustomResourceDefinition
when the program starts, and later releases update it, as [Change a
type](#change-a-type) describes. A program can also own a type that none of
its controllers reconciles, such as the reports that
[`examples/imagereport`](examples/imagereport/main.go) writes for people to
read. If the cluster doesn't have the CRD, such a program creates it the first
time that it owns an object of the type, or at startup with `kube.Owns`. If
that fails at startup, the program logs the error and starts anyway, and its
next `Own` of the type tries again.

A program that owns a type without reconciling it never changes a CRD that
exists, because only a program that reconciles the type knows all of the
type's versions. If the CRD doesn't serve the owning program's version of the
type, `Own` fails, and the framework retries the reconcile. If two programs
try to create the CRD at the same time, one of them creates it, and both use
it if it serves both of their versions.

A program that only reads a type never creates its CRD. While the CRD is
missing, `Get` and `List` of the type fail the reconcile, so a later `Own` in
it does nothing, and the framework retries it. `Fetch` returns `nil` and
doesn't fail the reconcile. If a reconcile calls `Get` or `List` for a type
before it first owns an object of the type, declare the type with `kube.Owns`,
so that the program creates the CRD when it starts.

When a program that reconciles the type starts, it installs its own CRD over
the created one. Until then, the CRD keeps the schema that it was created with,
even when a later release of the program that created it changes the type. To
update the CRD along with the type, reconcile the type, even with a
`Reconcile` method that does nothing. The reconciling program can't take over
the created CRD if the two programs disagree about the type:

- If they declare different scopes, the reconciling program fails to start,
  because a CRD's scope can't change.
- If the created version isn't one that the reconciling program declares, as
  its own version or with `kube.Version`, the reconciling program fails to
  start.
- If they set the `Domain` field of `kube.Manager` differently, the
  reconciling program doesn't recognize the created CRD as the framework's. It
  uses the CRD as it is and never updates it.

To recover, make the declarations agree, and then delete the created CRD while
it has no objects, because deleting a CRD deletes its objects. If only the
version differs, you can instead declare the created version in the
reconciling program with `kube.Version`, which keeps the objects.

The created CRD has the schema of the owning program's struct, so declare every
field of a type that you own. A struct that only reads the type can declare
only the fields that it uses. To own a type without creating its CRD, give its
`apiVersion` and `kind` instead of a group, as for a [built-in
type](#built-in-types).

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
webhook is down. With `-watch-namespace`, webhooks apply only in that
namespace.
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

## Serve an HTTP API

A program can serve HTTP next to its controllers, for endpoints that other
programs call. Pass a handler to `kube.Serve`:

```go
kube.Main(kube.For[Probe](&reconciler{}), kube.Serve(api.handler()))
```

Every replica serves the handler at `-serve-addr`, `:8081` by default,
whether or not it holds a lease, and `/readyz` reports ready once it
serves. As in a webhook, the handler can read with `Get`, `List`, and
`Fetch` through the request's context, and calling `Own`, `Apply`, or
`Delete` cancels the context with an error. To change the cluster in
response to a request, trigger a reconcile and make the change there. A
program can have one `kube.Serve`, so serve every path from one handler,
such as an `http.ServeMux`.

When the program stops, it stops accepting connections, and requests in
progress have up to 10 seconds to finish before their contexts are
canceled. `kube.Trigger` returns false during that time.

The `generate` command runs the program with `-serve-addr=:8081` and adds
port 80 to the program's Service, which routes to the handler. It also
gives the container a `preStop` hook that sleeps for 5 seconds, so the
Service stops sending the Pod connections before the program stops. The
hook's `sleep` action needs Kubernetes 1.30 or later. A program with a
`kube.Volume` gets no hook. It runs one Pod, which a rollout stops before
it starts the next, so no other Pod can take the connections, and the
sleep would only make each rollout 5 seconds longer. `generate` writes no
NetworkPolicy. If NetworkPolicies in the program's namespace deny traffic by
default, allow the callers to reach port 8081 of the program's Pods.

The server uses plain HTTP and doesn't authenticate requests. Check each
caller's token with `kube.ReviewToken`. Tokens cross the Pod network
unencrypted, so have callers send tokens for your server's audience, which
the API server rejects.

[`examples/probe`](examples/probe/main.go) serves an API that uses each
function in this section.

### Check a caller's token

A caller proves who it is with a service account token. Give the caller's
Pod a projected token for an audience that names your server:

```yaml
volumes:
- name: token
  projected:
    sources:
    - serviceAccountToken:
        audience: probe
        path: token
```

The caller sends the token in an `Authorization: Bearer` header, and the
handler asks the API server about it with `kube.ReviewToken`:

```go
token, _ := strings.CutPrefix(r.Header.Get("Authorization"), "Bearer ")
review, err := kube.ReviewToken(r.Context(), token, "probe")
switch {
case err != nil:
	slog.Error("reviewing a token failed", "err", err)
	http.Error(w, "can't check the token now", http.StatusInternalServerError)
case !review.Authenticated:
	http.Error(w, review.Error, http.StatusUnauthorized)
default:
	namespace, name, _ := review.User.ServiceAccount()
	fmt.Fprintf(w, "hello, %s in %s\n", name, namespace)
}
```

`ReviewToken` needs at least one audience. A token passes only if it's
valid for one of the audiences that you pass, so a token for another server
or for the API server fails. A token that the kubelet projects into a Pod
also names the Pod in `review.User.Extra`, and stops working when the Pod is
deleted. An invalid token isn't an error. `ReviewToken` returns an error
only when an audience is empty or when it can't ask, for example because
the program may not create TokenReviews. Log the error instead of sending
it to the caller, because it can name the program's service account and the
permission that it lacks. Each call asks the API server.

### Request a token for the program

`kube.RequestToken` returns a token for the program's own service account,
for a server that trusts the cluster's tokens, such as
[Octo STS](https://github.com/octo-sts/app) or another program that calls
`ReviewToken`:

```go
token, expires, err := kube.RequestToken(ctx, "octo-sts.dev")
```

Pass the audience as a constant, as a string literal or a `const`. For each
constant audience, the `generate` command adds a projected token to the
program's Pod, and `RequestToken` reads it from the directory that
`-token-dir` names. The token is bound to the Pod, the kubelet renews it, and
the program needs no permission to request tokens.

For an audience that isn't a constant, `RequestToken` asks the API server
for a new token, and `generate` lets the program request tokens for its own
service account. That permission also lets anyone who holds a token for the
service account, such as the token in the program's Pod, make tokens for any
audience that outlive the Pod, so prefer constant audiences. The program
asks the API server which service account it runs as, so this works in a Pod
and with a kubeconfig that holds a service account's token. In a Pod, the
new token is bound to the Pod.

If there's no mounted token and the program may not request one,
`RequestToken` returns an error that names the missing token file, or says
that `-token-dir` isn't set. Rerun `generate` and apply its output instead
of granting the permission by hand.

A token lasts about an hour, so use the returned expiry. Call `RequestToken`
each time you need a token, or reuse one until shortly before it expires.
Call it in a reconcile or in a `kube.Serve` handler.

Choose the audience in the program. If an object's author chose both the
audience and where the program sends the token, they could have the program
send them a token for the API server, with the program's permissions. The
probe example sends every check a token for the audience `probe`, and a
Probe chooses only the URL.

### Trigger a reconcile

When a handler learns that something outside Kubernetes changed, it can
reconcile an object at once, instead of at the next resync or requeue, with
`kube.Trigger`:

```go
if kube.Trigger[Probe](r.Context(), namespace, name) {
	w.WriteHeader(http.StatusAccepted)
	return
}
w.Header().Set("Connection", "close")
http.Error(w, "try again", http.StatusServiceUnavailable)
```

`Trigger` adds the object to the work queue of each controller that
reconciles its kind and returns true. The reconcile starts soon, even if
the object is waiting to retry an error. `Trigger` writes nothing to the
API server, so it needs no permissions.

On a replica that doesn't reconcile the object, `Trigger` returns false and
does nothing. That's the case before the controllers start or after they
stop, when the object isn't in the controller's cache, and, with
`-leader-elect` or `-shards`, when another replica holds the object's shard.
`Trigger` doesn't send the request to that replica. Instead, as in the
example, answer `503` and close the connection, so that the client's next
try can reach another replica through the Service. A true result holds even
if the replica loses the shard before the reconcile starts, because the
replica that takes the shard reconciles all of its objects. That replica
queues them at low priority, so the reconcile then waits its turn with the
rest of the shard.

To hand data from a request to the reconcile, such as a result that a
client posts, keep the data in memory under the object's key, call
`Trigger`, and have the reconcile write the data to the object, for example
to its status. The framework carries out a reconcile's writes after
`Reconcile` returns, and a write can fail. If the shard moves before the
retry, the retry runs on another replica, which doesn't have the data. So
the data is safe only once the object holds it:

- The handler keeps the data until `kube.Get` shows the change, and only
  then answers the client. If the change doesn't show in time, it answers
  `503` so that the client tries again. Either way, it drops the data when
  it answers.
- The reconcile reads the data without removing it, so a retry on the same
  replica still finds it. Then it reads the object with `kube.Get` and adds
  the data to what that copy holds, because later reconciles run without
  the data.

Don't add the data to the object that `Reconcile` receives. The framework
read that object before `Reconcile` ran, often before the cache had the
previous reconcile's write. In between, a handler can see that write,
answer, and drop its data, so writing back the older object would remove
data that a client was told was saved. Reading the data first avoids that.
A handler drops data only once `kube.Get` shows it, and `kube.Get` reads
one cache in handlers and reconciles. That cache never goes back to an
older version of an object, so data that's no longer pending is in the
object that `kube.Get` returns afterward.

The data also stays safe when another replica takes over the object's shard
before its cache has the previous holder's last writes. Until a status write
for the object succeeds on that replica, or a write that adds or removes the
framework's finalizer does, each of these writes requires the resource
version in the replica's cache. So a write from a cache that's behind fails
instead of removing data that a client was told was saved. Right after a
takeover, a reconcile can fail this way. So can the first reconcile of a new
object, if something else writes the object while it runs. The framework
logs the failure at the info level, counts it in `kube_reconcile_total` with
`result="stale"` rather than as an error, and retries the reconcile, which
succeeds once the caches catch up. `kube.LastError` doesn't return such a
failure, so the retry sees the error from the reconcile before it. After five
failed reconciles of the object in a row, the framework logs each further one
as a warning. A cache catches up sooner, so something else, such as a webhook,
may be refusing the write with `409 Conflict`. Requiring the cached resource
version covers a hand-off, where the previous holder finishes its reconciles
before it releases the shard, but not a lost Lease. A replica that can't renew
its Lease lets running reconciles finish, and a late status write from one of
them can still remove data that a client was told was saved.

In the handler, where `unavailable` answers `503` and closes the connection
as in the previous example:

```go
pending.add(key, result)
defer pending.remove(key, result)
if !kube.Trigger[Report](r.Context(), ns, name) {
	unavailable(w)
	return
}
deadline := time.Now().Add(10 * time.Second)
for {
	rep := kube.Get[Report](r.Context(), ns, name)
	if rep != nil && slices.Contains(rep.Status.Results, result) {
		return
	}
	if time.Now().After(deadline) {
		unavailable(w)
		return
	}
	time.Sleep(100 * time.Millisecond)
}
```

In `Reconcile`:

```go
results := pending.get(key)
cur := kube.Get[Report](ctx, rep.Namespace, rep.Name)
if cur == nil {
	return nil
}
rep.Status.Results = cur.Status.Results
for _, result := range results {
	if !slices.Contains(rep.Status.Results, result) {
		rep.Status.Results = append(rep.Status.Results, result)
	}
}
```

## Keep state on disk

A program that keeps state on disk across restarts, such as copies of
repositories, declares a persistent volume with `kube.Volume`. Give the
program a flag for the directory, so it can run outside a cluster too:

```go
dir := flag.String("dir", "/var/lib/eventlog", "directory to keep copies of Events in")
kube.Main(
	kube.For[Event](&eventLog{dir: dir}),
	kube.Serve(api.handler()),
	kube.Volume("/var/lib/eventlog"),
)
```

`kube.Volume` does nothing while the program runs. The `generate` command
adds a `ReadWriteOnce` PersistentVolumeClaim to the installation and mounts
it at the directory. The claim asks for 1 GiB of the cluster's default
StorageClass unless you set `-volume-size` or `-storage-class`, which
`generate` refuses for a program without a volume. The kubelet makes the
volume writable by the program's non-root user with `fsGroup`. The directory
can't be one that the installation uses for something else, such as `/tmp`
or the directories under `/var/run/secrets` where the Pod's tokens are
mounted. In many images, `/var/run` is a symbolic link to `/run`, so
`kube.Volume` refuses the same directories under `/run/secrets` too.

A program with a volume runs one replica, without leader election, so its
reconciles and its `kube.Serve` handler are the only writers and can share
what's on disk. `generate` fails if you set `-replicas` or `-shards` above 1.
The Deployment uses the `Recreate` strategy, so a rollout stops the old Pod
before it starts the new one. The old Pod stops at once, without the
`preStop` sleep that [Serve an HTTP API](#serve-an-http-api) describes.
While the Pod restarts, nothing reconciles or serves, so clients of the
handler need to retry. Nothing answers the program's webhooks either. kube
registers admission webhooks with `failurePolicy: Fail`, so until the new
Pod is ready, the API server rejects the creates and updates that they
cover, and requests that need the program's conversion webhook fail.

A Pod that's deleted instead of rolled out, for example by
`kubectl delete pod` or a node drain, is replaced at once, and the old
process can keep running for up to 30 seconds, the Pod's termination grace
period. If the replacement runs on the same node, both processes can write
the volume, because Pods on one node can share a `ReadWriteOnce` volume. Both
can reconcile too, so a late status write from the old process can replace a
newer one from its replacement, as after a lost Lease (see
[Trigger a reconcile](#trigger-a-reconcile)). Keep writes safe for two
processes at once. To keep a file whole through a crash of the node, write a
new file, sync it, rename it over the old one, and sync the directory.

The volume also constrains the program:

- A `ReadWriteOnce` volume is usually in one zone, and a local volume, such
  as one of kind's default StorageClass, is on one node. The Pod can run only
  there, so while that zone or node is unavailable, the Pod stays `Pending`.
- The claim's StorageClass can't change after the claim is created, and its
  size can't change until the claim is bound. To grow a bound claim, its
  StorageClass must have `allowVolumeExpansion: true`. Then apply the
  installation again with a larger `-volume-size`. A claim can't shrink. For
  a smaller volume or another StorageClass, you need a new claim: copy the
  data to it yourself, or let the program start over with an empty volume.
- Deleting the installation, for example with `kubectl delete -f`, deletes
  the claim. The volume's reclaim policy, which comes from its StorageClass,
  decides what happens to the data. `Delete`, the default, deletes the
  volume and its data. `Retain` keeps the volume for you to reuse or delete.

To add a volume to a program that's already installed, apply the new
installation with `kubectl apply`, or delete the Deployment first.
Server-side apply can't switch the Deployment to the `Recreate` strategy,
because the API server keeps the `rollingUpdate` field that it defaulted.
`kubectl apply` doesn't delete the objects that the program needed for two
replicas, so delete them yourself. Delete the Role and RoleBinding only if
the new installation has no Role in the program's namespace. The program
keeps that Role, without the rules for leader election, if it also needs
other rules there, for example for its webhooks.

```sh
kubectl -n NAMESPACE delete --ignore-not-found poddisruptionbudget NAME
# Only if the new installation has no Role in NAMESPACE:
kubectl -n NAMESPACE delete --ignore-not-found role,rolebinding NAME
```

Replace `NAME` with the program's name in the installation, and `NAMESPACE`
with the namespace that you installed it in, which is `NAME` unless you set
`-namespace`.

[`examples/eventlog`](examples/eventlog/main.go) keeps a copy of every Event
in a volume, and serves the copies.

## Run a controller

`kube.Main` runs controllers with these flags:

- `-kubeconfig`: the kubeconfig file. Without it, kube uses `$KUBECONFIG`,
  then the pod's service account, then `$HOME/.kube/config`.
- `-watch-namespace`: watch only one namespace.
- `-leader-elect`: reconcile only while this replica holds a Lease.
- `-shards`: split reconciles across replicas into this many shards.
- `-webhook-service`: the Service, as `name` or `namespace/name`, through
  which the API server reaches the webhooks.
- `-webhook-url`: an `https` URL through which the API server reaches the
  webhooks of a program outside the cluster.
- `-webhook-addr`: where to serve webhooks. The default is `:9443`.
- `-serve-addr`: where to serve the handler passed to `kube.Serve`. The
  default is `:8081`.
- `-token-dir`: a directory of service account tokens for
  `kube.RequestToken`, each in a file named by the hex SHA-256 hash of its
  audience, as `generate` mounts them.
- `-metrics-addr`: serve `/healthz`, `/readyz`, and Prometheus `/metrics`,
  for example on `:8080`.
- `-log-level`: log messages at this level and above: `debug`, `info`,
  `warn`, or `error`. The default is `info`.

If the program defines one of these flags itself on `flag.CommandLine`,
`kube.Main` leaves out its own and logs a warning, and the manager doesn't
read that flag.

For more control, set the fields of a `kube.Manager` and call its `Main`
method. Each flag defaults to its field's value, and a Manager with a
`Logger` has no `-log-level`. `Setup`, if you set it, runs after `Main`
reads the flags and before the manager connects to the cluster, so the
program can check its own flags and stop at startup:

```go
zone := flag.String("zone", "", "DNS zone for the sites")
m := &kube.Manager{Name: "sites"}
m.Setup = func(context.Context) error {
	if *zone == "" {
		return errors.New("-zone is required")
	}
	return nil
}
m.Main(kube.For[Website](reconciler{}))
```

`generate` follows the Manager's `Name`, `Namespace`, `LeaseNamespace`,
`LeaderElection`, and `Shards`. To run controllers without flags, signal
handling, or `generate`, call the Manager's `Run` method. `kube.For` takes
options such as `kube.Workers(n)`, `kube.WatchSelector(selector)`, and
`kube.Resync(duration)`.

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
   including calls inside generic helpers, whether the program calls
   `ReviewToken`, and the audiences that it passes to `RequestToken`. Only a
   program that calls `Eventf` gets permission to write events. A `Fetch`
   that names its type, not a type parameter, and passes constants as the
   namespace and name gets permission to get only that object, if the
   type's `kube` tag says `scope=Namespaced` or `scope=Cluster`.
1. Builds the program for each platform with `CGO_ENABLED=0` and the build
   tags and linker flags that the program was built with.
1. Builds an image for each platform on `cgr.dev/chainguard/static`, with the
   program at `/app/PROGRAM` as the entrypoint. The image keeps the base's
   user, or runs as user 65532 if the base has none. It
   pushes the images and an index of them to `REGISTRY/NAME` with
   [go-containerregistry](https://github.com/google/go-containerregistry),
   using the credentials from `docker login` or `podman login`.
1. Writes YAML that installs the image by digest: a Namespace if
   `-namespace` is the default, a ServiceAccount, a ClusterRole and a Role
   with only the rules that the program needs, their bindings, a
   Deployment, a PodDisruptionBudget for more than one replica, a Service
   for webhooks and the `kube.Serve` handler, an empty Secret that the
   program keeps its webhook certificate in, and a PersistentVolumeClaim
   for a `kube.Volume`. With more than
   one replica, the Deployment runs the program with `-leader-elect`, or
   with `-shards` when you set `-shards`. The kubelet probes `/readyz` every
   second, so a new Pod becomes ready within a second of `/readyz` passing,
   and 30 failures in a row make a ready Pod unready. The container's root
   file system is read-only, with an `emptyDir` volume at `/tmp` for
   temporary files.
   `-tmp-size` limits the volume's size. The Pod runs the program as user
   and group 65532, whatever the base's user is, because the kubelet won't
   start a container that must run as non-root when the image's user is
   root or a name. The Pod shares one process
   namespace, so the pause container is PID 1 and reaps the processes that
   the program's subprocesses leave behind, which a Go program doesn't do.
   A container that you add to the Pod can see the program's processes and
   their arguments, and if it runs as the same user, their environment
   variables and files. A projected volume at
   `/var/run/secrets/tokens` holds a token for each constant audience that
   the program passes to `RequestToken`. The `KUBE_IMAGE` environment
   variable holds the image's reference by digest, so the program can start
   Pods that run its own image. A tool that changes the container's image,
   such as kustomize's `images` field or `kubectl set image`, has to change
   `KUBE_IMAGE` too.

The images have fixed timestamps, so the same source gives the same digest,
and running `generate` again without changes leaves the cluster as it was.
When the program starts in the cluster, it installs its own
CustomResourceDefinitions and webhook configurations.

The installation's objects are named `NAME`, which is the `Name` of the
program's `kube.Manager` or else the program's name, lowercased, with each
character other than a letter or digit changed to `-`. Objects
outside the program's namespace are named `NAME.NAMESPACE`, where
`NAMESPACE` is the namespace that you install the program in, so that an
installation in another namespace doesn't replace them: the ClusterRole and
its binding, Roles in other namespaces, and the webhook configurations that
the program installs. When you install in the namespace `NAME`, the default,
they're named `NAME` too.

The YAML creates the namespace only when it's `NAME`, so deleting an
installation in another namespace, for example with `kubectl delete -f`,
leaves that namespace and the other objects in it.

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
| `-namespace` | `NAME` | Namespace to install in, which must exist unless it's the default |
| `-replicas` | 2, or 1 with a `kube.Volume` | Pods to run |
| `-shards` | 1, or the Manager's `Shards` | Shards to split reconciles across |
| `-tag` | `latest` | Tag for the image, in addition to its digest |
| `-tmp-size` | No limit | Size limit of the `emptyDir` volume at `/tmp`, such as `1Gi` |
| `-volume-size` | `1Gi` | Size of the claim for a `kube.Volume` |
| `-storage-class` | The cluster's default | StorageClass of the claim for a `kube.Volume` |
| `-watch-namespace` | Every namespace, or the Manager's `Namespace` | Namespace for the program to watch; the rules for namespaced resources go in a Role there |

Flags after `--` go to the program in the Deployment:

```sh
go run ./examples/podpolicy generate -registry=ghcr.io/you -- -registries=ghcr.io/you/ |
  kubectl apply -f -
```

`generate` parses these flags as the program would, so it fails on a flag
that the program doesn't define, and the function that you pass to
[`kube.Install`](#install-other-objects) sees their values.

The Deployment sets some of `kube.Main`'s flags to match the RBAC rules,
ports, and probes that `generate` writes: `-metrics-addr`, `-leader-elect`,
`-shards`, `-watch-namespace`, `-webhook-addr`, `-webhook-service`,
`-serve-addr`, and `-token-dir`. `generate` fails when you pass one of these
after `--`, or when the program defines one itself. To watch one namespace
or to set the shards, use the `generate` flag of the same name.

go-containerregistry is kube's only dependency, and only `generate` uses it.
The command builds the copy of the program for the image with the program's
own build tags and linker flags, which come from the go command line or
`GOFLAGS`, so a version that `-ldflags=-X` sets reaches the image. It adds the
`kube_nogenerate` build tag, which leaves the command out, so the program in
the cluster links only kube and the standard library. It also adds `-s -w`,
which leave out the symbol table and debug information. The command finds
the program's calls with the same tags, so the rules cover the code in the
image. Go doesn't record the linker flags of a program built with
`-trimpath`, so for such a program `generate` takes them from `GOFLAGS`.

### Install other objects

A program can install objects that it needs but doesn't reconcile, such as
admission policies for its types, the way it installs its own
CustomResourceDefinitions. Embed a manifest in the program, and pass a
function that returns it to `kube.Install`:

```go
//go:embed policy.yaml
var policy []byte

func main() {
	installPolicy := flag.Bool("install-policy", true, "install policy.yaml when the program starts")
	kube.Main(
		kube.Install(func() []byte {
			if !*installPolicy {
				return nil
			}
			return policy
		}),
		kube.For[Website](reconciler{}),
	)
}
```

The manifest is YAML documents separated by `---` lines, without anchors,
aliases, or tags. Give each namespaced object its `metadata.namespace`, and
put each admission policy before its bindings.

When the program starts, after its controllers install their
CustomResourceDefinitions and before they reconcile, it applies the objects in
order with server-side apply and labels them with the program's name. It
applies them again each time it starts, but doesn't watch them. Server-side
apply sets only the fields in the manifest, so fields that others set keep
their values. Entries that others add to a list that merges by key or value,
such as a binding's `validationActions`, also stay. If the merged object isn't
valid, such as a binding whose `validationActions` would hold both `Deny` and
`Warn`, the apply fails and the program exits when it starts. The program
doesn't delete an object that a later manifest leaves out.

`generate` calls the function after it parses the flags after `--`, so
`-- -install-policy=false` leaves out the policy and the permissions to apply
it. For each object that the function returns, `generate` grants `create` and
`patch` on that object by name. A server-side apply names the object in its
request, so the API server checks `create` on that name, and the program
can't create or change other objects of the same type. For an object in a
namespace other than the program's own or the one that it watches,
`generate` writes a Role and a RoleBinding in that namespace, which must
exist before you apply the YAML.

An admission policy with a `paramKind` needs more permissions. The API server
lets you create the policy only if you can get every object of its
`paramKind`, which it checks as `get` on an object named `*`. When the
`paramKind` is ConfigMap or a custom type that the program defines, `generate`
grants `get` on the name `*`. Objects of those kinds can't have that name, so
the rule passes the check without letting the program read the parameters.
Objects of some other kinds, such as ClusterRoles, can have the name `*`, so
for any other `paramKind`, `generate` prints a warning, and you give the
program the permission yourself. For a binding with a `paramRef`, `generate`
grants `get` on the parameter object that the binding names.

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
It keeps serving webhooks and the `kube.Serve` handler, and `/readyz` reports
ready once they serve and the controllers it runs have synced, so the Service
sends requests to standby replicas too.

### Permissions

The `generate` command writes these rules. If you install the program another
way, its service account needs these permissions:

- `get`, `list`, and `watch` on every type that it reads. For `Fetch`, `get`
  on each object that it fetches is enough.
- `create`, `patch`, and `delete` on every type that it declares with `Own`,
  `Apply`, or `Delete`. Server-side apply needs `create` for objects that
  don't exist yet.
- `patch` on the reconciled type's `status` subresource, for status.
- `patch` on the reconciled type, for its finalizer and for migrations, when
  any of the following is true:
  - The reconciler has a `Finalize` method.
  - The controller has `kube.RemovesFinalizer()`.
  - The type has more than one version.
  - The program declares owned objects with `Own` or `kube.Owns`, and the
    type's `kube` tag doesn't say `scope=Cluster`.
- `patch` on the `status` subresource of every type with a status that it
  declares with `Apply`, unless no version of the program has set that
  status.
- `get`, `create`, and `patch` on `customresourcedefinitions`, and `patch` on
  `customresourcedefinitions/status`, for the CRDs of its own types, by name.
  To check and migrate objects when a type changes, it also needs `list` on
  its own types in every namespace.
- `create` on `customresourcedefinitions`, and `get` on their CRDs by name,
  for the types that it defines and owns without reconciling them, so that it
  can create their CRDs. Without `get`, it logs a warning and doesn't create
  them.
- `create` and `patch` on each object that `kube.Install` applies, by name.
  For an admission policy with a `paramKind`, it also needs `get` on the name
  `*` of that kind in every namespace, and for the policy's binding, `get` on
  the parameter object.
- `get`, `list`, `create`, `update`, and `delete` on `leases`, with
  `-leader-elect` or `-shards`.
- `create` and `patch` on `events` in the `events.k8s.io` group, for a program
  that calls `Eventf`, in the namespaces of the reconciled objects, or in
  `default` for cluster-scoped ones.
- `get` and `delete` on its `validatingwebhookconfigurations` and
  `mutatingwebhookconfigurations`, by name, so that it can delete one that an
  earlier version left.
- For webhooks, `get` and `update` on the Secret `NAME-webhook-tls` in its
  namespace, and `create` and `patch` on its validating webhook configuration
  when it validates objects, and on its mutating one when it defaults them.
  The YAML that `generate` writes creates the Secret empty, and the program
  fills it in. If the Secret doesn't exist, the program creates it, which
  needs `create` on `secrets`.
- `create` on `tokenreviews`, to check tokens with `ReviewToken`.
- `create` on `serviceaccounts/token` for its own service account, in its
  namespace, to request tokens with `RequestToken`. The `generate` command
  grants it only to a program that passes an audience that isn't a constant.
  For each constant audience, it mounts a projected token in `-token-dir`
  instead.

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
`k8s.Deployment` that you pass to `kube.Fake`. If you also pass an error,
`kube.LastError` returns it, as if the previous reconcile had failed with it.

`kube.Applied` returns each object with its status, which the framework
applies too. A status that `Apply` rejects for the reconciled object fails the
reconcile, as in a cluster, and the recorder's `Err` method returns the error.

`rec.Events()` returns the events that the reconciler recorded with
`Eventf`, in order, as `kube.Event` values with a type, a reason, and a note.

To test `Validate`, `Default`, `ConvertTo`, and `ConvertFrom`, call them
directly. With a context from `kube.Fake`, `Validate` and `Default` can read
objects with `Get` and `List`.

To test a `kube.Serve` handler, pass it a request with a context from
`kube.FakeRequest`, which gives the handler the scope that a request has in a
cluster. Pass it the objects that the handler reads and a `kube.FakeToken`
for each token that `ReviewToken` accepts. `kube.Triggered[T]` returns the
keys of the objects of `T`'s kind that `Trigger` queued, and `rec.Err`
returns the error from a call that a handler can't make, such as `Apply`.
With `kube.FakeStandby{}`, `Trigger` returns false, as on a replica that
doesn't hold the lease:

```go
ctx, rec := kube.FakeRequest(t.Context(), probe, kube.FakeToken{
	Token:     "ci",
	User:      kube.UserInfo{Username: "system:serviceaccount:team:ci"},
	Audiences: []string{"probe"},
})
req := httptest.NewRequest("POST", "/probes/team/api", nil).WithContext(ctx)
req.Header.Set("Authorization", "Bearer ci")
handler.ServeHTTP(httptest.NewRecorder(), req)
if got := kube.Triggered[Probe](rec); len(got) != 1 {
	t.Errorf("triggered %v, want the probe", got)
}
if err := rec.Err(); err != nil {
	t.Error(err)
}
```

Use a new context from `kube.FakeRequest` for each request, as each request
in a cluster has its own.

`RequestToken` returns the tokens `fake-token-1`, `fake-token-2`, and so on,
which `ReviewToken` accepts for the requested audience.

The fakes differ from a cluster in two ways:

- `Trigger` doesn't check that a controller in the program reconciles the
  object's kind, so it returns true for any object in the world unless the
  world holds `kube.FakeStandby{}`.
- Nothing that a reconcile in a `kube.Fake` context declares reaches the world
  of a `kube.FakeRequest` context, so a unit test can't follow data from a
  handler through a reconcile to the handler's next `Get`. Test the hand-off
  in [Trigger a reconcile](#trigger-a-reconcile) against a real API server, as
  `TestServeHandsDataToReconcile` in `e2e/serve_test.go` does.

The end-to-end tests run each example against a real `kube-apiserver` and
`etcd`, without a kubelet or controller manager. To run them, download the
binaries with the `fetch-envtest.sh` script:

```sh
export KUBEBUILDER_ASSETS="$(bash fetch-envtest.sh)"
go test -race ./...
```

Without `KUBEBUILDER_ASSETS`, the end-to-end tests skip. CI downloads the
binaries and runs them.

One more test installs the website, imagereport, janitor, probe, eventlog,
and podpolicy examples with `generate` in a [kind](https://kind.sigs.k8s.io/)
cluster, and pushes their images to a local registry. It needs Docker,
`kubectl`, and `curl`, and installs kind if it's missing:

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
| [`website`](examples/website/main.go) | Most operators | Owned Deployment and Service, pruning, status from an owned object, events |
| [`replicator`](examples/replicator/main.go) | emberstack/reflector, mittwald/kubernetes-replicator | Metadata-only cache, `Fetch`, owned objects in other namespaces |
| [`reloader`](examples/reloader/main.go) | stakater/Reloader | Dependency tracking through `Get`, `Apply` on someone else's object |
| [`dnsrecord`](examples/dnsrecord/main.go) | external-dns, Crossplane | External resources, `Finalize`, `Permanent`, drift checks |
| [`janitor`](examples/janitor/main.go) | hjacobs/kube-janitor | Time-based desired state with `RequeueAfter`, `Delete` |
| [`podpolicy`](examples/podpolicy/main.go) | Kyverno and OPA Gatekeeper policies | Admission webhooks for Pods with `kube.Webhooks`, a patch that keeps undeclared fields |
| [`imagereport`](examples/imagereport/main.go) | aquasecurity/trivy-operator | Creating the CRD of a type that it owns but doesn't reconcile, `kube.Owns` |
| [`probe`](examples/probe/main.go) | Prometheus Blackbox Exporter | An HTTP API on every replica with `kube.Serve`, `ReviewToken`, `RequestToken`, and `Trigger` |
| [`eventlog`](examples/eventlog/main.go) | resmoio/kubernetes-event-exporter | State on disk with `kube.Volume`, one replica that writes it, a `kube.Serve` handler that reads it |

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
  contains a type parameter, such as `Item[T]`. When it can't tell which
  types a call passes to a `kube` function, directly or through the
  program's own generic helpers, it prints a warning at that call, and you
  add the permissions for those types yourself. Such a call that reaches
  `kube.Own` still counts as declaring owned objects, so the program gets
  `patch` on the namespaced types that it reconciles.
- `generate` mounts a token only for an audience that the call of
  `RequestToken` passes as a constant. An audience that reaches the call
  through a variable or a function's parameter gets the permission to
  request tokens instead.
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
- Events are only about the reconciled object. The count of an event's
  repeats reaches the API server up to 6 minutes late, and a replica that
  crashes loses the counts that it hasn't written. A replica that stops
  loses the events and counts that it can't write in 5 seconds.
- In these cases, a write by the framework appears only when the watch
  delivers it, and a reconcile that runs before then reads the older version:
  - The write overlaps a list of the cache's objects. The cache lists when
    it starts and when its watch's resource version expires.
  - The framework makes another write to the same object at the same time.
  - The write uses one version of a type, and the cache reads another.
  - The cache's label selector uses `<` or `>`.
- A cache with a label selector hides an object that the framework deleted,
  or changed to stop matching, until the watch removes the object. If other
  clients' earlier changes take the object out of the selector and back in,
  the cache returns the older version that they put back until the watch
  delivers the framework's write.
- If the watch doesn't deliver a write by the framework within a minute, the
  cache returns the older version until it does. The limit is for an API
  server whose watch doesn't deliver the resource version that a write's
  response carries. With such a server, caches miss other clients' changes
  to the written object for that minute, and return the object even after
  it's deleted.
- Fields that `Apply` wrote, including status fields, stay on an object when
  a reconcile stops calling `Apply` for it, and when the reconciled object is
  deleted.
- `generate` can't tell which namespace an owned object goes in, so a program
  that declares owned objects gets `patch` on every namespaced type that it
  reconciles, even when each owned object is in its owner's namespace and
  needs no finalizer.
- `kube.Trigger` queues a reconcile only on the replica that reconciles the
  object. It doesn't send the request to that replica.
- `kube.Serve` serves plain HTTP, without TLS.
- A program with a `kube.Volume` runs one replica, and is down while it
  restarts, webhooks included. Adding a volume to an installed program takes
  `kubectl apply` rather than server-side apply, and leaves objects for you
  to delete, as [Keep state on disk](#keep-state-on-disk) describes.

## Layout

| Path | Contents |
| --- | --- |
| `*.go` | The `kube` package: types, caches, dependency tracking, controllers, status, events, webhooks, HTTP APIs, tokens, triggers, other objects to install, volumes, versions, shards, metrics, and fakes |
| `k8s/` | Types for common built-in objects |
| `examples/` | Example controllers and webhooks with unit and end-to-end tests |
| `e2e/` | End-to-end tests of the framework: shards and leader election, webhooks, versions, protobuf, steady-state writes, reads of a controller's own writes, shared status, status that `Apply` writes, changes that types can't see, panics, permanent errors, `LastError`, events, HTTP handlers and the data that they hand to reconciles, tokens, `Install`, volumes, and `generate`; `e2e/kind/` installs the examples in a kind cluster |
| `internal/client/` | REST client, kubeconfig, authentication, discovery, and JSON and protobuf watch decoding |
| `internal/protobuf/` | Protobuf decoding of built-in types into partial structs, and its schema; `gen/` is the separate module that generates the schema |
| `internal/certs/` | Certificate authority and serving certificates for webhooks |
| `internal/jsonpatch/` | JSON patches for mutating webhooks |
| `internal/queue/` | Prioritized, deduplicating work queue |
| `internal/schema/` | OpenAPI schemas and CustomResourceDefinitions from Go types |
| `internal/clone/` | Deep copy of any Go value, compiled once per type |
| `internal/subset/` | Checks whether one JSON document's fields are a subset of another's |
| `internal/yaml/` | The YAML subset that kubeconfig files use, and the YAML that `generate` writes |
| `internal/analysis/` | Type-checks a program to find the types that it passes to kube's generic functions, its calls to `Eventf` and `ReviewToken`, and the audiences that it passes to `RequestToken`, for `generate`'s RBAC rules and token volumes |
| `internal/image/` | Builds and pushes images with go-containerregistry, for `generate` |
| `internal/envtest/`, `internal/e2e/` | Start `etcd` and `kube-apiserver` for tests |
| `bench/` | Benchmark against `client-go` and `controller-runtime`, in its own module |

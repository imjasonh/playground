# kube design

This document explains why kube exists and how it works. It covers the
controller pattern that kube implements, problems that people report with the
standard Go libraries for writing controllers, earlier projects that solved
some of them, kube's design, and measurements. To learn how to use kube, see
the [README](../README.md).

- [The controller pattern](#the-controller-pattern)
- [What's hard with existing frameworks](#whats-hard-with-existing-frameworks)
- [Prior art](#prior-art)
- [Goals](#goals)
- [Design](#design)
- [Measurements](#measurements)
- [Limitations and future work](#limitations-and-future-work)

## The controller pattern

A Kubernetes controller makes the real state of a system match a desired state
that someone wrote down. A person creates an object, for example a Deployment,
whose `spec` is the desired state. A controller reads the object, compares it
with the real state, and acts on the difference, for example by creating Pods,
calling a cloud API, or changing other objects. It reports what it observed in
the object's `status`.

Controllers are level-triggered. Each pass looks at the whole current state,
not at the event that caused the pass, so a missed or repeated event doesn't
leave the system wrong. A pass that finds the state already right does
nothing.

Controllers built on `client-go` share one structure:

1. An informer lists every object of a type, then watches for changes,
   starting from the resource version that the list returned. It keeps the
   objects in an in-memory cache. When a watch ends, the informer resumes from
   the last resource version it saw. Bookmark events advance that version
   without changing an object. If the version is too old, the API server
   answers `410 Gone`, and the informer lists again.
1. Event handlers turn each added, changed, or deleted object into a key,
   `namespace/name`, and add it to a work queue. The queue holds each key once,
   however many times it's added, and never hands one key to two workers at
   the same time.
1. Workers take keys from the queue and call a reconcile function. Reconcile
   reads from the cache and writes to the API server. If it returns an error,
   the key goes back in the queue with exponential backoff.

Several API server features shape how controllers write:

- Optimistic concurrency. An update carries the object's `resourceVersion`,
  and the API server rejects it with `409 Conflict` if the object changed
  since. A controller that reads from a cache and then updates conflicts
  whenever the cache is behind.
- Server-side apply. A client sends only the fields it wants to set, under a
  field manager name. The API server merges them, records which manager owns
  each field, and removes fields that a manager stops sending. The Kubernetes
  documentation recommends it for controllers, and says that "it is strongly
  recommended for controllers to always force conflicts on objects that they
  own and manage" ([Server-Side Apply](https://kubernetes.io/docs/reference/using-api/server-side-apply/#using-server-side-apply-in-a-controller)).
- Owner references. An object can name its owner, and the garbage collector
  deletes owned objects after their owner. An owner reference can't point
  across namespaces, and a namespaced object can't own a cluster-scoped one.
- Finalizers. A finalizer turns an object's deletion into an update that sets
  `deletionTimestamp`. The object stays until every finalizer is removed,
  which gives a controller time to clean up outside Kubernetes
  ([Finalizers](https://kubernetes.io/docs/concepts/overview/working-with-objects/finalizers/)).
- Status conventions. `status.observedGeneration` records which
  `metadata.generation` of the spec the status describes, and
  `status.conditions` reports aspects of the state, such as `Ready`, in a
  standard form.
- Leases. Replicas of a controller take turns holding a Lease object, and
  only the holder runs controllers.
- Streaming lists. A list of a large collection can make the API server
  allocate about five times the size of the response, and a few lists at once
  can exhaust its memory ([KEP-3157](https://github.com/kubernetes/enhancements/issues/3157)).
  Instead, a client can open a watch with `sendInitialEvents=true`. The server
  sends every existing object as an `ADDED` event, then a bookmark with the
  `k8s.io/initial-events-end` annotation, then changes
  ([Streaming lists](https://kubernetes.io/docs/reference/using-api/api-concepts/#streaming-lists)).

## What's hard with existing frameworks

Most Go controllers use [`controller-runtime`](https://github.com/kubernetes-sigs/controller-runtime)
on top of `client-go`, often scaffolded by [Kubebuilder](https://book.kubebuilder.io/).
These libraries run a large part of the Kubernetes ecosystem. The problems in
this section come from their documentation, design documents, and release
notes, from Kubernetes enhancement proposals, and from measuring them.

### Dependencies and binary size

A `controller-runtime` controller depends on `client-go`, `apimachinery`,
`k8s.io/api`, and what they depend on. A minimal controller that owns one
Service for each Deployment, [`bench/crsize`](../bench/crsize/main.go), builds
from 61 modules into a 30.6 MiB stripped binary. Each `controller-runtime`
minor version requires one Kubernetes minor version of those modules, and the
v0.22 release notes list "Update to k8s.io/* v1.34 dependencies" as a breaking
change ([v0.22.0](https://github.com/kubernetes-sigs/controller-runtime/releases/tag/v0.22.0)).
A program that imports two libraries built against different Kubernetes
versions gets one version of each module, and can fail to build until the
libraries agree.

### Breaking changes

`controller-runtime` hasn't reached version 1. The release notes for v0.15
through v0.25 list 69 breaking changes. v0.15 had 20 of them, and its
maintainers called it "probably the largest in the history of the project"
([v0.15.0](https://github.com/kubernetes-sigs/controller-runtime/releases/tag/v0.15.0)).
An upgrade can require changes in every controller.

### Boilerplate and generated code

A Kubebuilder project starts with a `Makefile`, a `PROJECT` file, and
Kustomize configuration under `config/`
([What's in a basic project?](https://book.kubebuilder.io/cronjob-tutorial/basic-project.html)).
Each API version adds a `groupversion_info.go` file that registers types in a
scheme, and each type needs generated deep-copy methods in
`zz_generated.deepcopy.go`. Every object must implement `runtime.Object`, and
"the core of the `runtime.Object` interface is a deep-copy method,
`DeepCopyObject`"
([What's the rest of this stuff?](https://book.kubebuilder.io/cronjob-tutorial/other-api-files.html)).
`controller-gen` generates CRDs, RBAC rules, and webhook configuration from
comment markers, and the output must be regenerated and committed whenever a
type changes.

### Memory

An informer caches every object of its type in full, including
`metadata.managedFields`, the server-side apply bookkeeping that controllers
rarely read. In the [benchmark](#measurements), a `client-go` informer uses
14,687 bytes of heap for each Pod, whose JSON is 8.2 KB, and 10,894 bytes with
`managedFields` removed.

`controller-runtime` can cache less, but each way to do it is opt-in and
changes code. Transform functions, such as `cache.TransformStripManagedFields`
and `cache.Options.DefaultTransform`, edit objects before they're stored.
Metadata-only watches need a different type, `PartialObjectMetadata`, and a
different builder call, `WatchesMetadata`, added in v0.15. Label and field
selectors are set per type in the cache options, and the design document for
them warns that requests for objects outside the filter "will never return
anything"
([Filter cache ListWatch using selectors](https://github.com/kubernetes-sigs/controller-runtime/blob/main/designs/use-selectors-at-cache.md)).

### Watching related objects

When a reconcile reads objects of another type, the controller must also
watch that type and map each change back to the objects that read it. In
`controller-runtime`, that's a `Watches` call with
`handler.EnqueueRequestsFromMapFunc`, and usually a field index,
`FieldIndexer.IndexField`, so that the map function can find dependents
without scanning the cache. The reconcile logic and the watch setup are
written separately, and nothing checks that they agree. A missing or wrong
mapping shows up as a controller that reacts at the next resync instead of at
once. The [`reloader`](../examples/reloader/main.go) example needs all three
pieces in `controller-runtime`.

### Read-modify-write

A reconcile that reads an object from the cache, changes it, and updates it
gets a conflict whenever the cache is behind, and can overwrite fields that
another client set since the cache saw them. Server-side apply avoids both.
`controller-runtime`'s client gained native server-side apply in v0.22
([v0.22.0](https://github.com/kubernetes-sigs/controller-runtime/releases/tag/v0.22.0)).
Applying the standard Go types has its own trap. A struct with every field of
a type includes "zero valued required fields" in the request, "resulting in
fields being accidentally set to incorrect values and/or fields accidentally
being claimed as owned"
([KEP-2155](https://github.com/kubernetes/enhancements/issues/2155)). The KEP's
fix is a second generated type, an apply configuration, for every API type.

### Stale caches

"Every controller operates on a local cache that is populated by watching for
changes from the apiserver. By its nature, this watch stream is eventually
consistent and provides no guarantee of how far behind the 'live' state of the
apiserver it is" ([KEP-5647](https://github.com/kubernetes/enhancements/issues/5647)).
A stale cache causes two kinds of mistakes. A reconcile that runs right after
its own write can read the old object and act again. And a write based on a
stale cache can target an object that no longer exists. Server-side apply
creates objects that don't exist, so applying a finalizer to an object that
was deleted a moment ago creates it again, and a status write meant for a
deleted object can land on a new object with the same name.

### Startup and resync storms

A controller reconciles every object when it starts, and some reconcile
everything periodically. "In both these cases, the reconciliation of new or
changed objects gets delayed, resulting in poor user experience"
([Priority Queue](https://github.com/kubernetes-sigs/controller-runtime/blob/main/designs/priorityqueue.md)).
`controller-runtime` added a priority queue for this and enabled it by default
in v0.23 ([v0.23.0](https://github.com/kubernetes-sigs/controller-runtime/releases/tag/v0.23.0)).

### Testing

`controller-runtime` offers a fake client and envtest. The fake client
reimplements API server behavior in memory, and its release notes show how
hard that is to get right. v0.22 added server-side apply support to it and
changed how it handles `TypeMeta` and pointer `ObjectMeta`, all as breaking
changes, and fixes to its apply behavior continue in v0.23 and v0.24. envtest
runs a real `kube-apiserver` and `etcd`, which behaves correctly but needs
those binaries and a few seconds to start.

### One active replica

With leader election, one replica does all the work and the others wait.
"Typically, Kubernetes controllers use a leader election mechanism to
determine a single active controller instance"
([kubernetes-controller-sharding](https://github.com/timebertt/kubernetes-controller-sharding)),
and that project shards objects across replicas to remove the limit. It
assigns each object to a replica by labeling it, with a separate sharder
component. Knative's [`leaderelection`](https://github.com/knative/pkg/tree/main/leaderelection)
package instead splits each controller's keys into buckets and runs a leader
election for each bucket, so no object needs a label.

### Webhooks

Admission and conversion webhooks are HTTPS servers that the API server
calls, so they need a serving certificate whose CA bundle is in each webhook
configuration and CustomResourceDefinition. Kubebuilder projects get both
from [cert-manager](https://book.kubebuilder.io/cronjob-tutorial/cert-manager),
whose [CA injector](https://cert-manager.io/docs/concepts/ca-injector/) copies
the bundle into those objects, which is another component to install and keep
running. For conversion, Kubebuilder uses a
[hub-and-spoke model](https://book.kubebuilder.io/multiversion-tutorial/conversion-concepts):
one version is the hub, and each other version converts to and from it, so
adding a version doesn't mean writing a conversion for every pair.

### Upgrading custom resource definitions

Changing a CRD's stored version doesn't rewrite the objects already in etcd.
The [Kubernetes v1.37 storage version migration
announcement](https://kubernetes.io/blog/2026/08/31/kubernetes-v1-37-storage-version-migration-ga/)
puts it this way: "You cannot safely remove `v1alpha1` from the CRD's
`.status.storedVersions` or drop serving support until every single resource
in storage has been re-written." Version 1.37 makes the StorageVersionMigration
API and its controller in `kube-controller-manager` generally available. A
migration is an object that someone creates, and its controller updates
`status.storedVersions` only "if the generation of the CRD has not been
updated during the migration"
([KEP-4192](https://www.kubernetes.dev/resources/keps/4192/)).

Removing a version takes more than that. "Kubernetes stores field ownership
information by apiVersion in managedFields. Unfortunately, there is no builtin
logic that removes managedFields of an apiVersion when that apiVersion is
removed from the CRD. If there are still managedFields with a removed
apiVersion any subsequent apply requests will fail"
([cluster-api#11894](https://github.com/kubernetes-sigs/cluster-api/issues/11894)).
The bug, [kubernetes#111937](https://github.com/kubernetes/kubernetes/issues/111937),
is open. Cluster API's answer is a
[CRD migrator](https://github.com/kubernetes-sigs/cluster-api/tree/main/controllers/crdmigrator)
that each controller runs. It applies a no-op patch with the object's resource
version to every object when `status.storedVersions` isn't just the storage
version, optionally through the status subresource "to avoid mutating &
validation webhook errors". It then updates `status.storedVersions` with
optimistic locking, and removes `managedFields` entries for versions that
aren't served. Cluster API keeps a retired version in the CRD as
`served: false` for several releases so that the cleanup runs before the
version goes. Since [kubernetes#130704](https://github.com/kubernetes/kubernetes/pull/130704)
in Kubernetes 1.35, the API server doesn't watch or convert versions that are
neither served nor stored, so keeping them costs nothing.

Changes inside a version have their own risks.
[OLM v1](https://operator-framework.github.io/operator-controller/concepts/crd-upgrade-safety/)
blocks CRD upgrades that remove a field or a stored version, change a field's
type, add a required field, change defaults, or narrow enums and bounds.
[Validation ratcheting](https://kubernetes.io/docs/tasks/extend-kubernetes/custom-resources/custom-resource-definitions/#validation-ratcheting),
generally available since 1.33, accepts updates that leave invalid values
unchanged, but "Errors arising from changing the list of required fields will
not be ratcheted."

## Prior art

Other projects solved parts of these problems, and kube borrows from them.

[kube-rs](https://github.com/kube-rs/kube) is a Kubernetes client and
controller runtime in Rust that doesn't follow `client-go`'s design. Its
`CustomResource` derive macro generates a CRD from a Rust struct, and its
`Api<K>` type works with any type that implements its `Resource` trait. kube's
`kube:"group=..."` tag and generic functions apply the same idea in Go, with
struct tags and reflection instead of macros. kube-rs also has metadata-only
watches and a finalizer helper.

[krt](https://github.com/istio/istio/tree/master/pkg/kube/krt), Istio's
declarative controller runtime, builds collections from transformation
functions. A transformation reads other collections with `krt.Fetch`, and "if
the result of the `Fetch` operation changes, the collection will automatically
be recomputed." kube applies this to reconcile functions. `Get` and `List`
record what a reconcile read, and a change to any of it runs the reconcile
again. krt's README also notes that its requirements on objects "are not
expressed as generic constraints due to limitations in Go's type system."
kube's `Resource[T]` constraint, `interface{ *T; unexported methods }`, works
around one of these limitations. Any struct that embeds `kube.Object`
satisfies it, and Go infers it from `T`.

[Metacontroller](https://metacontroller.github.io/metacontroller/api/compositecontroller.html)'s
CompositeController sends a parent object and its children to a sync hook,
which returns the children it wants. Metacontroller creates and updates them,
and deletes children that the hook stops returning. kube's `Own` is the same
contract inside the process, with typed objects and no HTTP round trip.

[Knative's generated reconcilers](https://github.com/knative/pkg/blob/main/injection/README.md)
call a typed `ReconcileKind(ctx, obj)` method, and handle status updates and
retries. "Implementing `FinalizeKind` will result in the reconciler using
finalizers on the resource." kube's optional `Finalize` method works the same
way, without code generation. In Knative, watches are still set up by hand.

[Crossplane managed resources](https://docs.crossplane.io/latest/managed-resources/managed-resources/)
manage cloud resources by observing the external resource, then creating,
updating, or deleting it, under management policies such as `Observe` and
`Delete`. The [`dnsrecord`](../examples/dnsrecord/main.go) example follows the
same observe-then-act shape for a DNS provider.

[kro](https://github.com/kubernetes-sigs/kro) defines groups of resources and
their dependencies in a ResourceGraphDefinition, without Go code. It suits
compositions of existing resources, not controllers that call outside systems.

kube's work queue follows `controller-runtime`'s priority queue, with two
priority levels so that the initial list and resyncs don't delay reaction to
changes.

## Goals

kube is an experiment in what a controller runtime looks like when it starts
from server-side apply, streaming lists, and Go generics, which `client-go`
predates. Its goals:

- A controller is one struct for the type and one method. The developer
  doesn't write a scheme, deep-copy code, CRD manifests, watch setup, map
  functions, or indexes.
- `Reconcile` reads the real state and declares the desired state. It doesn't
  create, update, or delete objects in Kubernetes directly.
- The framework does the bookkeeping that every controller needs: status,
  `observedGeneration`, conditions, finalizers, owner references, pruning,
  retries, and leader election.
- Caches hold only what controllers read, by default.
- A converged controller makes no writes, including after a restart.
- No dependencies beyond the Go standard library in the program that runs in
  the cluster.
- `Reconcile` is testable without a cluster, a fake client, or a mock.

## Design

### Types are projections

Any struct that embeds `kube.Object` is a Kubernetes type. Reflection over the
struct, done once per type, finds its `apiVersion`, `kind`, and scope, and
where its `status`, `status.observedGeneration`, and `status.conditions` are.
A `kube:"group=..."` tag marks a type that the program defines, and the
framework generates its CRD. A `kube:"apiVersion=...,kind=..."` tag marks a
type that already exists. A struct that declares no fields besides
`kube.Object` is metadata-only.

A struct needn't declare every field of its kind. `encoding/json` skips
fields that a struct doesn't declare, so the cache decodes and stores only
declared fields. `managedFields` isn't declared, so it's never stored. For a
metadata-only type, the informer asks the API server for
`PartialObjectMetadata`, and the server sends no spec, status, or data.

Writing with a partial type is safe because every write is a server-side apply
of the fields that the struct sets. The framework never sends a whole object
in an update, so it can't clear fields that the struct omits. This also makes
each type its own apply configuration, which avoids the trap in KEP-2155. The
types in the [`k8s`](../k8s/k8s.go) package make optional fields pointers or
`omitempty`, so a desired object sets only the fields you assign.

The cache interns strings that repeat across objects, such as namespaces,
label keys and values, annotation keys, owner kinds, and finalizers, with
Go's `unique` package. For the benchmark's Pods, interning saves 286 bytes per
Pod, about 5%.

`Get` and `List` return copies, so a reconcile can change what it reads. The
`internal/clone` package deep-copies any Go value with a copier that it builds
once per type with reflection, instead of generated `DeepCopy` methods.

### Caches and watches

A manager keeps one informer for each type, namespace, and label selector that
its controllers use, and controllers that read the same type with the same
filters share it. An informer starts the first time a reconcile reads its
type. On a replica with leader election or shards, informers start only after
the replica first holds a shard, so standby replicas hold no caches.

The informer first tries a streaming list, which is a watch with
`sendInitialEvents=true`, `resourceVersionMatch=NotOlderThan`, and
`allowWatchBookmarks=true`. When the `initial-events-end` bookmark arrives, it
replaces the cache's contents in one step, then keeps reading the same watch.
If the server rejects the parameters with `400` or `422`, or sends nothing for
15 seconds, the informer switches to paginated lists of 500 objects and
watches from the list's resource version. Watches ask for a random timeout
between 5 and 10 minutes so that reconnects spread out, and resume from the
last resource version they saw. A `410 Gone` starts a new list. Replacing the
cache's contents computes which objects were added, changed, or deleted while
the informer was disconnected, and notifies controllers of exactly those.

For built-in types, the informer asks for protobuf, as the
[Protobuf](#protobuf) section describes. For custom types, a watch is a stream
of JSON events, each `{"type":"ADDED","object":{...}}`. Decoding each event
into a struct with a `json.RawMessage` field and then decoding the object
costs two passes over the bytes. The informer instead
scans each event's boundaries with a byte scanner at about 500 MB/s, reads
the type from the event's prefix, and decodes the object straight into `T`.
That uses 30% less CPU and allocates a third fewer bytes than decoding twice.
A field whose JSON type doesn't match its Go type doesn't stop the watch. The
rest of the object decodes, and the informer logs the mismatch once.

A controller's `kube.WatchNamespace` and `kube.WatchSelector` options, and the
manager's `Namespace` field, become query parameters, so the API server
filters objects before sending them.

Go's HTTP transport asks for gzip by default. For a controller in the
cluster, compression costs the API server CPU on every list and saves
bandwidth that's rarely scarce, so kube turns it off. `Manager.Compression`
turns it back on.

### Dependency tracking

Each reconcile runs with a scope that records what it reads. `Get` records the
type, namespace, and name, whether or not the object exists, so creating a
missing object runs the reconcile again. `List` records the type, namespace,
and label selector. After the reconcile, the framework replaces the
reconcile's previous dependencies with the new ones, so a reconcile that stops
reading an object stops depending on it.

An informer passes on a change only if it changes a field that the informer's
type declares. Every change has a new `metadata.resourceVersion`, and one that
changes only that, or only fields that the type doesn't declare, can't change
what a reconcile reads. So declaring fewer fields means fewer reconciles, as
well as less memory. Metadata-only types can't see the fields that matter, so
for them every new resource version counts.

When an informer passes on a change, the framework finds the reconciles that
read the object by name, and the reconciles whose lists match the object's old
or new labels. Matching either catches objects that start or stop matching a
selector. Those reconciles go back in the queue. The
`kube_tracked_dependencies` metric counts the recorded dependencies.

Owned objects carry their owner in a label and an annotation, and each type's
cache indexes objects by owner. A change to an owned object, including to its
status, runs its owner's reconcile again. A change to the reconciled object
runs its reconcile only when a declared field other than `status` changed, or
someone else changed the status, so the controller's own status writes don't
cause another reconcile.

### The work queue

The queue in `internal/queue` holds each key once, never gives one key to two
workers at the same time, and processes a key again after its current
processing if it was added meanwhile. Keys have one of two priorities. Changes
are high priority. The initial list and periodic resyncs, every 10 hours by
default, are low priority, so a restart with thousands of objects doesn't
delay reaction to a change. Failed keys back off exponentially from 50 ms to
5 minutes, with up to 10% random jitter, and `RequeueAfter` schedules a key on
a timer heap. The queue's tests use `testing/synctest`, so they check timing
without sleeping.

### Reconcile and intents

The framework calls `Reconcile` with a copy of the cached object. `Own`,
`Apply`, and `Delete` don't write. They record intents in the scope. If
`Reconcile` returns `nil`, the framework carries out the intents in order.

For `Own` and `Apply`, the framework builds an apply document from the desired
object and sends it with server-side apply, forcing conflicts. The field
manager is the controller's name for `Own`, and a name derived from the
reconciled object for `Apply`, so two objects that apply fields to the same
target don't remove each other's fields. An owned object's document also gets
the owner label and annotation and, when Kubernetes allows it, an owner
reference.

A reconcile can pass an object to `Own` or `Apply` only once, and the
framework compares the objects by group, kind, and key, not by Go type.
Server-side apply takes each request as the field manager's whole intent, so
if two declarations of one object shared a manager, the second request would
remove the fields that only the first sent. For example, a type that sets a
label, followed by a type that declares only the status, would remove the
label. Declaring an object with both `Own` and `Apply` fails too, because
`Apply` is for objects that the reconciled object doesn't own. The error also
says that `Own` doesn't apply a status, so that a program doesn't move the
status into the `Own` declaration and lose it unnoticed.

The framework skips an apply when the cached object already has every field
of the document. That alone isn't enough, because server-side apply removes
fields that a manager stops sending, and a desired object that drops a field
still matches a cached object that has it. So an owned object's document
carries an annotation with a hash of the rest of the document. If the cached
object has every field including that annotation, the last apply sent this
same document, and there's nothing to add or remove. Because the hash lives on
the object, the skip works after a restart or a leader failover. For `Apply`,
the framework doesn't annotate objects it doesn't own. Instead, it records in
memory the documents that the last successful reconcile of each object
applied, and skips only when the record holds the same document. A reconcile
whose writes fail may already have applied documents that the record doesn't
hold, so the framework drops the record, and the next reconcile sends every
document. The `kube_apply_total` metric counts applies by result, `applied` or
`skipped`.

For a kind with a status subresource, server-side apply tracks the status
fields apart from the object's other fields, and a request to the object
itself ignores the status. So when the type passed to `Apply` has a status,
the framework sends a second document to the status subresource, with the
same field manager, that holds the object's name, namespace, UID, and status.
It sends the status after the first request succeeds or is skipped, and not
at all when the first request fails. When the status request fails, the
reconcile fails and is retried, and the first request's fields stay. A status
request is skipped by the same rule as the first request, and counts in
`kube_apply_total` the same way.

An empty status goes without a `status` field, so the manager gives up every
status field that it owns, and the API server removes each one that no other
manager owns. So an empty status needs a request only while the manager owns
status fields. The API server keeps a `managedFields` entry for a manager and
subresource only while the manager owns fields there. When the framework sends
the first request, it sends an empty status only if the response has an entry
for the manager and the status subresource. The framework records a status
that isn't empty along with each document, so when it skips the first request,
it sends an empty status only if the record holds a status. A program that
never sets a status sends no status requests, and one that clears a status
sends one, even after a restart or a failed reconcile.

An earlier version of a program can leave status fields to give up, even when
the current one sets only a label on a type with a status, such as
`k8s.Deployment`. So `generate` grants `patch` on the status subresource for
each type with a status that a program applies. With hand-written rules that
leave that out, the program works until it has status fields to give up.
Then the reconcile fails with `403 Forbidden`, and the fields stay until the
controller gets the permission. Skipping a forbidden empty status instead
would report success while the fields stay.

A request to a subresource that the API server doesn't serve fails with the
same `404 Not Found` as a request for an object that was deleted, so before it
sends a status, the framework checks discovery for the status subresource.
Without one, the framework skips an empty status and fails the reconcile for
any other. Such a kind either has no status, as with ConfigMaps, or is a
custom resource whose definition keeps the status with the other fields. The
framework doesn't put the status in the first request instead, because the
API server rejects a document with a field that the kind doesn't declare, so
for a kind without a status, the rest of the object wouldn't be applied
either.

The client caches discovery results and fetches them again when they don't
list the subresource, so it finds one that a CRD gains. When a status request
fails with `404`, the framework drops the cached results for the kind's API
version, so the next status request finds out whether the kind lost the
subresource. The client doesn't remember a missing subresource, because that
would hide one that a CRD gains later. So for such a kind, a status that
isn't empty costs a discovery request on each retry, and an empty status
costs one only when the manager owns status fields, as after a CRD drops its
status subresource.

The framework writes the reconciled object's status with the controller's
name as the field manager. If `Apply` wrote it too, under the name derived
from the reconciled object, both managers would own every field that both
send, and neither could remove one alone. So when the reconciled type has a
status, `Apply` fails the reconcile when it's given a status for the
reconciled object, and ignores an empty one. A reconciled type without a
status, such as a view of another controller's type, can apply the status of
its own object.

After the intents, the framework deletes owned objects that the reconcile
didn't declare. It finds them in the owner index of each owned type's cache.

Every write that targets an object that must already exist carries its UID:
status writes, finalizer changes, `Apply`, and deletes. An apply with a UID
fails instead of creating an object, and a delete with a UID precondition
fails if the name now belongs to a new object. A write based on a stale cache
can't bring back a deleted object or touch its replacement.

`Reconcile` can change the reconciled object's status. After every reconcile,
whether it succeeded or not, the framework sets `observedGeneration` and a
`Synced` condition if the status has those fields, compares the status with
the cached one, and writes it with server-side apply only if it differs.
`Synced` reports the reconcile's error, cut to its first line and 1,024
characters. `kube.SetCondition` keeps `lastTransitionTime` when a condition's
status doesn't change, so a reconcile that observes the same state writes
nothing.

Several managers can write one status, each to its own fields. A status
write manages every field it sends, so a reconcile that reads a field that
another manager writes clears it before returning, and the status then never
equals the cached one. The framework skips such a write by the same rule as for
`Apply`. If the cached status has every field of the new one, and the
controller's last status write sent the same status, there's nothing to add
or remove. Server-side apply ignores annotations sent to the status
subresource, so the record of the last write is in memory.

A reconcile that returns an error is retried with backoff, and its intents are
discarded. An error wrapped with `kube.Permanent` isn't retried; the object
waits for its next change, and `Synced` has the reason `PermanentError`. A
panic in `Reconcile` becomes an error, so one bad object doesn't stop the
controller.

### Finalizers and cleanup

When a reconciler has a `Finalize` method, the framework adds a finalizer to
each object before its first reconcile, with server-side apply under its own
field manager. When the object is deleted, the framework calls `Finalize`
instead of `Reconcile`, and removes the finalizer when `Finalize` returns
`nil`. Removal is a JSON patch that tests the finalizer's position in the list
before removing it, so a concurrent change to the list fails the patch instead
of removing the wrong entry.

Owner references can't point across namespaces or from a namespaced object to
a cluster-scoped one. When a reconcile owns such an object, the framework adds
a finalizer to the owner before creating it, and records the owned types in an
annotation. When the owner is deleted, the framework deletes those objects by
UID, then removes the finalizer. When a reconcile stops declaring such
objects, the framework deletes any that remain and removes the finalizer, so
the owner can then be deleted without the controller running.

### Custom resource definitions

`internal/schema` generates an OpenAPI v3 schema from a struct, using `json`
tags for field names and requiredness and `kube`, `pattern`, and `doc` tags for
validation, defaults, printer columns, and descriptions. `kube:"immutable"`
becomes the validation rule `self == oldSelf`. When a controller for a custom
type starts, it applies the generated CRD, waits until the API server reports
it `Established`, and labels it as installed by the framework. If something
else installed the CRD, for example a Helm chart, the controller leaves it
alone. [CRD upgrades](#crd-upgrades) describes how it updates a CRD that
already exists.

### Shards and leader election

Leader election and sharding are one mechanism. The keys of every controller
in a manager are divided into shards by an FNV hash of namespace and name, and
each shard is a `coordination.k8s.io/v1` Lease with a 15-second duration,
renewed every 2 seconds. A worker reconciles a key only while its replica
holds the key's shard, and a replica that acquires a shard enqueues every
cached key in it and forgets what it last wrote for them, because another
replica may have reconciled them since. Leader election is the case of one
shard. Candidates measure a lease's expiry from when they saw its holder or
renew time change, on their own clock, so clock skew between replicas doesn't
give a shard two holders.

With more than one shard, each replica also renews a membership Lease, and
every replica lists the manager's Leases each retry period. Each computes the
same assignment of shards to live members with rendezvous hashing: a shard
goes to the member with the highest hash of its identity and the shard
number, mixed with MurmurHash3's finalizer, because FNV alone barely changes
its high bits for the last bytes it hashes and gave every shard to one member.
A member joining or leaving moves only the shards assigned to it. A replica
that holds a shard assigned to another live member stops starting reconciles
in it, keeps renewing it until the reconciles in progress finish, and then
releases it, so a key is never reconciled by two replicas at once while
leases work. A free shard that its member doesn't take within a lease
duration goes to any replica, so a member that can't take shards doesn't
strand them.

A replica that can't renew a shard for 10 seconds stops starting reconciles in
it, but keeps running, because its webhooks must keep answering. Reconciles
already running finish, as with any lease-based election. On shutdown,
`Manager.Run` stops reconciles first and then releases its shards, so another
replica takes over in about one retry period.

Sharding by lease, as Knative does, needs no component that labels objects,
but every replica caches every object. Labeling objects with their shard, as
kubernetes-controller-sharding does, would let each replica watch only its
shard's objects, at the cost of a sharder and a write to every object.

### Admission webhooks

A reconciler with a `Validate` or `Default` method, or a handler passed to
`kube.Webhooks`, gets a validating or mutating webhook for its type, for
`CREATE` and `UPDATE` with `matchPolicy: Equivalent`, so requests for other
versions are converted first. Both methods receive the old object on updates.
The webhook decodes the request's object into the projection, so a mutating
webhook can't send the whole object back without dropping the fields the
projection lacks. Instead, it encodes the projection before and after
`Default`, and `jsonpatch.Overlay` applies only the differences to the
request's original JSON, matching list items by position, so fields that the
projection leaves out, including fields inside list items, keep their values.
The patch is the difference between the original and the result.

Webhooks run inside a read-only scope. `Get` and `List` read caches without
recording dependencies, and `Own`, `Apply`, `Delete`, and `RequeueAfter`
reject the request with an error.

Every replica serves webhooks, before it competes for shards. The first
replica to start makes an ECDSA certificate authority valid for ten years and
a serving certificate valid for one, and creates a Secret with both. The
others read the Secret, including a replica that loses the race to create it.
Each replica rereads the Secret every minute. The first to see the serving
certificate within 30 days of expiry, or missing a host name it needs, writes
a new one with the Secret's resource version as a precondition, so replicas
agree. Replacing the CA keeps the old one in the bundle until it expires, so
servers still using a certificate it signed keep working. Each replica applies
the webhook configurations with the bundle, which is idempotent, and deletes
configurations that its program no longer needs, so that a dropped webhook
doesn't fail every request for its type.

### Versions and conversion

`kube.Version[V]` adds a served version to the CustomResourceDefinition, with
a schema from `V`. The reconciled type is the hub and the stored version, as
in Kubebuilder, and versions convert through it with `ConvertTo` and
`ConvertFrom` methods. The framework finds the methods by asserting
`converter[T]`, an interface with the hub type as its parameter. A version
without them converts by copying fields with the same JSON names. If no
version has methods, the CustomResourceDefinition uses the `None` strategy and
no webhook. The conversion webhook copies each object's metadata from the
request, because the API server rejects conversions that change it and the
projection's metadata has fewer fields than the object's.

### CRD upgrades

A program that installs its own CRDs updates them with every release, and
during a rolling update or a rollback, an older release can start after a
newer one. Tests against `kube-apiserver` v1.37.0, reading etcd directly,
showed what can go wrong:

- When a field leaves a version's schema, reads stop returning it at once,
  and the next write of any kind, including a status update, stores the
  object without it. Restoring the field doesn't bring the values back.
- When a version's schema newly requires a field, updates that change
  `spec` fail for objects without it. Status and metadata updates succeed.
- A no-op merge patch with the object's resource version, sent to the status
  subresource, stores the object in the current storage version. A second
  one doesn't write, and a stale resource version gets `409 Conflict`.
- After a version leaves the CRD, server-side apply fails with `request to
  convert CR to an invalid group/version` on objects that have
  `managedFields` entries for it, including the controller's own status
  updates. Patches that remove the entries report success and change
  nothing. While the version is in the CRD but unserved, the API server still
  converts objects to it for server-side apply, so its conversion must work
  until the entries are gone.

So before applying a CRD over one that the framework installed, `installCRD`
compares them. If the cluster's CRD has a version that sorts after all of the
program's versions in Kubernetes version priority, a newer release installed
it, and the framework leaves it alone. For each served version in both, it
diffs the schemas for removed fields, changed types, and newly required fields
without defaults, and lists the objects at that version to see which changes
touch data. It keeps the cluster's schema for removed and retyped fields that
some object sets, warns about required fields that some object lacks, and
applies the rest. If it can't list the objects, it keeps every removed and
retyped field. A version that the program no longer declares is removed only
if it isn't in `status.storedVersions` and no object's `managedFields` names
it. Otherwise the program fails to start with an error that names the
release to run first.

After the controller's cache syncs, the replica that holds the shard of the
CRD's name runs Cluster API's two phases. If `status.storedVersions` isn't just
the storage version, it applies the no-op patch to every object, through the
status subresource when there is one, ignoring `404` and `409`. Then it sets
`status.storedVersions` with the CRD's resource version from before the
patches as a precondition, so a CRD that changed meanwhile means another
pass. For each unserved version, it removes that version's `managedFields`
entries with a JSON patch that also replaces the resource version, and, like
Cluster API, leaves a minimal entry for the same manager when none would
remain, because server-side apply infers an owner for every field of an
object without entries. It retries failures with backoff. The `unserved` tag
option is the step between serving a version and deleting it.

### Protobuf

`internal/protobuf` decodes protobuf into the same projections that JSON
decodes into, without generated code. The API server sends an object as the
bytes `k8s\x00` followed by a `runtime.Unknown` message that holds the type and
the encoded object, a list as a list message whose items field holds encoded
objects, and a watch as length-prefixed `WatchEvent` messages, each holding an
object in the same envelope. Errors come back as encoded `Status` messages.

The decoder needs each field's number. `schema.txt` lists them for every
stable kind, by JSON name, about 100 KB. The `gen` command writes it from the
`protobuf` struct tags on the Go types in `k8s.io/api`, in a separate module,
so the kube module never depends on `k8s.io/api`. Field numbers never change
once Kubernetes assigns them, so an old schema decodes newer servers'
objects, skipping fields it doesn't know. A plan matches a struct's fields to
the schema by JSON name, the way `encoding/json` matches them, and fails if
the struct declares a field the schema lacks, so a newer field never decodes
as empty: the cache reads that type as JSON. The schema is parsed lazily, one
kind and the messages it contains at a time.

Some fields differ between the two encodings. A struct that `encoding/json`
inlines, such as a Volume's VolumeSource, is a nested message. Times,
quantities, and int-or-string values are messages in protobuf but strings or
numbers in JSON. A few lists, such as a user's extra values, are messages that
wrap a repeated field. The decoder sets times and quantities directly, and
converts other such values, or any field whose Go type has an `UnmarshalJSON`
method, to the JSON value that the API server would send, and decodes that
with `encoding/json`. A test creates an object of every type in the `k8s`
package on a real API server and checks that its JSON and protobuf decode to
equal structs.

### The client

`internal/client` is a small REST client for the Kubernetes API. It reads
kubeconfig files with a parser for the subset of YAML they use, supports
in-cluster service account tokens, client certificates, and exec credential
plugins, and uses HTTP/2 with pings to detect dead connections. It turns API
errors into Go errors with `IsNotFound`, `IsConflict`, `IsGone`, and similar
functions, from JSON or protobuf `Status` responses, and finds resource names
through discovery. Caches ask for protobuf with JSON as a fallback, and the
client decodes whichever the response's `Content-Type` names.

### Installation

`PROGRAM generate -registry=REGISTRY` builds the program that runs it into an
image and writes the YAML that installs it, the way [ko](https://ko.build)
builds Go programs into images without a Dockerfile.

The RBAC rules come from the program. Each controller's `describe` method
reports its type, the types that it owns, and whether it serves webhooks,
without a cluster. The types that `Reconcile` reads and writes are known only
at run time, so `internal/analysis` finds them in the source. It runs `go list
-deps -export` for the program's package, parses the packages that import
kube, and type-checks them with `go/types`, importing every other package from
the compiler's export data. Each instantiation of `Get`, `List`, `Fetch`,
`Own`, `Apply`, or `Delete` names a type, or a type parameter of the generic
function that contains the call. The analysis follows type parameters back
through generic helpers to the types that the program passes, and reads each
type's `kube` tag. `Get` and `List` need `list` and `watch`, `Fetch` needs
`get`, `Own` needs `list`, `watch`, `create`, `patch`, and `delete`, `Apply`
needs `create` and `patch`, and `Delete` needs `delete`. When a type passed to
`Apply` has a field whose `json` tag names it `status`, the rules also grant
`patch` on the type's `status` subresource. `controller-gen` reads
`+kubebuilder:rbac` comment markers, which people write and update by hand.
These rules change when the calls do.

The rules go in a ClusterRole, because a program watches every namespace,
except those for the program's own Leases and webhook certificate, which go in
a Role in its namespace. With `-watch-namespace`, the program runs with
`-namespace`, and the rules for a type whose `kube` tag says
`scope=Namespaced`, or that the program defines without `scope=Cluster`, go in
a Role in the watched namespace. A reconciled type with more than one version
keeps its rules in the ClusterRole, because migrating its stored objects to a
new version lists and patches them in every namespace.

[go-containerregistry](https://github.com/google/go-containerregistry), kube's
only dependency, builds and pushes the image. For each platform, `generate`
builds the program with `CGO_ENABLED=0`, adds one layer that holds it at
`/app/PROGRAM` to the base's image for that platform, sets the entrypoint and
a non-root user, and pushes an index of the images. Each image names its base
with the `org.opencontainers.image.base.name` and `.digest` annotations, and
leaves out the base's own annotations, such as its title and source
repository, which describe the base. Timestamps are the Unix
epoch, so the same source and base give the same digest, and the Deployment
names the image by digest. The copy of the program in the image is built with
the `kube_nogenerate` build tag, which leaves out `generate` and
go-containerregistry with it, so the program in the cluster links only kube.

`internal/yaml` writes the YAML from ordered JSON, so the output is stable. It
quotes strings that YAML 1.1 parsers read as other types, such as `on`, `yes`,
`1:20`, and `.5`. The Deployment runs the program with probes on `/readyz` and
`/healthz`, as a non-root user with a read-only root file system, and with
`-leader-elect` or `-shards` when it has more than one replica. An `emptyDir`
volume at `/tmp` gives `os.TempDir` somewhere to write. With `-tmp-size`, the
volume has a size limit, and the kubelet evicts a Pod that writes more instead
of letting it fill the node's disk.

### Testing

`kube.Fake` gives `Reconcile` a scope backed by a list of objects instead of
caches. The reconcile runs the same code as in a cluster, and the scope
records its intents for the test to check with `kube.Owned`,
`kube.Applied`, and `kube.Deleted`. `kube.Applied` returns each object with
the status that the framework would apply, and the scope rejects a status for
the reconciled object as it does in a cluster. In a cluster, every type of a
kind reads the same objects, so the fake converts the listed objects of one
type through JSON for reads of another type of the same kind. A test doesn't
fake an API server, so there's no fake behavior that can differ from a real
server's.

End-to-end tests start `etcd` and `kube-apiserver` from the controller-tools
envtest release, with no kubelet or controller manager. The API server calls
webhooks at a loopback address with the manager's CA bundle, as it would
call a Service in a cluster. Every example has end-to-end tests. The
framework's tests check that:

- A converged controller makes no writes when its objects' labels change, and
  none after a restart.
- Reconciles that apply their own entries in another object's status own
  only those entries, make no writes when they run again, and remove an entry
  when they stop applying it. A status for a kind without a status
  subresource fails the reconcile after the rest of the object is applied. A
  reconcile that applies one object through two types fails and writes
  nothing. A controller that may not patch a Deployment's status still
  applies a label to it. Restarted without permission to patch a Poll's
  status, a controller fails to withdraw its vote, and withdraws it once it
  has the permission. When a reconcile applies a vote and a label and then
  fails, the next reconcile that abstains removes both.
- Panics and permanent errors are reported and retried correctly.
- Leader election fails over.
- Three replicas with 32 shards split the work, hand shards over when one
  stops and another starts, and never reconcile one object at the same time.
- Admission webhooks reject and default objects, including a metadata-only
  webhook whose patch keeps a ConfigMap's data, and a later version of the
  program removes the webhooks it dropped.
- Objects written in one version read back in another, through the
  conversion webhook or without one.
- The JSON and protobuf encodings of every type in the `k8s` package decode
  to equal structs.
- The program in the image that `generate` pushes runs with the token of the
  service account that `generate` installs, so it has only the RBAC rules
  that `generate` wrote.

A test in `e2e/kind` runs the whole installation in a
[kind](https://kind.sigs.k8s.io/) cluster, which has a kubelet and
kube-proxy. It pushes to a local registry as kind's
[guide](https://kind.sigs.k8s.io/docs/user/local-registry/) describes, pipes
`generate` to `kubectl apply`, and checks that a Website's Service serves,
that reconciles continue after every controller pod is replaced, and that the
podpolicy webhooks deny and default pods through their Service.

## Measurements

The benchmark in [`bench/`](../bench/main.go) is a separate Go module, so
`client-go` and `controller-runtime` never enter kube's module graph. It
starts `etcd` 3.7.0 and `kube-apiserver` v1.37.0, creates 5,000 Pods and 1,000
Secrets, and measures each cache design in a fresh process. The Pods look like
a Deployment's Pods. Each has labels, an owner reference, one container with
eight environment variables, and a status written by a second field manager.
Each Pod's JSON is 8,235 bytes on average, including `managedFields`. The
machine has 8 vCPUs and runs Go 1.26.0. The comparison uses `client-go`
v0.37.1 and `controller-runtime` v0.25.2.

To reproduce the measurements, run:

```sh
cd bench
KUBEBUILDER_ASSETS="$(bash ../fetch-envtest.sh)" go run . -pods 5000
```

### Memory

Heap is measured after a garbage collection, before and after the cache
syncs:

| Cache | Heap for 5,000 Pods | Per Pod |
| --- | --- | --- |
| `client-go` informer | 70.0 MiB | 14,685 B |
| `client-go` informer without `managedFields` | 51.9 MiB | 10,894 B |
| kube with `k8s.Pod` | 25.9 MiB | 5,442 B |
| kube with `k8s.Pod`, JSON | 25.7 MiB | 5,392 B |
| kube with `k8s.Pod`, interning off | 27.4 MiB | 5,747 B |
| kube with a two-field type | 7.4 MiB | 1,551 B |
| kube, metadata only | 6.6 MiB | 1,390 B |

`managedFields` is 26% of `client-go`'s heap per Pod. `k8s.Pod` declares the
Pod fields that controllers commonly use, and kube stores it in 37% of the
memory of a `client-go` Pod, or 50% of a `client-go` Pod without
`managedFields`. A type with only `spec.nodeName` and `status.phase`, enough
for a controller that counts Pods per node, uses a ninth of the memory of a
`client-go` Pod. The heap includes the protobuf schema of the kinds read,
which is 179 KiB for Pods, about 37 bytes per Pod at this count.

Metadata only saves bandwidth as well as memory. Listing 1,000 Secrets of
8 KiB each transfers 10.8 MiB in full and 0.40 MiB as metadata only.

### Sync time

| Cache | Initial sync of 5,000 Pods |
| --- | --- |
| `client-go` informer, protobuf | 0.20 s |
| kube, streaming list, protobuf | 0.18 s |
| kube, streaming list, JSON | 0.51 s |
| kube, paginated list, protobuf | 0.31 s |
| kube, metadata only, protobuf | 0.12 s |

Across four runs, kube's protobuf sync took 0.18 to 0.23 seconds and
`client-go`'s 0.20 to 0.30 seconds. To see where time goes, the benchmark also
reads the Pods without decoding them:

| Request | Size | Time |
| --- | --- | --- |
| Streaming list, JSON | 39.5 MiB | 0.49 s |
| Streaming list, protobuf | 28.6 MiB | 0.18 s |
| List, JSON | 39.3 MiB | 0.26 s |
| List, protobuf | 28.5 MiB | 0.15 s |

A streaming sync takes as long as the API server takes to send the stream, so
the server's encoding sets the sync time, and protobuf is what closes the gap
with `client-go`. For this Kubernetes version and size, a paginated list is
faster for the server than a streaming list in JSON, but a streaming list
keeps the server's memory bounded, which KEP-3157 is about. CRDs have no
protobuf encoding, so for custom resources, `client-go` and kube both use
JSON.

Decoding is still worth making fast, because it runs on every watch event.
On one core, decoding the benchmark's Pod into a type with metadata,
containers, and environment variables takes 17.7 µs from JSON and 4.8 µs
from protobuf. Into a type with metadata and `spec.nodeName`, it takes
15.2 µs from JSON and 2.5 µs from protobuf, because the protobuf decoder skips
undeclared fields by their length instead of scanning them. Go 1.26's
experimental JSON implementation, with `GOEXPERIMENT=jsonv2`, roughly doubles
JSON decoding speed without code changes, which still leaves it behind
protobuf.

### Writes

The end-to-end tests count writes with the `kube_apply_total` and
`kube_status_writes_total` metrics. After a Widget converges, five label
changes cause five reconciles, no applies, and no status writes. A new manager
that starts over the converged Widget makes no applies and no status writes.
A controller that totals the votes that other managers write into a Poll's
status makes no status writes for votes that leave the total as it was.
A controller that applies each Ballot's vote to a Poll's status with `Apply`
makes no applies when label changes reconcile the Ballots again. A change to
a ConfigMap field that a reconcile's type doesn't declare doesn't run the
reconcile again.

### Binary size and dependencies

| Program | Stripped binary | Modules in the build |
| --- | --- | --- |
| kube, [`examples/website`](../examples/website/main.go), in its image | 8.4 MiB | 1 |
| kube, `examples/website`, with `generate` | 11.7 MiB | 10 |
| `controller-runtime`, [`bench/crsize`](../bench/crsize/main.go) | 30.6 MiB | 61 |

The module counts include each program's own module. The image's copy of the
program is built with `-tags=kube_nogenerate`, so its one module is kube
itself. A plain `go build` includes `generate`, with go-containerregistry and
the eight modules it needs.

## Limitations and future work

kube is an experiment, and it leaves out much of what `controller-runtime`
offers:

- Custom resources are JSON only. CBOR is a binary encoding that covers them,
  but `kube-apiserver` v1.37.0 with default flags answers a CBOR request for
  Pods with `406 Not Acceptable`.
- The protobuf schema covers stable versions of built-in kinds as of
  `k8s.io/api` v0.37.1. Regenerating it picks up new fields and kinds.
- Shards divide reconciles, not memory. Labeling objects with their shard
  would let replicas watch only their own objects.
- `generate` can't follow the type parameter of a generic type, or a type
  argument that contains a type parameter, to the types that it stands for.
  It warns about those calls instead.
- `generate` builds images that hold only the program. ko copies a `kodata`
  directory into the image; kube programs use `embed` instead.
- One cluster per manager.
- Webhooks run for creates and updates, not deletes or connections.
- `Fetch` isn't tracked, by design, so a change to a fetched object doesn't
  run the reconcile again.
- `kube.WatchSelector` and `Finalize` don't combine. An object whose labels
  stop matching looks deleted, so its finalizer is never removed.
- After a restart, or after a reconcile whose writes fail, each object
  declared with `Apply` is applied once, and so is a status that isn't empty,
  because the framework doesn't annotate objects it doesn't own. After a
  restart, a status that leaves out other managers' fields is also written
  once, because the record of the last status write is in memory.
- Fields that `Apply` wrote, including status fields, stay on an object when
  a reconcile stops declaring it, and when the reconciled object is deleted.
  Giving them up would take a durable record of what each reconcile applied.
- `Apply` can't write the status of a custom resource whose definition keeps
  the status with the other fields, without a status subresource.
- The CRD checks compare field names, types, and required fields, not
  validation such as enums or bounds, and they need permission to list
  objects in every namespace.
- Storage migration doesn't wait for every API server in a highly available
  control plane to see a new storage version. Like Cluster API's migrator, it
  relies on the resource version precondition and on running after the cache
  syncs.

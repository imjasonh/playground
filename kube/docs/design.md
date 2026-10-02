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
and that project shards objects across replicas to remove the limit.

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
- No dependencies beyond the Go standard library.
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
type. On a replica with leader election, informers start only after the
replica becomes leader, so standby replicas hold no caches.

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

A watch is a stream of JSON events, each `{"type":"ADDED","object":{...}}`.
Decoding each event into a struct with a `json.RawMessage` field and then
decoding the object costs two passes over the bytes. The informer instead
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

When an informer sees a change, it finds the reconciles that read the object
by name, and the reconciles whose lists match the object's old or new labels.
Matching either catches objects that start or stop matching a selector. Those
reconciles go back in the queue. The `kube_tracked_dependencies` metric counts
the recorded dependencies.

Owned objects carry their owner in a label and an annotation, and each type's
cache indexes objects by owner. A change to an owned object, including its
status, runs its owner's reconcile again. A change to the reconciled object
runs its reconcile only when a declared field other than `status` or
`metadata.resourceVersion` changed, so the controller's own status writes
don't cause another reconcile. Metadata-only types can't see the fields that
matter, so for them every new resource version counts.

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

The framework skips an apply when the cached object already has every field
of the document. That alone isn't enough, because server-side apply removes
fields that a manager stops sending, and a desired object that drops a field
still matches a cached object that has it. So an owned object's document
carries an annotation with a hash of the rest of the document. If the cached
object has every field including that annotation, the last apply sent this
same document, and there's nothing to add or remove. Because the hash lives on
the object, the skip works after a restart or a leader failover. For `Apply`,
the framework doesn't annotate objects it doesn't own, and skips only when
this process applied the same document before. The `kube_apply_total` metric
counts applies by result, `applied` or `skipped`.

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
alone.

### Leader election

Leader election uses a `coordination.k8s.io/v1` Lease with a 15-second
duration, renewed every 2 seconds. A replica that can't renew for 10 seconds
stops its controllers. Candidates measure a lease's expiry from when they saw
its holder or renew time change, on their own clock, so clock skew between
replicas doesn't cause two leaders. A leader that stops releases the lease, so a
standby takes over in about one retry period instead of a lease duration.

### The client

`internal/client` is a small REST client for the Kubernetes API. It reads
kubeconfig files with a parser for the subset of YAML they use, supports
in-cluster service account tokens, client certificates, and exec credential
plugins, and uses HTTP/2 with pings to detect dead connections. It turns API
errors into Go errors with `IsNotFound`, `IsConflict`, `IsGone`, and similar
functions, and finds resource names through discovery.

### Testing

`kube.Fake` gives `Reconcile` a scope backed by a list of objects instead of
caches. The reconcile runs the same code as in a cluster, and the scope
records its intents for the test to check with `kube.Owned`,
`kube.Applied`, and `kube.Deleted`. A test doesn't fake an API server, so
there's no fake behavior that can differ from a real server's.

End-to-end tests start `etcd` and `kube-apiserver` from the controller-tools
envtest release, with no kubelet or controller manager. Every example has
end-to-end tests, and the framework's tests check that a converged controller
makes no writes when its objects' labels change and none after a restart,
that panics and permanent errors are reported and retried correctly, and that
leader election fails over.

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
| `client-go` informer | 70.0 MiB | 14,687 B |
| `client-go` informer without `managedFields` | 51.9 MiB | 10,894 B |
| kube with `k8s.Pod` | 25.3 MiB | 5,314 B |
| kube with `k8s.Pod`, interning off | 26.7 MiB | 5,600 B |
| kube with a two-field type | 6.9 MiB | 1,453 B |
| kube, metadata only | 6.7 MiB | 1,399 B |

`managedFields` is 26% of `client-go`'s heap per Pod. `k8s.Pod` declares the
Pod fields that controllers commonly use, and kube stores it in 36% of the
memory of a `client-go` Pod, or 49% of a `client-go` Pod without
`managedFields`. A type with only `spec.nodeName` and `status.phase`, enough
for a controller that counts Pods per node, uses a tenth of the memory of a
`client-go` Pod.

Metadata only saves bandwidth as well as memory. Listing 1,000 Secrets of
8 KiB each transfers 10.8 MiB in full and 0.40 MiB as metadata only.

### Sync time

| Cache | Initial sync of 5,000 Pods |
| --- | --- |
| `client-go` informer, protobuf | 0.20 s |
| kube, streaming list | 0.49 s |
| kube, paginated list | 0.41 s |
| kube, metadata only | 0.35 s |

`client-go`'s generated clients ask for protobuf for built-in types. To see
where time goes, the benchmark also reads the Pods without decoding them:

| Request | Size | Time |
| --- | --- | --- |
| Streaming list, JSON | 39.5 MiB | 0.47 s |
| List, JSON | 39.3 MiB | 0.28 s |
| List, protobuf | 28.5 MiB | 0.18 s |

kube's streaming sync takes as long as the API server takes to send the
stream, so the server's JSON encoding sets the sync time, not kube's decoding.
For this Kubernetes version and size, a paginated JSON list is faster for the
server than a streaming list, but a streaming list keeps the server's memory
bounded, which KEP-3157 is about. CRDs have no protobuf encoding, so for custom
resources, `client-go` and kube both use JSON.

Decoding is still worth making fast, because it runs on every watch event.
On one core, decoding the benchmark's Pod JSON into a type with metadata,
containers, and environment variables runs at 118 MB/s, and into a type with
metadata and `spec.nodeName` at 138 MB/s. Go 1.26's experimental JSON
implementation, with `GOEXPERIMENT=jsonv2`, raises these to 228 MB/s and
274 MB/s and cuts allocations per Pod from 74 to 21, without code changes.

### Writes

The end-to-end tests count writes with the `kube_apply_total` and
`kube_status_writes_total` metrics. After a Widget converges, five label
changes cause five reconciles, no applies, and no status writes. A new manager
that starts over the converged Widget makes no applies and no status writes.

### Binary size and dependencies

| Program | Stripped binary | Modules in the build |
| --- | --- | --- |
| kube, [`examples/website`](../examples/website/main.go) | 7.7 MiB | 1 |
| `controller-runtime`, [`bench/crsize`](../bench/crsize/main.go) | 30.6 MiB | 61 |

The module counts include each program's own module. kube's one module is
itself.

## Limitations and future work

kube is an experiment, and it leaves out much of what `controller-runtime`
offers:

- JSON only. The API server sends built-in types as protobuf faster than as
  JSON, and a protobuf decoder that fills only declared fields can close the
  sync gap for built-in types. CBOR is a binary encoding that also covers
  custom resources, but `kube-apiserver` v1.37.0 with default flags answers a
  CBOR request for Pods with `406 Not Acceptable`.
- One version per custom type, and no conversion or admission webhooks.
- No generated RBAC rules or deployment manifests. The framework knows every
  type a controller reads and writes only at run time.
- One cluster per manager, and one active replica per controller.
- `Fetch` isn't tracked, by design, so a change to a fetched object doesn't
  run the reconcile again.
- `kube.WatchSelector` and `Finalize` don't combine. An object whose labels
  stop matching looks deleted, so its finalizer is never removed.
- After a restart, each object declared with `Apply` is applied once, because
  the framework doesn't annotate objects it doesn't own.

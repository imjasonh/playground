# Substrate actor overlay

These files run a tenant's CI runners as Agent Substrate actors. They are
applied **after** Agent Substrate
([agent-substrate/substrate](https://github.com/agent-substrate/substrate)) is
installed into the cluster, and after
the `cas`/`cascache` control plane from `../` is already running. Install the
Substrate release that `../../go.mod` requires as `go.ate.dev/substrate`; the
pool's client is built against it, and `workerpool.yaml` runs its
`ateworker-gvisor` image. The daily dependency update moves all three to each
new release. They are not
part of the default kind e2e: that e2e proves multi-tenancy, node-local
caching, and remote execution with the runner Deployment in
`../40-runner.yaml`, and it is what CI gates on.

| File | What it is |
|------|------------|
| `workerpool.yaml` | Two `WorkerPool`s of gVisor workers labeled `workload: ci-runner`: `ci-runner-base`, one worker on the always-on node, and `ci-runner`, the burst pool on autoscaled nodes, whose replicas the pool sets. Actors from the runner template land on either. |
| `casfs-csi.yaml` | The `casfs-csi` DaemonSet, its controller Service, the `CSIDriverConfig` that tells Substrate where the driver listens, the tenant's `StorageClass` (`casfs-tenant-a`, parameters `instance: tenant-a` and `atespace: tenant-a`), and the driver's ServiceAccount. The driver mounts an inputs volume for each actor on the actor's node and serves it from that node's `cascache` with the tenant's token. |
| `egress-cas.yaml` | The egress policy every runner actor gets: plain gRPC to the `cas` Service only, with Substrate's egress gateway injecting a short-lived signed Actor JWT (`actorJwt`) into `x-ci-substrate-tenant` — no per-tenant token Secrets or `k8s-credential-provider-namespace-policy` needed. |
| `runner-template.yaml` | The `ActorTemplate` for default and clean-room runner actors: `GOLDEN_SNAPSHOT_MODE_ENABLED` memory snapshots, actor name projected into `/system/name` (re-read per lease), and an external `inputs` volume of the tenant's `StorageClass` mounted at `/inputs`. |
| `runner-env-template.yaml` | Companion volume-free `ActorTemplate` (`ci-runner-env`, `-input-mode=copy`) used for pre-warmed Substrate Tag environments (`ci-substrate/env=<tag>`), since Substrate Tag cloning does not support external volumes. |
| `pool.yaml` | The `pool` Deployment for the tenant, its per-tenant ServiceAccount (`ci-substrate-pool-tenant-a`) in `ci-substrate`, and a Role letting that ServiceAccount change only the burst `WorkerPool`'s scale. It sizes the tenant's actors across RBE platform queues (`default`, `ci-substrate/env=<tag>`, `ci-substrate/isolation=clean`) and sizes the burst `WorkerPool` to its actors. |

`../../e2e/run-substrate.sh` applies all of it for `tenant-a` and runs the
Go e2e tests (`e2e/`) against the result. `../../e2e/run-substrate-kind.sh` builds a
two-node kind cluster with the [node pools](#node-pools) below, installs
Substrate, and runs it there. By hand, for each CI tenant:

1. Create the atespace `tenant-a`.
2. Configure `StatefulSet/cas` to verify Substrate Actor JWTs: mount the
   `servicedns.podcert.ate.dev/identity` `ClusterTrustBundle` and set
   `ACTOR_JWT_ISSUER=https://idp.ate-system.svc`,
   `ACTOR_JWT_AUDIENCE=cas.ci-substrate.svc.cluster.local`, and
   `ACTOR_JWT_CA_FILE=/run/ate-idp/trust-bundle.pem`.
3. Apply `workerpool.yaml`. It needs the node labels and taint in
   [Node pools](#node-pools).
4. Turn on Substrate's `ExternalVolumes` preview gate: add
   `ExternalVolumes` to the `--preview=` argument of the `ate-api-server`
   Deployment in `ate-system`. Substrate keeps external volumes behind it.
5. Grant the CSI driver's ServiceAccount `viewer` and the tenant pool's
   ServiceAccount `editor` in the atespace. The driver refuses a volume for an
   actor that isn't in the `StorageClass`'s `atespace` (which it learns by
   listing actors), and the pool creates, resumes, suspends, reverts, and deletes
   actors and their egress policies in only that atespace. Both reach
   `ate-api-server` through the `ci-substrate` namespace's
   `ate.dev/api-access=true` label (set in `../00-namespace-and-config.yaml`):

   ```bash
   kubectl ate create access-policy -a tenant-a -f - <<'EOF'
   bindings:
   - role: viewer
     members:
     - user:system:serviceaccount:ci-substrate:casfs-csi
   - role: editor
     members:
     - user:system:serviceaccount:ci-substrate:ci-substrate-pool-tenant-a
   EOF
   ```

   If the atespace already has an access policy, add the members with
   `kubectl ate update access-policy` instead.
6. Deploy the CSI driver and the tenant's `StorageClass`:

   ```bash
   ko apply -f casfs-csi.yaml
   kubectl -n ci-substrate rollout status daemonset/casfs-csi
   ```

   For another tenant, add a `StorageClass` with that tenant's instance
   name as the `instance` parameter and its atespace as the `atespace`
   parameter, and give the ServiceAccount `viewer` there. The driver
   resolves the instance to a token from the `tenants` Secret, so the
   `StorageClass` needs no secret of its own. A `StorageClass`'s parameters
   can't change, so delete and recreate one to change them.
7. Resolve and create the actor templates (`--preview` is needed for
   `runner-template.yaml`'s external volume):

   ```bash
   ko resolve -f runner-template.yaml > /tmp/runner-template.yaml
   kubectl ate --preview create actor-template -f /tmp/runner-template.yaml
   ko resolve -f runner-env-template.yaml > /tmp/runner-env-template.yaml
   kubectl ate create actor-template -f /tmp/runner-env-template.yaml
   ```

   An actor keeps the volumes it was created with. To change a template,
   stop the pool, delete its actors, delete the template, and create the
   new one; `run-substrate.sh` does this when the template exists.
8. Put the egress policy in a ConfigMap and deploy the pool:

   ```bash
   kubectl -n ci-substrate create configmap ci-substrate-pool-tenant-a \
     --from-file=egress-policy.yaml=egress-cas.yaml
   ko apply -f pool.yaml
   ```

The pool creates actors from the templates (never reusing deleted actor names,
since Substrate's egress gateway caches policies by atespace and actor name),
sets each one's egress policy before its first resume, and then:

- forks new default actors from `ci-runner`'s golden memory snapshot
  (`GOLDEN_SNAPSHOT_MODE_ENABLED`) and keeps `WARM` actors (default 1)
  suspended with a snapshot;
- forks actors for `ci-substrate/env=<tag>` RBE `Platform.Properties` directly
  from the published Substrate `Tag` (`sourceTag`) using `ci-runner-env`;
- reverts `ci-substrate/isolation=clean` actors back to their clean durable
  snapshot via `RevertActor` between actions (and deletes them once idle);
- resumes a suspended actor for each queued action that no running actor is
  free to take, and creates more up to `MAX` (default 4);
- suspends an actor that has run nothing for `IDLE_AFTER` (default 2m), and
  deletes suspended actors beyond `WARM`;
- deletes crashed non-clean actors and replaces them under a new name;
- retries the first resume of an actor it created, each reconcile, until it
  succeeds.

When `WORKER_POOL` names a `WorkerPool` (`namespace/name`), the pool also
sets that pool's replicas through its scale subresource. `BASE_SLOTS` is how
many actors fit on workers the pool doesn't size, here `ci-runner-base`'s
one worker; `ACTORS_PER_WORKER` is how many actors one burst worker hosts;
and `MAX_WORKERS` caps the burst pool. Substrate fits actors on a worker by
the `WorkerPool`'s `limits` and the template's `resources`, so update
`BASE_SLOTS` and `ACTORS_PER_WORKER` when you change either: a 2-CPU worker
holds two 1-CPU actors. Each reconcile, it wants enough burst
workers for the actors that are running or about to resume beyond
`BASE_SLOTS`, and grows the `WorkerPool` before it resumes them. Until the
new worker is ready, a resume fails with "no worker has room for the
actor", and the pool tries again on its next reconcile. It shrinks the
`WorkerPool` only when no actor is resuming and none of its actors is on a
burst worker, since a scale-down can stop any worker and Substrate crashes
the actor on it. When every actor is suspended, that is zero, and the
cluster autoscaler removes the burst nodes. The pool calls the Kubernetes
API with a projected token for `ci-substrate-pool-tenant-a`, which the `ci-substrate-pool` Role allows to get and patch
only `workerpools/scale` for `ci-runner`.

It reads the queue from the scheduler in `cas` with `WorkerService.Status`,
which reports queued actions and the bot ids holding leases. The runner's
bot id is its actor name (projected from actor metadata into
`/system/name`), so the pool knows which actors are busy without asking
them. The pool also holds a `WorkerService.WatchStatus` stream open, which
sends a new report each time the queue changes, so a queued action wakes an
actor within `MIN_INTERVAL` (default 250ms) rather than on the next poll.
It still reconciles every `INTERVAL` (default 5s) to see what only Substrate
knows: crashed actors, finished resumes, a worker with room for a resume that
failed, and idle runners. Substrate has no change feed, and scale-up waits on
the middle two.

The runner in the actor sends a placeholder tenant header. The egress gateway
replaces it with the tenant's token, so the sandbox holds no credential. The
gVisor sandbox has no `/dev/fuse`, and the runner needs none: its
`-input-mode=volume` makes each exec root with a `mkdir` of the input root's
digest on `/inputs`, and the `casfs-csi` driver on the node loads the tree
from that node's `cascache` and serves each file on its first read. The
pool's calls to `ate-api-server` carry `Ate-Preview-Allowed: true`, which
the API needs to create an actor from a template with external volumes.

How a volume reaches the sandbox: when Substrate assigns the actor to a
worker, `ate-api-server` calls the driver's `CreateVolume` through the
`casfs-csi` Service (the `CSIDriverConfig` names it) and records the volume
id. `atelet` on the worker's node then calls `NodePublishVolume` on the
driver's socket under
`/var/lib/kubelet/plugins/casfs.ci-substrate.imjasonh.com/`, the driver
mounts `casfs` with `allow_other` at the target under
`/var/lib/ate`, and `atelet` binds that path into the gVisor sandbox. The
DaemonSet mounts `/var/lib/ate` with `Bidirectional` propagation so the
mount is visible to `atelet` and the worker pod. On suspend, `atelet`
unpublishes and the mount goes away; a resume publishes a fresh, empty
volume. The driver runs as root and privileged: FUSE `allow_other`, the
kubelet plugins directory, and detaching a stale mount need it.

## Node pools

Agent Substrate runs on GKE Standard. Give the cluster two node pools:

- An always-on pool of one node, labeled and tainted
  `ci-substrate.imjasonh.com/always-on=true` (the taint's effect is
  `NoSchedule`). It runs Substrate's control plane, `cas`, telemetry, the
  pool, and `ci-runner-base`, so a build's first action starts without
  waiting for a node. Size it for those plus `ci-runner-base`'s worker.
- A burst pool labeled `ci-substrate.imjasonh.com/burst=true`, with no taint
  and autoscaling from a minimum of 0. The `ci-runner` workers run there.

```bash
gcloud container node-pools create always-on --cluster=CLUSTER \
  --num-nodes=1 --machine-type=e2-standard-8 \
  --node-labels=ci-substrate.imjasonh.com/always-on=true \
  --node-taints=ci-substrate.imjasonh.com/always-on=true:NoSchedule
gcloud container node-pools create burst --cluster=CLUSTER \
  --enable-autoscaling --min-nodes=0 --max-nodes=4 \
  --machine-type=e2-standard-4 --spot \
  --node-labels=ci-substrate.imjasonh.com/burst=true
```

The manifests in `../` and here tolerate the taint: `cas` and telemetry
prefer the always-on node, and the `cascache` and `casfs-csi` DaemonSets run
on both. Substrate's own Deployments and StatefulSets in `ate-system` do
not, so add the toleration and a
`ci-substrate.imjasonh.com/always-on: "true"` `nodeSelector` to each, and the toleration to its DaemonSets, such as
`atelet`; `run-substrate-kind.sh` shows one way. A pod without the
toleration lands on a burst node and keeps that node from scaling to zero.
GKE's own system pods also need a node; check where they run before you
count on the burst pool emptying.

## Cluster requirements

- `atelet` pulls actor images itself, from inside its pod. The registry in
  the resolved template must be reachable from pods: a kind registry
  published on `127.0.0.1` is not, and `atelet`'s
  `--localhost-registry-replacement` flag names the endpoint it uses for
  `localhost` references. `run-substrate.sh` takes
  `CI_SUBSTRATE_ACTOR_IMAGE_REPO` for the repository to resolve the template
  against when it differs from `KO_DOCKER_REPO`.
- The worker pool's `SandboxConfig` names the gVisor release to download. On
  a node without egress, upload the release to Substrate's object store and
  point the `SandboxConfig` at the `s3://` or `gs://` copy; the object-store
  plugin serves it from there.
- `kubectl-ate` acts as `ate-system/ate-client` by default (Substrate's
  default bootstrap owner); the pool uses its own per-tenant ServiceAccount in
  `ci-substrate` with the `editor` role in only its tenant's atespace.
- `ate-api-server` must reach the `casfs-csi` Service on port 9095 for
  `CreateVolume`, and the worker pod must see mounts made under
  `/var/lib/ate` on the host. Both hold on kind.

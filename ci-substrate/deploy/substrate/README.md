# Substrate actor overlay

These files run a tenant's CI runners as Agent Substrate actors. They are
applied **after** Agent Substrate
([agent-substrate/substrate](https://github.com/agent-substrate/substrate)) is
installed into the cluster with the `k8s.io` credential provider, and after
the `cas`/`cascache` control plane from `../` is already running. They are not
part of the default kind e2e: that e2e proves multi-tenancy, node-local
caching, and remote execution with the runner Deployment in
`../40-runner.yaml`, and it is what CI gates on.

| File | What it is |
|------|------------|
| `workerpool.yaml` | A `WorkerPool` of gVisor workers labeled `workload: ci-runner`. Actors from the runner template land on these workers. |
| `tenant-a-token.yaml` | The tenant's cas token in a namespace of its own, for the egress gateway to inject. |
| `casfs-csi.yaml` | The `casfs-csi` DaemonSet, its controller Service, the `CSIDriverConfig` that tells Substrate where the driver listens, and the tenant's `StorageClass` (`casfs-tenant-a`, parameter `instance: tenant-a`). The driver mounts an inputs volume for each actor on the actor's node and serves it from that node's `cascache` with the tenant's token. |
| `egress-cas.yaml` | The egress policy every runner actor gets: plain gRPC to the `cas` Service only, with the tenant token replacing the placeholder header. Inputs don't go through egress. |
| `runner-template.yaml` | The `ActorTemplate` for a runner actor: the `runner` bot with the tenant's instance, a placeholder token, its actor name as its bot id, and an external `inputs` volume of the tenant's `StorageClass` mounted at `/inputs`. |
| `pool.yaml` | The `pool` Deployment for the tenant. It runs in `ate-system` as the `ate-client` ServiceAccount and sizes the tenant's actors to its queue. |

`../../e2e/run-substrate.sh` applies all of it for `tenant-a` and runs
`cictl` against the result. By hand, for each CI tenant:

1. Create the atespace `tenant-a`.
2. Apply `tenant-a-token.yaml` to put the tenant's token in its own
   namespace, and grant the `tenant-a` atespace that namespace in the
   `k8s-credential-provider-namespace-policy` ConfigMap.
3. Apply `workerpool.yaml`.
4. Turn on Substrate's `ExternalVolumes` preview gate: add
   `ExternalVolumes` to the `--preview=` argument of the `ate-api-server`
   Deployment in `ate-system`. External volumes are behind it in Substrate
   v1.0.0.
5. Deploy the CSI driver and the tenant's `StorageClass`:

   ```bash
   ko apply -f casfs-csi.yaml
   kubectl -n ci-substrate rollout status daemonset/casfs-csi
   ```

   For another tenant, add a `StorageClass` with that tenant's instance
   name as the `instance` parameter. The driver resolves it to a token from
   the `tenants` Secret, so the `StorageClass` needs no secret of its own.
6. Resolve and create the actor template, with `--preview` so the API
   accepts the external volume:

   ```bash
   ko resolve -f runner-template.yaml > /tmp/runner-template.yaml
   kubectl ate --preview create actor-template -f /tmp/runner-template.yaml
   ```

   An actor keeps the volumes it was created with. To change the template,
   stop the pool, delete its actors, delete the template, and create the
   new one; `run-substrate.sh` does this when the template exists.
7. Put the egress policy in a ConfigMap and deploy the pool:

   ```bash
   kubectl -n ate-system create configmap ci-substrate-pool-tenant-a \
     --from-file=egress-policy.yaml=egress-cas.yaml
   ko apply -f pool.yaml
   ```

The pool creates `ci-runner-N` actors from the template, sets each one's
egress policy before its first resume, and then:

- keeps `WARM` actors (default 1) suspended with a snapshot, so a resume is
  a memory restore, not an image pull and a cold start;
- resumes a suspended actor for each queued action that no running actor is
  free to take, and creates more up to `MAX` (default 4);
- suspends an actor that has run nothing for `IDLE_AFTER` (default 2m), and
  deletes suspended actors beyond `WARM`;
- deletes crashed actors and replaces them under a new name.

It reads the queue from the scheduler in `cas` with `WorkerService.Status`,
which reports queued actions and the bot ids holding leases. The runner's
bot id is its actor name (projected from actor metadata into
`/system/name`), so the pool knows which actors are busy without asking
them.

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
driver's socket under `/var/lib/kubelet/plugins/casfs.ci-substrate.dev/`,
the driver mounts `casfs` with `allow_other` at the target under
`/var/lib/ate`, and `atelet` binds that path into the gVisor sandbox. The
DaemonSet mounts `/var/lib/ate` with `Bidirectional` propagation so the
mount is visible to `atelet` and the worker pod. On suspend, `atelet`
unpublishes and the mount goes away; a resume publishes a fresh, empty
volume. The driver runs as root and privileged: FUSE `allow_other`, the
kubelet plugins directory, and detaching a stale mount need it.

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
- `kubectl-ate` acts as `ate-system/ate-client` by default, which is also
  the identity the pool uses.
- `ate-api-server` must reach the `casfs-csi` Service on port 9095 for
  `CreateVolume`, and the worker pod must see mounts made under
  `/var/lib/ate` on the host. Both hold on kind.

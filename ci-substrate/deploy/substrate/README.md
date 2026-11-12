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
| `egress-cascache.yaml` | The egress policy every runner actor gets: plain gRPC to the `cascache` and `cas` Services only, with the tenant token replacing the placeholder header. |
| `runner-template.yaml` | The `ActorTemplate` for a runner actor: the `runner` bot with the tenant's instance, a placeholder token, and its actor name as its bot id. |
| `pool.yaml` | The `pool` Deployment for the tenant. It runs in `ate-system` as the `ate-client` ServiceAccount and sizes the tenant's actors to its queue. |

`../../e2e/run-substrate.sh` applies all of it for `tenant-a` and runs
`cictl` against the result. By hand, for each CI tenant:

1. Create the atespace `tenant-a`.
2. Apply `tenant-a-token.yaml` to put the tenant's token in its own
   namespace, and grant the `tenant-a` atespace that namespace in the
   `k8s-credential-provider-namespace-policy` ConfigMap.
3. Apply `workerpool.yaml`.
4. Resolve and create the actor template:

   ```bash
   ko resolve -f runner-template.yaml > /tmp/runner-template.yaml
   kubectl ate create actor-template -f /tmp/runner-template.yaml
   ```

5. Put the egress policy in a ConfigMap and deploy the pool:

   ```bash
   kubectl -n ate-system create configmap ci-substrate-pool-tenant-a \
     --from-file=egress-policy.yaml=egress-cascache.yaml
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
gVisor sandbox has no `/dev/fuse`, so the runner's `auto` input mode falls
back to copying inputs into the exec root; the runner Deployment outside
Substrate mounts them lazily with FUSE.

Actor egress leaves the sandbox through the `atenet-egress` gateway, so the
gateway pod, not the actor, opens the connection to `cascache`. With
`internalTrafficPolicy: Local`, that connection reaches the cascache on the
gateway's node, not the actor's. The top-level README describes this gap and
how to close it.

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

# ci-substrate

A KinD demo of a multi-tenant CI / Bazel Remote Execution control plane in
front of [Agent Substrate](https://github.com/agent-substrate/substrate). The
two properties the demo proves are **multi-tenant isolation** (one tenant
cannot read another's instance) and **optimized caching** (a content-addressed
blob warmed by one tenant is served to another from a node-local verified
cache, with no second origin fetch).

Images are built and applied with [ko](https://ko.build/). There are no
Dockerfiles and no Helm charts.

## What runs

| Binary | Role |
|--------|------|
| `cas` | Authoritative multi-tenant CAS + action cache. Speaks the Bazel Remote Execution API (`ContentAddressableStorage`, `ActionCache`, `ByteStream`, `Capabilities`) over gRPC. |
| `cascache` | Node-local, read-only CAS proxy (DaemonSet, `hostNetwork`, port 9092). Verified read-through cache in front of `cas`. |
| `runner` | In-actor build runner. Prefetches inputs from `cascache`, checks the action cache, executes on a miss, uploads outputs. |
| `cictl` | Demo driver. Uploads a shared blob as tenant A, warms the cache, reads it as tenant B, and asserts tenant B cannot touch tenant A's private instance. |

Tenant identity is a token on the `x-ci-substrate-tenant` gRPC metadata header.
Each token is allowed a set of Remote Execution instance names. Blobs are
content addressed and shared; action results are namespaced by instance.

## Milestone map

| Milestone | In this demo |
|-----------|--------------|
| M1 Control plane state | Job and tenant state live in the CAS/action-cache process, not Kubernetes CRDs. No Postgres or Redis yet; an in-memory action cache is enough for the demo. |
| M2 Substrate lifecycle | Actor templates and egress policies live under `deploy/substrate/`. The default kind e2e does not install Substrate; see that directory's README for the overlay. |
| M3 Artifact push | `runner` uploads stdout/stderr digests and writes the action cache after exit. |
| M4 Bazel RBE API | `cas` implements the CAS, ActionCache, ByteStream, and Capabilities services from `bazelbuild/remote-apis`. Execution (`Execute`/`WaitExecution`) is not wired yet; the runner drives the same data plane locally. |
| M5 Node-local CAS + verification | `cascache` is the node-local proxy. Every served blob is SHA-256-verified in flight; a poison is dropped and the request falls back to the origin. The production FUSE lazy-hydration guest daemon is modeled by this verified read-through path. |
| M6 Output handling | `remote.Client.Upload` routes blobs under 4 MiB through `BatchUpdateBlobs` and larger ones through `ByteStream.Write`. `FindMissingBlobs` skips content the CAS already holds. |

## Local unit tests

```bash
cd ci-substrate
go test ./...
go test -race ./...
```

The `internal/remote` package includes an in-process gRPC integration test that
covers cross-tenant cache reuse, isolation, poison rejection, large-blob
ByteStream, and action-cache isolation without needing a cluster.

## KinD end-to-end

Requires Docker. The script installs `kind`, `ko`, and `kubectl` when they are
missing, creates a cluster with a local registry, and deploys with `ko apply`:

```bash
cd ci-substrate
CI_SUBSTRATE_KIND_E2E=1 go test -race -v -timeout 20m ./e2e/
```

Or run the script directly:

```bash
bash e2e/run-kind.sh
```

Set `CI_SUBSTRATE_KIND_KEEP=1` to leave the cluster up afterwards.

The script drives `cictl` from the host over `kubectl port-forward`, so the
demo does not depend on ClusterIP routing (some nested kind environments
cannot program kube-proxy iptables rules). What it asserts:

1. Tenant A uploads a shared blob to `cas`.
2. Tenant A reads it through `cascache` (cold: one origin fetch).
3. Tenant B reads the same content through `cascache` (warm: local hit).
4. Tenant B is `PermissionDenied` on tenant A's private instance.
5. Cache `/stats` reports at least one hit.

`deploy/30-cictl-job.yaml` is the same demo as an in-cluster Job for clusters
where Service DNS works.

## Deploy with ko

```bash
export KO_DOCKER_REPO=<your-registry>/ci-substrate
kubectl apply -f deploy/00-namespace-and-config.yaml
ko apply -f deploy/10-cas.yaml
ko apply -f deploy/20-cascache.yaml
ko apply -f deploy/30-cictl-job.yaml
```

On an egress-restricted host that cannot reach `cgr.dev`, point ko at the
docker.io mirror of the same static base:

```bash
export KO_DEFAULTBASEIMAGE=registry-1.docker.io/chainguard/static:latest
```

## Substrate overlay

When Agent Substrate is installed in the cluster, apply the templates under
`deploy/substrate/` to run the `runner` inside a gVisor actor whose egress
policy reaches only the node-local cascache and the central cas. The default
kind e2e does not install Substrate. Building Substrate's envoy dataplane from
source needs open Debian apt egress; use Substrate's published images or a
machine with unrestricted egress for that install.

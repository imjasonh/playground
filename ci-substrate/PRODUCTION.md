# Production RBE capabilities and roadmap

This guide describes the Bazel Remote Execution (RBE) and Build Event Service
(BES) features that `ci-substrate` supports, how to enable them from Bazel, and
the remaining gaps to close before running `ci-substrate` as a large-scale
production cluster.

## Supported RBE features

### Build Event Service (BES), Build Metrics, coverage, and JSON tracing

The `cas` server implements `google.devtools.build.v1.PublishBuildEvent`
(`PublishLifecycleEvent` and `PublishBuildToolEventStream`) on the same gRPC
port as REAPI.

When you stream BEP events to `cas`, the server:

- Authorizes every stream using the `x-ci-substrate-tenant` header and the
  `project_id` (`--bes_instance_name`), isolating records by tenant.
- Indexes `BuildStarted`, `BuildFinished`, `BuildMetrics` (action counts,
  package and target counts, analysis/execution/wall/CPU timings, peak post-GC
  JVM heap size, and host network bytes), `TestResult` summaries, coverage
  artifact references (`coverage.dat`, `*.lcov`), and `BuildToolLogs` including
  JSON trace profiles (`command.profile.gz`).
- Persists each invocation summary to `${STORE_DIR}/bes/` and records
  `bazel.bep.*` OpenTelemetry metrics and a `bes.invocation` span in the
  build's trace.
- Closes the server-side invocation immediately on `BuildFinished` instead of
  waiting for `INVOCATION_IDLE`.
- Serves tenant-authorized JSON invocation summaries at
  `GET /invocations/<INVOCATION_ID>` when `HTTP_ADDR` is configured on `cas`.

Configure Bazel to stream BEP, upload JSON trace profiles, and publish memory
metrics:

```bash
bazel test //... \
  --remote_executor=grpc://<CAS_ADDR> \
  --remote_instance_name=<INSTANCE> \
  --remote_header=x-ci-substrate-tenant=<TOKEN> \
  --bes_backend=grpc://<CAS_ADDR> \
  --bes_instance_name=<INSTANCE> \
  --bes_header=x-ci-substrate-tenant=<TOKEN> \
  --bes_results_url=http://<CAS_HTTP_ADDR>/invocations/ \
  --profile=command.profile.gz
```

Query a recorded invocation over HTTP:

```bash
curl -H "x-ci-substrate-tenant: <TOKEN>" \
  "http://<CAS_HTTP_ADDR>/invocations/<INVOCATION_ID>"
```

For Bazel's client-side JSON trace profile (`--profile=command.profile.gz`),
the scheduler and runner populate every `ExecutedActionMetadata` stage
timestamp (`queued`, `worker_start/completed`, `input_fetch_start/completed`,
`execution_start/completed`, `output_upload_start/completed`) and
`virtual_execution_duration`. The runner also attaches POSIX `getrusage(2)`
metrics (`user_seconds`, `system_seconds`, `max_rss_bytes`, `inblock`,
`oublock`) to its `runner.execute` OpenTelemetry span.

### Transfer compression (Zstd and Deflate)

Both `cas` and `cascache` support `Compressor.ZSTD` and `Compressor.DEFLATE` on
ByteStream (`compressed-blobs/{zstd,deflate}/...`) and `BatchReadBlobs` /
`BatchUpdateBlobs`, and `GetCapabilities` advertises both compressors.

Enable wire compression in Bazel:

```bash
bazel build //... --remote_cache_compression
```

### Streaming ByteStream I/O and LRU cache eviction

- `cas` streams `ByteStream.Read` and `ByteStream.Write` directly to and from
  disk in chunks while computing SHA-256 digests, avoiding full-blob memory
  buffering for large artifacts.
- Set `CAS_MAX_BYTES` on `cas` or `CACHE_MAX_BYTES` on `cascache` to enable
  size-bounded least-recently-used (LRU) eviction (evicting down to 85% of the
  configured limit).
- Set `MAX_CAS_BLOB_SIZE_BYTES` on `cas` to cap the largest single blob upload
  and advertise `CacheCapabilities.max_cas_blob_size_bytes`.

### ActionCache completeness, inlining, and read-only tokens

- **Completeness verification:** Both `GetActionResult` and `Execute` verify
  that every output file, output directory (`tree_digest` and
  `root_directory_digest`), stdout, and stderr blob referenced by a cached
  `ActionResult` still exists in CAS before returning a cache hit. Evicted CAS
  blobs trigger a clean cache miss instead of a broken build.
- **Inlining:** `GetActionResult` honors `inline_stdout`, `inline_stderr`, and
  `inline_output_files` for blobs up to 1 MiB.
- **Read-only ActionCache tokens:** In the `TENANTS` JSON configuration, you
  can grant developer tokens read access to an instance while denying
  `UpdateActionResult` and Remote Asset `Push` calls (and advertising
  `action_cache_update_capabilities.update_enabled = false` in
  `GetCapabilities`) so workstations cannot poison CI-populated caches:

```json
{
  "tok-ci": ["tenant-a"],
  "tok-dev": {"instances": ["tenant-a"], "action_cache_read_only": true}
}
```

### Build without the Bytes (BwoB) and `CAS.GetTree`

- `cas` implements paginated streaming `ContentAddressableStorage.GetTree`.
- The runner uploads every output `Directory` proto individually and sets both
  `OutputDirectory.tree_digest` and `OutputDirectory.root_directory_digest`,
  supporting Bazel's `--remote_download_minimal` and
  `--remote_download_toplevel` modes.

### Scheduling, cancellation, and action timeouts

- **Priority scheduling:** `Scheduler` honors
  `ExecuteRequest.execution_policy.priority` (lower values are more urgent,
  with FIFO ordering among equal priorities) and advertises `[-1000, 1000]` in
  `ExecutionCapabilities.execution_priority_capabilities`.
- **Operations API:** `cas` registers `google.longrunning.Operations`
  (`GetOperation` and `CancelOperation`), scoped by tenant. Cancelling a
  running operation signals `Cancelled=true` on the runner's next heartbeat.
- **Timeouts and process-tree cleanup:** Every action runs in its own POSIX
  process group (`setpgid`). On `Action.timeout` or lease cancellation, the
  runner terminates the entire process group so grandchild processes do not
  leak. When an action times out, the runner still uploads partial stdout,
  stderr, and declared outputs, and the scheduler returns
  `codes.DeadlineExceeded` with the partial `ActionResult` without caching it.

### Remote Asset API and Remote Logstream API

- **Remote Asset API (`build.bazel.remote.asset.v1`):** `cas` implements
  tenant-isolated `Fetch` (`FetchBlob`, `FetchDirectory`) and `Push`
  (`PushBlob`, `PushDirectory`) backed by `${STORE_DIR}/asset/` and CAS
  existence checks, supporting Bazel's `--experimental_remote_downloader`.
- **Remote Logstream API (`build.bazel.remote.logstream.v1`):** `cas`
  implements `CreateLogStream` with separate read and write resource names and
  live tailing over `ByteStream.Read` and `ByteStream.Write`.

### Optional TLS and mTLS transport security

Set certificate environment variables on `cas` and `cascache`, or flags on
`runner`, to enable TLS 1.3 or mutual TLS (mTLS):

| Component | Configuration |
|---|---|
| `cas` | `TLS_CERT_FILE`, `TLS_KEY_FILE`, `TLS_CLIENT_CA_FILE` |
| `cascache` | Server: `TLS_CERT_FILE`, `TLS_KEY_FILE`, `TLS_CLIENT_CA_FILE`; Origin client: `ORIGIN_TLS`, `ORIGIN_TLS_CA_FILE`, `ORIGIN_TLS_CERT_FILE`, `ORIGIN_TLS_KEY_FILE` |
| `runner` | `-tls`, `-tls-ca-file`, `-tls-cert-file`, `-tls-key-file` |

When unset, components default to plaintext for local and KinD development.

---

## Remaining roadmap for future efforts

The following production RBE capabilities are not yet implemented and are
tracked for future work.

### Storage, high availability, and scaling

- **Replicated and sharded CAS / ActionCache:** `cas` runs as a single
  StatefulSet replica on one PVC. Production deployments need horizontal
  sharding, replication, and a tiered backend (such as local NVMe hot tier over
  GCS or S3, plus Redis or PostgreSQL for ActionCache and metadata).
- **Durable distributed scheduler queue:** Queued and executing job state lives
  in memory inside `cas`, so a `cas` restart drops in-flight operations.
  Persisting scheduler state (or running a replicated scheduler) avoids
  re-running builds during control-plane rollouts.
- **Disk-backed writable upper layer for `casfs`:** Writes inside a `casfs`
  exec root live in memory (bounded by the `casfs-csi` pod memory limit on the
  Substrate path). Large outputs or coverage dumps (`.profraw`) need a
  disk-backed scratch upper layer.
- **CAS blob lease renewal for BwoB:** Under aggressive LRU eviction,
  long-running builds using `--remote_download_minimal` need blob TTL extension
  on `FindMissingBlobs` and `GetActionResult` so intermediate outputs are not
  evicted before downstream actions read them.
- **FastCDC chunking (`SplitBlob` and `SpliceBlob`):** Chunk-level
  deduplication for large binaries and container images is not yet implemented.

### Execution environments and scheduling

- **Platform property routing and heterogeneous worker pools:** `Scheduler`
  routes jobs only by `instance_name` and ignores `Action.platform` /
  `Command.platform` properties (`OSFamily`, `Arch`, CPU/RAM/GPU, pool tags).
- **Per-action container images (`container-image`):** Actions execute inside
  the runner's own `chainguard/bash` image rather than pulling and running an
  action-specified container image (which also limits C/C++, Java, and
  multi-toolchain `bazel coverage` runs).
- **Persistent and multiplexed workers:** Every action spawns a fresh `bash`
  process. Supporting Bazel persistent worker daemons across actions speeds up
  JVM, Kotlin, and TypeScript builds.
- **Per-action cgroup resource enforcement and max timeout cap:** Enforcing CPU
  and memory limits per action (beyond pod or actor boundaries) and capping
  `Action.timeout` via server configuration.
- **Speculative / hedged execution and transient error retries:** Retrying
  known transient runner failures and hedging straggler actions.

### Protocol extensions

- **Additional digest functions:** Only `SHA256` is supported; `BLAKE3` and
  `SHA256TREE` are not yet implemented.
- **Absolute symlinks and `NodeProperties`:** `SymlinkAbsolutePathStrategy` is
  `DISALLOWED`, and file `NodeProperties` (mtime, custom POSIX mode bits beyond
  executable) are not preserved.
- **Server-side Remote Asset origin fetching:** `FetchBlob` and
  `FetchDirectory` currently serve previously pushed assets and return
  `NotFound` on misses rather than fetching upstream HTTP/Git URLs from the
  server side.
- **Automatic action log streaming:** `cas` serves the Remote Logstream API,
  but `runner` does not yet automatically stream live stdout/stderr into a
  `LogStream` during execution.

### Observability, UI, and coverage visualization

- **BES web UI and search:** `cas` exposes a JSON API at `/invocations/{id}`,
  but has no web UI for browsing build history, streaming build logs, viewing
  interactive Chrome trace profiles (`command.profile.gz`), inspecting test XML
  failures, or rendering line-by-line coverage diffs and trends.
- **Standardized `POSIXResourceUsage` auxiliary proto:** Runner `getrusage(2)`
  metrics are exported to OpenTelemetry spans, but are not yet packed into a
  Buildbarn-compatible `POSIXResourceUsage` `Any` message in
  `ExecutedActionMetadata.auxiliary_metadata`.

### Security and multi-tenancy

- **OIDC / JWT authentication and RBAC:** Tenant auth uses static tokens loaded
  from a Secret rather than short-lived OIDC/JWT tokens or mTLS identity
  mapping.
- **Per-tenant quotas, rate limits, and fair-share scheduling:** No bandwidth,
  storage, or concurrent-execution quotas per tenant, and no fair-share
  queuing across instances sharing a runner fleet.
- **Cross-tenant CAS existence oracle mitigation:** Because CAS blobs are
  shared globally by SHA-256 digest, `FindMissingBlobs` reveals whether another
  tenant previously uploaded a known hash. Strict multi-tenant environments
  that require hiding blob existence need per-tenant presence indexes or
  tenant-salted CAS namespaces.

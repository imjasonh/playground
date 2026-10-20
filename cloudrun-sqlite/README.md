# cloudrun-sqlite

A SQLite database for a Cloud Run service whose only durable copy is a
[Litestream](https://litestream.io) replica in Cloud Storage or S3. The
service reads pages on demand through the
[Litestream VFS](https://litestream.io/guides/vfs/), so a cold start reads the
replica's index instead of downloading the database. Writes go into the same
replica before the request returns.

This revives the
[`terraform-playground/litestream`](https://github.com/imjasonh/terraform-playground/tree/main/litestream)
experiment. Its first version restored the whole database on every cold
start. Its second version used the VFS, and stopped at
[benbjohnson/litestream#1018](https://github.com/benbjohnson/litestream/issues/1018).

## The VFS write bug

Sustained writes through the write-enabled VFS corrupt the database. SQLite
reports `database disk image is malformed`, and the process stays broken
until it restarts. As of October 20, 2026, the issue is still open, and the
fixes are split between `main` and an unmerged pull request.

The program in [`repro/`](repro/) opens one connection with
`_busy_timeout=5000` and a 1-second sync interval, runs an insert and a
`count(*)` in a loop for the stated time, then runs `integrity_check` in the
writer and from a fresh VFS. These are its results against each version:

| Litestream | 30 s, 1 writer | 60 s, 10 writers | 130 s, 4 writers, compaction on | 90 s, 4 writers, L1 every 1 s, polls every 3 s |
|---|---|---|---|---|
| v0.5.7 (the earlier attempt) | malformed after 2 s | malformed after 1 s | not run | not run |
| v0.5.17 (latest release) | malformed after 6 s | malformed after 1 s | not run | not run |
| `main` at `716acc5` | corrupt pages, 629 acknowledged rows lost | replica itself corrupt | not run | not run |
| [#1293](https://github.com/benbjohnson/litestream/pull/1293) alone | pass | pass | malformed after 16 s | not run |
| `main` + #1293 | pass | pass | pass | malformed in 5 of 6 runs, after 6-27 s |
| `main` + #1293 + shrink check | pass | pass | pass | pass in 6 of 6 runs |
| `main` + #1293 + both shrink fixes ([`litestream/`](../litestream)) | pass | pass | pass | pass in 6 of 6 runs |

The 60-second, 10-writer run gives the same results on S3, using MinIO behind
the latency proxy described in [Measurements](#measurements). v0.5.7,
v0.5.17, and `main` fail, and #1293 alone and `main` + #1293 pass.

The last column needs two L1 compactions between polls, which the earlier
runs never had. A poll that finds two new L1 files reads the older one's
smaller commit as a shrink and drops every page the two files don't contain.
`main` has the same bug.

A transaction that really does shrink the database hits a separate bug,
which `main` also has. With `auto_vacuum`, a `DELETE` truncates the database
and writes only the pages it changes. A poller that finds the smaller commit
replaces its page index with that file's pages, so every page the `DELETE`
didn't write disappears, and another instance's next query fails with
`database disk image is malformed`. The writer's own file size and a cold
start's page index also keep pages past the new end.
`TestShrinkIsVisibleToAnotherInstance` reproduces it with two instances.

This repository carries those fixes in [`litestream/`](../litestream), a
fork of Litestream imported with `git subtree`, and `go.mod` replaces
Litestream with it. Its [`PATCHES.md`](../litestream/PATCHES.md) lists each
patch, explains which race it fixes, and shows how to send it upstream. A
nightly workflow pulls upstream into the fork and merges the update when the
tests pass. Drop a patch once Litestream ships it.

## How it works

**Reads.** SQLite reads pages through the VFS, which serves each one from
this instance's own writes, an LRU page cache (64 MiB), an optional local
copy that it downloads in the background (`HYDRATE=true`), or a ranged GET of
the LTX file that holds the page. A read waits while a durable write commits
and uploads, so it sees only writes that are in the replica. With
`DURABLE=false`, reads also see writes that the VFS hasn't uploaded yet.

**Writes.** Every request's transaction runs on one goroutine. Writes that
arrive while one is committing share the next transaction, then the store
uploads the changed pages as one L0 file before any of those requests return.
With `DURABLE=false`, requests return after the local commit and the VFS
uploads every second instead.

**Cold starts.** Opening the database lists the replica and reads the header
and page index of each file in the restore plan, the newest snapshot plus the
files written after it. The store fetches those in parallel before the VFS
asks for them one at a time. The VFS compacts L0 files into L1, L2, and L3
files, and the store merges the plan into a new snapshot when it grows past
16 files, then deletes files that the previous snapshot covers.

**Overlapping instances.** Cloud Run can run two instances of a
`max_instance_count = 1` service for a short time, for example during a
deploy. The store uploads L0 files with a conditional create
(`If-None-Match: *` on S3, `DoesNotExist` on Cloud Storage, `link(2)` on a
local directory). If another instance already published that transaction, the
upload fails, the store discards its local commit, reopens the database, and
reruns the batch. Reads on that instance wait until the commit is gone,
because the row IDs it took belong to the other instance's writes. Any failed
upload makes the store reopen the database from the replica this way. If the
open fails too, requests get a 503 until a later read or write opens it.

**Shutdown.** On SIGTERM the server stops accepting requests, finishes the
ones in flight, uploads anything left, and exits. Cloud Run sends SIGKILL 10
seconds after SIGTERM.

## Measurements

These numbers come from this repository's Cloud Run simulator (`cmd/crsim`)
running against MinIO behind `cmd/latproxy`, which adds 20 ms to each GET,
30 ms to each LIST, and 50 ms to each PUT (plus or minus 25%), and caps each
download at 100 MB/s. Those are guesses at Cloud Storage from Cloud Run in
the same region; check them against a real deployment.

### Cold start versus database size

`crbench coldstart` seeds a database of 1,000-byte rows as one snapshot,
then repeats five times: stop the instance, send `GET /items/{random id}`,
then send 200 more random reads. "Full restore" is how long Litestream takes
to download the same database, which the original sidecar version did before
it could listen.

"Start to listen" runs from process start until the port accepts
connections, which is when Cloud Run's default startup probe passes. "First
request" runs from a request arriving at a service with no instance until its
response, so it includes starting the process.

| Database | Start to listen | First request | Random read p50 / p99 | Full restore |
|---:|---:|---:|---:|---:|
| 10 MiB | 216 ms | 288 ms | 23.6 / 49.4 ms | 0.8 s |
| 98 MiB | 225 ms | 297 ms | 25.6 / 54.2 ms | 1.8 s |
| 979 MiB | 363 ms | 457 ms | 49.0 / 61.1 ms | 11.3 s |
| 3.8 GiB | 898 ms | 1.0 s | 58.6 / 83.7 ms | 42.7 s |

The open is 89 ms of that at 10 MiB and 760 ms at 3.8 GiB. The growth is the
snapshot's page index, one entry per page, which the VFS downloads and
decodes before it serves anything. Before the store prefetched the open's
requests, the first request took 601 ms at 10 MiB and 1.3 s at 3.8 GiB.
Random reads miss the cache on a large database, and each miss is a GET.

### Writes and reads under failures

`crbench soak` runs 8 writers and 8 readers for 90 seconds with CPU frozen
between requests (request-based billing), while the simulator SIGKILLs the
instance every 20 seconds, stops it with SIGTERM every 15 seconds, and
deploys a new revision every 25 seconds with 3 seconds where both revisions
serve. Afterward it restarts the service from nothing and reads back every
acknowledged write.

| Mode | Acknowledged writes | Write p50 / p99 | Read p50 / p99 | Lost after restart | `integrity_check` |
|---|---:|---:|---:|---:|---|
| Durable (default) | 3,671 | 121 / 1,759 ms | 62 / 911 ms | 0 | ok |
| `DURABLE=false` | 62,025 | 1.8 / 380 ms | 1.1 / 216 ms | 306 | ok |

The p99 latencies include waiting for a new instance after each kill or
stop, 12 times in 90 seconds. In the two runs, 64 and 63 requests failed
with a 502 because their instance was killed mid-request; the client can't
tell whether those writes happened. With `DURABLE=false`, every kill loses
the writes from the last second that were acknowledged but not yet uploaded,
and the next instance hands out their IDs again.

### Steady state

With no failures injected, for 60 seconds:

| Workload | Write p50 / p99 | Read p50 / p99 | Writes per second |
|---|---:|---:|---:|
| 8 writers and 8 readers, durable | 111 / 135 ms | 56 / 68 ms | 71 |
| 1 writer and 1 reader, durable | 56 / 68 ms | 52 / 68 ms | 18 |
| 1 writer at 5 writes per second and 8 readers, durable | 56 / 69 ms | 0.3 / 1.6 ms | 5 |
| 8 writers and 8 readers, `DURABLE=false` | 1.9 / 7.1 ms | 1.0 / 8.7 ms | 1,899 |

A durable write costs one upload, a conditional put. The writer lists the
replica for a newer transaction first only when it hasn't confirmed its
position for half of `L0Retention`, 2.5 minutes by default; the conditional
put catches another writer the rest of the time. With a list request before
every put, writes took 188 / 220 ms with 8 writers and 93 / 114 ms with one;
[`docs/improvements.md`](docs/improvements.md#skip-the-conflict-check-list)
explains why skipping it is safe. Reads are fast until uploads run back to
back, because a read waits for the write that is committing or uploading.
Before reads waited for whole writes, the 8-writer run's reads took
104 / 560 ms: a read could take the one connection between a commit and its
upload, then hold it until the upload finished while other reads queued
behind it.

`crbench live` runs that workload against a service that is already
running, instead of MinIO and the latency proxy. `-roll` deploys a new
Cloud Run revision before the read-back, so a new instance has to serve
the acknowledged writes from the replica.

```bash
go build -tags vfs -o crbench ./cmd/crbench
./crbench live -url https://SERVICE.run.app -duration 1m \
  -roll -project PROJECT -region us-central1 -service cloudrun-sqlite
```

Client latencies include the network to Cloud Run. The command also prints
`/stats` from the instance that served the load: time waiting on an upload,
the SQLite transaction, acknowledged writes, paged-in and cold page reads,
and replica GET, LIST, and PUT. On Cloud Run those spans and histograms
also go to Cloud Trace and Cloud Monitoring; see
[Observability](#observability).

### Deployed service

These numbers are from Cloud Run and Cloud Storage in `us-central1` on
October 20, 2026. The client was not in the same region. Server columns are
from `/stats`. The simulator's 50 ms PUT was 78 ms here. SQLite was under 1
ms. A durable write is that PUT.

| Workload | Client write p50 / p99 | Client read p50 / p99 | Server PUT p50 | Writes per second |
|---|---:|---:|---:|---:|
| 1 writer and 1 reader, 30 s | 124 / 286 ms | 113 / 223 ms | 78 ms | 7.5 |
| 8 writers and 8 readers, 60 s | 163 / 330 ms | 82 / 211 ms | 77 ms | 46 |

With one writer, reads waited on the upload in progress (server wait p50 59
ms, query 0.2 ms). Eight writers shared uploads, about 3 writes per batch,
and reads waited 25 ms at the median. All 2,787 acknowledged writes from the
8-writer run were readable from the next revision: none missing, none
mismatched.

A cold open after that run, with no snapshot yet, read 734 objects and took
1.6 s. There were 936 L0 files. The snapshot check is now 15 seconds. The
next busy period wrote two snapshots, and the following cold open took 682
ms. Reading that backlog into the first snapshot stalled requests for up to
9 s. Replica GETs were 35 ms at the median once the instance was warm, and
65 to 76 ms while opening. The latency proxy assumed 20 ms.

### Background requests

Polling, compaction, and retention list the replica on timers while an
instance has CPU. An idle instance made 18 object-store requests a minute with
the defaults (a 30-second poll and Litestream's compaction intervals), and 130
a minute with a 1-second poll. With request-based billing, an idle instance's
CPU is frozen and it makes none.

## Limits

- One SQLite connection serves every request, so a slow query delays
  everything behind it. In durable mode, a read also waits for the write
  that is committing or uploading, which adds up to one upload's time to
  reads that arrive during a write.
- A page that isn't cached costs one object-store round trip. A query that
  scans a large table on a cold instance is slow until the cache or the
  hydrated copy has the pages. Hydration needs memory for the whole database
  on Cloud Run, where the filesystem is in memory.
- Opening the database still decodes the snapshot's page index into a map
  that stays in memory. Each GiB of database adds about 170 ms to the open and
  75 MiB of memory: an instance used 81 MiB after opening a 10 MiB database,
  156 MiB for 979 MiB, and 372 MiB for 3.8 GiB.
- With `DURABLE=false` and constant writes, an instance peaked at 457 to
  488 MiB. Durable instances peaked at 106 to 126 MiB in every run.
- With request-based billing, Cloud Run throttles CPU between requests, so
  compaction and snapshots only make progress while requests are in flight.
  Set `cpu_always_allocated = true` if cold starts slow down because the
  restore plan grew.
- `Write` runs each function inside a transaction, so it can't run `VACUUM`,
  which SQLite doesn't allow there.

[`docs/improvements.md`](docs/improvements.md) lists changes that make writes
faster and cheaper, which of them are done, their measured benefits, reasons
not to make each one, and what each needs to stay correct.

## Run locally

Build the server and point it at a local directory. Litestream builds its
VFS only with the `vfs` tag:

```bash
go build -tags vfs -o cloudrun-sqlite .
./cloudrun-sqlite -replica-url file://$PWD/replica
```

Open <http://localhost:8080/>, or use the JSON endpoints:

```bash
curl -X POST --data 'hello' localhost:8080/items   # {"id":1}
curl localhost:8080/items/1                        # {"body":"hello","id":1}
curl localhost:8080/stats
```

To use S3 or a local MinIO instead, set credentials in the environment and
pass an `s3://` URL:

```bash
export AWS_ACCESS_KEY_ID=minioadmin AWS_SECRET_ACCESS_KEY=minioadmin
./cloudrun-sqlite -replica-url 's3://BUCKET/db?endpoint=http://127.0.0.1:9000&region=us-east-1&forcePathStyle=true'
```

The server reads these environment variables:

| Variable | Default | Meaning |
|---|---|---|
| `REPLICA_URL` | none | `gs://`, `s3://`, or `file://` replica URL |
| `PORT` | `8080` | listen port |
| `DATA_DIR` | `$TMPDIR/cloudrun-sqlite` | write buffer and hydrated copy |
| `DURABLE` | `true` | acknowledge writes only after they are uploaded |
| `HYDRATE` | `false` | download the whole database in the background |
| `CACHE_SIZE` | `67108864` | page cache size in bytes |
| `SNAPSHOT_PLAN_LEN` | `16` | snapshot when a cold start would read more files (`0` disables) |
| `POLL_INTERVAL` | `30s` | how often to list the replica for compacted files or another instance's writes |
| `ADMIN_TOKEN` | none | bearer token that enables `/admin/check` and `/admin/snapshot` |

`seed` replaces a replica with a generated database, for benchmarks:

```bash
./cloudrun-sqlite seed -replica-url file://$PWD/replica -rows 1000000 -force
```

## Simulate Cloud Run

`crsim` starts the server when a request arrives, gives each instance a fresh
`TMPDIR`, stops idle instances with SIGTERM and then SIGKILL, and can freeze
instances between requests:

```bash
go build -o crsim ./cmd/crsim
./crsim -listen :8080 -idle-timeout 30s -throttle -env REPLICA_URL=file://$PWD/replica -- ./cloudrun-sqlite
curl -X POST 'localhost:8080/_crsim/deploy?overlap=5s'   # new revision; both serve for 5 s
curl -X POST localhost:8080/_crsim/crash                 # SIGKILL
curl -X POST localhost:8080/_crsim/scale-to-zero         # SIGTERM
curl localhost:8080/_crsim/stats
```

`crbench` drives the server through the simulator:

```bash
go build -tags vfs -o crbench ./cmd/crbench
./crbench coldstart -app ./cloudrun-sqlite -replica-url file://$PWD/bench -rows 10000,100000
./crbench soak -app ./cloudrun-sqlite -replica-url file://$PWD/soak -duration 1m -throttle
```

To reproduce the measurements, run MinIO behind `latproxy` and point
`crbench` at the proxy. MinIO publishes source only, so build it with
`go install`:

```bash
GOBIN=$PWD/bin go install github.com/minio/minio@latest github.com/minio/mc@latest
MINIO_ROOT_USER=minioadmin MINIO_ROOT_PASSWORD=minioadmin ./bin/minio server /tmp/minio --address 127.0.0.1:9000 &
./bin/mc alias set local http://127.0.0.1:9000 minioadmin minioadmin && ./bin/mc mb local/bench
go run ./cmd/latproxy -listen 127.0.0.1:9100 -target http://127.0.0.1:9000 &

export AWS_ACCESS_KEY_ID=minioadmin AWS_SECRET_ACCESS_KEY=minioadmin
./crbench coldstart -app ./cloudrun-sqlite \
  -replica-url 's3://bench/cold?endpoint=http://127.0.0.1:9100&region=us-east-1&forcePathStyle=true' \
  -env AWS_ACCESS_KEY_ID=minioadmin -env AWS_SECRET_ACCESS_KEY=minioadmin
```

## Deploy

The Terraform in `terraform/` creates a bucket, a service account that can
use only that bucket, and a Cloud Run service limited to one instance. It
builds the image with [`ko`](https://ko.build). The build needs CGO; by
default it cross-compiles with [zig](https://ziglang.org).

```bash
cd terraform
cp terraform.tfvars.example terraform.tfvars   # set project_id
terraform init
terraform apply
```

It also creates a Cloud Monitoring dashboard of the latencies in
[Observability](#observability); `terraform output dashboard_url` prints its
link.

## Observability

The server times writes, reads, and object-storage calls as histograms:

| Histogram | Labels | What it times |
|---|---|---|
| `store.write` | `durable`, `result` | A write from the call to its acknowledgement. A durable write includes its upload. |
| `vfs.page_read` | `source`: `paged_in` or `cold` | One SQLite page read through the VFS. A `paged_in` page came from memory (pages this instance wrote, or the page cache) or the hydrated copy; a `cold` one came from object storage. |
| `replica.operation` | `op`: `get`, `list`, or `put` | One object-storage call. |
| `store.phase` | `phase` | One part of a read or write: `read_wait`, waiting for a write in progress; `read_query`; `write_queue`; `tx`, the SQLite transaction; and `flush`, the upload. |
| `http.server` | `route` | A request's time in the server. |

SQLite reads each page through its own page cache first, so
`vfs.page_read` counts only the reads that reach the VFS.

You can see them in three places:

- `/stats` reports recent percentiles from the instance that answers.
- `/metrics` serves the histograms in the Prometheus text format, with dots
  in names replaced by underscores and `_seconds` appended: for example,
  `vfs_page_read_seconds`.
- On Cloud Run they also go to Cloud Monitoring as
  `workload.googleapis.com/NAME`, every 30 seconds, and requests and store
  operations go to Cloud Trace as spans. The dashboard that Terraform creates
  charts durable write latency, page read latency split into paged in and
  cold, object-storage latency, read latency, and write latency by phase.

To graph a local run, point [Prometheus](https://prometheus.io/download/)
at `/metrics`:

```bash
cat > prometheus.yml <<'EOF'
scrape_configs:
  - job_name: cloudrun-sqlite
    scrape_interval: 5s
    static_configs:
      - targets: ['localhost:8080']
EOF
prometheus --config.file=prometheus.yml
```

Then graph these queries at <http://localhost:9090>:

```promql
# Durable write latency, p50 and p99
histogram_quantile(0.5, sum by (le) (rate(store_write_seconds_bucket{durable="true",result="ok"}[1m])))
histogram_quantile(0.99, sum by (le) (rate(store_write_seconds_bucket{durable="true",result="ok"}[1m])))

# Page read latency, paged in and cold, p50
histogram_quantile(0.5, sum by (le, source) (rate(vfs_page_read_seconds_bucket[1m])))

# Page reads per second, paged in and cold
sum by (source) (rate(vfs_page_read_seconds_count[1m]))

# Object-storage latency by call, p99
histogram_quantile(0.99, sum by (le, op) (rate(replica_operation_seconds_bucket[1m])))
```

## Test

```bash
go test -tags vfs -race ./...
```

`TestCloudRunLifecycle` builds the server, runs it under the simulator for 25
seconds of crashes, scale-to-zero, and overlapping deploys, and fails if any
acknowledged write is missing afterward. `go test -short` skips it.

The races in [The VFS write bug](#the-vfs-write-bug) show up in the `repro`
runs only after seconds of load, and not on every run. The fork's
`vfs_interleave_test.go` pauses the VFS's polls and compactions at each
storage call and checks every page read, so each race fails
deterministically within milliseconds.
[`PATCHES.md`](../litestream/PATCHES.md#testing) describes how to run the
fork's tests, more random schedules, and the fuzzer.

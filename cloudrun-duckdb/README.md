# cloudrun-duckdb

A DuckDB database for a Cloud Run service whose only durable copy is in
Cloud Storage, with the same scale-to-zero model as
[`cloudrun-sqlite`](../cloudrun-sqlite). Both serve the same click counter,
item API, live updates, and read-only replica, and both acknowledge a write
only after it is in the bucket. This one exists to compare the two, to see
what changes when the engine is DuckDB instead of SQLite, and whether that
is easier, cheaper, or faster to operate.

The short answer is in [Differences from cloudrun-sqlite](#differences-from-cloudrun-sqlite).

## How it works

There is no Litestream for DuckDB, and no way to read a DuckDB file page by
page from object storage while also writing it. So the server keeps a
complete copy of the database on the instance and ships DuckDB's own
write-ahead log (WAL) to the bucket.

**Objects.** The replica is a numbered log and the database files it refers
to:

```
log/<seq>                    one commit: a kind byte, then its payload
base/<seq>-<nonce>.duckdb    a whole database file
```

A `W` entry holds the bytes DuckDB appended to its WAL for that commit. A
`B` entry names a base file, uploaded just before it, that holds the
database as of that commit. Sequence numbers are 16 hex digits, so keys sort
in commit order.

**Writes.** Every request's transaction runs on one goroutine. Writes that
arrive while one is committing share the next transaction. After the commit,
the store reads the bytes DuckDB added to its WAL and uploads them as
`log/<seq+1>` with a conditional create (`ifGenerationMatch=0` in Cloud
Storage, `link(2)` in a local directory). The requests return after that
upload. With `DURABLE=false`, requests return after the local commit and the
store uploads every second instead.

DuckDB has no savepoints, and any error aborts its transaction. When one
request's function fails, the store rolls back the shared transaction and
reruns the others without it.

**Why WAL bytes are enough.** WAL bytes replay only onto the exact file they
were written against. The store configures DuckDB so that nothing but the
store's own `CHECKPOINT` writes the main file:

| Setting | Why |
|---|---|
| `checkpoint_threshold=1TB` | No automatic checkpoints. |
| `enable_optimistic_write=false` | By default, a large insert writes row groups straight into the main file before it commits. With this off, the insert goes to the WAL like any other. |
| `PRAGMA disable_checkpoint_on_shutdown` | Closing the database leaves the file and the WAL as they were, so the store can truncate the WAL and catch up after a conflict without downloading the base again. |
| `autoinstall_known_extensions=false`, `autoload_known_extensions=false`, `enable_external_access=false` | A cold start never downloads an extension, and SQL can't read the instance's files. |

Before each upload, the store hashes the first 12 KiB of the main file,
where DuckDB rewrites a database header on every checkpoint. If the hash
changed or the WAL shrank, DuckDB checkpointed on its own, and the store
uploads a new base instead of a `W` entry. A modification time can't stand
in for the hash, because on Linux it has the kernel tick's resolution, a few
milliseconds.

**Reads.** DuckDB serves every read from the local file and its buffer pool,
so a read makes no object-storage request. A durable read sees only commits
that are in the bucket. Before each commit, the store starts four
transactions on their own connections, and reads use those until the upload
finishes. DuckDB's snapshot isolation hides the commit from them, so reads
neither wait for the upload nor see it early.

**Cold starts.** Opening the database lists `log/` and `base/`, downloads
the newest base, fetches the entries after it 32 at a time, writes them out
as the base's WAL, and opens the file. DuckDB replays the WAL as it opens. The
whole database is downloaded before the first request is served.

**Snapshots.** After each batch, the store estimates what restoring the
entries after the base would cost, in bytes of base download. A restore
fetches 32 entries at a time, so each entry's GET counts as 64 KiB
(`SNAPSHOT_ENTRY_COST`). DuckDB replays about 12,000 small commits a second
as it opens, so each commit counts as 8 KiB. The entries' bytes count once.
When the estimate reaches the base's size, or 128 entries' worth
(`SNAPSHOT_MIN_ENTRIES`) for a small base, the store uploads a new base, so
a cold start never takes much longer than twice the base's download.

A snapshot runs `FORCE CHECKPOINT`, uploads the file, and creates the `B`
entry. Writes wait for the upload; reads continue. At 507 MiB, a snapshot
took 5.2 seconds. It then deletes log entries and bases older than the
previous base, once they are older than 5 minutes.

DuckDB holds a checkpoint lock for any committed transaction that created
something, updated a row, or drew from a sequence, until no transaction that
started before it is still open. So a checkpoint can't run while a pinned
read is open, and the store never takes one inside a durable commit. When the
replica is empty, the first instance publishes an empty base at startup, so
every later commit is a `W` entry.

**Overlapping instances.** Cloud Run can briefly run two instances of a
`max_instance_count = 1` service, for example during a deploy. If another
instance already created `log/<seq+1>`, the upload fails. The store then
closes DuckDB, truncates its WAL to what it had uploaded, appends the entries
it is missing, reopens, and reruns the batch. If the replica has a newer base
than the local file, it downloads that base instead. A writer that hasn't
confirmed its position for half of the 5-minute retention lists the log
before it publishes, so it can't publish an entry that retention deleted.

**Shutdown.** On SIGTERM the server stops accepting requests, finishes the
ones in flight, uploads anything left, and exits.

### Read-only replica

The `cloudrun-duckdb-reader` service runs the same image with
`READ_ONLY=true`. Its service account has `roles/storage.objectViewer`,
DuckDB opens the file with `access_mode=READ_ONLY`, and
`POST /click`, `POST /items`, and `POST /admin/snapshot` return 405.

DuckDB can't replay WAL into an open database. Every `POLL_INTERVAL` (2
seconds in Terraform), the replica lists `log/` after its newest entry. If
there are new `W` entries, it appends them to its local WAL and reopens the
database, which replays the WAL since the base. If one of them is a `B`
entry, it downloads the new base into a fresh directory, opens it, and then
switches to it. Each poll is one LIST request. After each change, it sends
the new count to connected pages.

## Differences from cloudrun-sqlite

The two services have the same API, the same durability, and the same
behavior during crashes, scale to zero, and overlapping deploys. The
[soak](#writes-and-reads-under-failures) loses no acknowledged write in
either. They differ in where the database lives while an instance runs.

| | cloudrun-sqlite | cloudrun-duckdb |
|---|---|---|
| Database on the instance | Pages on demand through the Litestream VFS, plus a 64 MiB cache | The whole file, downloaded at cold start |
| Size of the same rows | 979 MiB for a million 1,000-byte rows | 507 MiB, because DuckDB compresses columns |
| Cold start | Reads the newest snapshot's page index: 0.36 s for a million rows, 0.9 s for four million | Downloads the base: 0.67 s for 100,000 rows, 5.2 s for a million, 20 s for four million |
| Instance memory | 81 MiB at 10 MiB of data, 372 MiB at 3.8 GiB | The process (70 to 150 MiB) plus the whole file, which is in memory on Cloud Run |
| Reads | 24 to 59 ms for a random row that isn't cached; under constant writes, reads wait for the upload in progress | 2 to 3 ms, from memory; reads never wait for an upload |
| Durable write | One conditional PUT of changed pages; SQLite's transaction is under 1 ms | One conditional PUT of WAL bytes; DuckDB's transaction is 2 to 8 ms |
| Writes per second, not durable | 1,899 | 505 |
| Compaction | Litestream merges L0 into L1 to L3 files; snapshot when the restore plan grows | A new base is the whole file. At 507 MiB a snapshot took 5.2 s, and writes waited for it |
| Read-only replica | Applies new LTX files without reopening | Appends WAL and reopens, replaying the WAL since the base; downloads every new base whole |
| Correctness risk | Every Litestream release's write-enabled VFS corrupts databases under sustained writes; this repository carries a fork with patches | DuckDB's own crash recovery, plus three settings that keep the main file unchanged between checkpoints |
| Engine | Row store: fast point reads and writes | Column store: compressed, fast scans and aggregations, slower single-row transactions |
| Build | CGO with C; zig cross-compiles from any host | CGO with DuckDB's C++ library; build on linux/amd64 with gcc (GitHub Actions does). Zig can't link libstdc++ |
| Dependencies | Litestream fork, Cloud Storage and AWS SDKs, OpenTelemetry (575 lines of go.sum) | DuckDB driver and its prebuilt library; a 300-line Cloud Storage client (95 lines of go.sum) |

What that means in practice:

- **Size decides it.** Below about 100 MiB of DuckDB file (about 200,000 of
  these rows), a cold start takes under a second and the instance needs
  little memory, so DuckDB costs about the same to run. Each GiB adds about
  10 seconds to every cold start and a GiB to the instance's memory, and
  Cloud Run bills memory for as long as a request is in flight.
  cloudrun-sqlite's cold start and memory barely grow with size.
- **Durable writes cost about the same.** Both make about one Class A
  request per batch, and the upload is most of a write's latency, 62 ms
  against 56 ms with one writer. DuckDB's slower transactions show under
  load, with 56 durable writes a second against 71, and 505 non-durable
  against 1,899.
- **Reads favor DuckDB once it's running.** A warm DuckDB instance answers
  from memory in 2 to 3 ms and never waits for an upload. SQLite fetches an
  uncached page from the bucket, so a random read on a big database takes
  tens of milliseconds, and a cold scan of a big table is slow.
- **Analytics favor DuckDB.** Aggregating over millions of rows is what
  DuckDB is for. The counter and item lookups here don't need it.
- **Less to maintain, more to own.** There is no Litestream fork to keep
  patched. Instead, this repository owns the replication protocol, about
  1,000 lines in `internal/store`. Its correctness depends on DuckDB
  replaying a WAL onto the exact file it was written against, which is
  DuckDB's crash-recovery path.
- **DuckDB upgrades need care.** Bases and WAL entries are in DuckDB's
  storage format, so every instance must run a DuckDB that reads them.
  During a deploy that changes the DuckDB version, both revisions can run
  at once, and the older binary may not open a file the newer one wrote.
  Test an upgrade against a copy of the replica, then take a snapshot with
  `POST /admin/snapshot`, and don't roll back past it.

### Why not DuckLake or httpfs

DuckDB's own answers to "the data lives in object storage" are the
[httpfs](https://duckdb.org/docs/extensions/httpfs/overview) extension,
which reads a DuckDB or Parquet file in place but can't write a DuckDB file,
and [DuckLake](https://ducklake.select), which stores data as Parquet files
in the bucket and keeps its catalog in a SQL database. DuckLake's catalog is
the same problem again. A DuckDB or SQLite catalog file has to live somewhere
durable, and a Postgres catalog doesn't scale to zero. Each small write also
adds a Parquet file or a row in the catalog, which needs compaction. Both
extensions are downloaded at runtime unless the image includes them; the
prebuilt library that the Go driver links has parquet, json, and icu, but
neither of these.

## Measurements

These numbers come from this repository's Cloud Run simulator (`cmd/crsim`)
running against `cmd/fakegcs` with the same latency model that
cloudrun-sqlite's `latproxy` puts in front of MinIO: 20 ms per GET, 30 ms
per LIST, and 50 ms per upload (plus or minus 25%), and each download capped
at 100 MB/s. `fakegcs` caps uploads at 100 MB/s too, since snapshots here
upload whole files. The cloudrun-sqlite columns are from its README, measured
on a different machine with the same model. The model dominates write and
cold-start latency, but treat small differences as noise. Instance scratch
directories were on tmpfs, as Cloud Run's in-memory volume is.

### Cold start versus database size

`crbench coldstart` seeds a database of 1,000-byte rows of random hex as one
base, then repeats five times: stop the instance, send
`GET /items/{random id}`, then send 200 more random reads. The rows are the
ones cloudrun-sqlite's benchmark writes. DuckDB compresses them to about
half the size SQLite stores.

| Rows | SQLite file | SQLite: start to listen / first request | SQLite: random read p50 / p99 | DuckDB base | DuckDB: start to listen / first request | DuckDB: random read p50 / p99 | DuckDB: process + file in memory |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 10,000 | 10 MiB | 216 / 288 ms | 23.6 / 49.4 ms | 5.8 MiB | 212 / 215 ms | 1.6 / 2.4 ms | 69 + 6 MiB |
| 100,000 | 98 MiB | 225 / 297 ms | 25.6 / 54.2 ms | 51 MiB | 665 / 670 ms | 1.9 / 2.7 ms | 94 + 51 MiB |
| 1,000,000 | 979 MiB | 363 / 457 ms | 49.0 / 61.1 ms | 507 MiB | 5.2 / 5.2 s | 2.0 / 17.5 ms | 121 + 507 MiB |
| 4,000,000 | 3.8 GiB | 898 ms / 1.0 s | 58.6 / 83.7 ms | 2.0 GiB | 20.4 / 20.4 s | 2.1 / 3.7 ms | 151 + 2,026 MiB |

DuckDB's cold start is the download, about 10 seconds per GiB at 100 MB/s.
That is still faster than restoring the same rows with Litestream, which took
11.3 s at 979 MiB and 42.7 s at 3.8 GiB, because the file is compressed and
is one object. But cloudrun-sqlite doesn't restore at all. Once running,
DuckDB answers every read from memory, while SQLite fetches each uncached
page from the bucket. cloudrun-sqlite used 372 MiB at 3.8 GiB; DuckDB needs
memory for the whole file.

### Writes and reads under failures

`crbench soak` runs 8 writers and 8 readers for 90 seconds with CPU frozen
between requests (request-based billing). The simulator SIGKILLs the
instance every 20 seconds, stops it with SIGTERM every 15 seconds, and
deploys a new revision every 25 seconds with 3 seconds where both revisions
serve. Afterward it restarts the service from nothing and reads back every
acknowledged write.

| Mode | | Acknowledged writes | Write p50 / p99 | Read p50 / p99 | Lost after restart | Integrity |
|---|---|---:|---:|---:|---:|---|
| Durable | SQLite | 3,671 | 121 / 1,759 ms | 62 / 911 ms | 0 | ok |
| Durable | DuckDB | 4,844 | 134 / 536 ms | 2.7 / 7.1 ms | 0 | ok |
| `DURABLE=false` | SQLite | 62,025 | 1.8 / 380 ms | 1.1 / 216 ms | 306 | ok |
| `DURABLE=false` | DuckDB | 41,453 | 14.5 / 81 ms | 2.6 / 10.1 ms | 4,887 | ok |

The p99 latencies include waiting for a new instance after each kill or
stop. Durable mode lost nothing in either service. With `DURABLE=false`, a
crash loses the writes since the last upload, up to a second's worth, and the
next instance hands out their IDs again. An overlapping deploy loses more.
Both revisions accept writes, and every second the one that loses the race to
publish discards what it hadn't uploaded. In separate 90-second runs, four
crashes lost 1,562 writes and three deploys lost 4,720. cloudrun-sqlite's
README reports 306 for both together. Its dependencies didn't build where
these measurements ran, so the two haven't run side by side to show where
the difference comes from.

### Steady state

With no failures injected, for 60 seconds. "DuckDB transaction" is the
server's median time for one batch's transaction, from `/stats`.

| Workload | SQLite: write p50 / p99 | SQLite: read p50 / p99 | SQLite: writes/s | DuckDB: write p50 / p99 | DuckDB: read p50 / p99 | DuckDB: writes/s | DuckDB transaction |
|---|---:|---:|---:|---:|---:|---:|---:|
| 8 writers and 8 readers, durable | 111 / 135 ms | 56 / 68 ms | 71 | 138 / 262 ms | 2.9 / 8.6 ms | 56 | 7.6 ms |
| 1 writer and 1 reader, durable | 56 / 68 ms | 52 / 68 ms | 18 | 62 / 111 ms | 1.7 / 2.8 ms | 16 | 2.4 ms |
| 1 writer at 5 writes per second and 8 readers, durable | 56 / 69 ms | 0.3 / 1.6 ms | 5 | 66 / 135 ms | 2.7 / 8.5 ms | 5 | 3.0 ms |
| 8 writers and 8 readers, `DURABLE=false` | 1.9 / 7.1 ms | 1.0 / 8.7 ms | 1,899 | 14 / 71 ms | 2.5 / 7.9 ms | 505 | 6.3 ms |

A durable write costs one upload in both, and the upload is most of it. The
rest is the engine. A DuckDB transaction that inserts one row with a primary
key, a sequence, and `RETURNING` takes 2 to 3 ms, and a batch of about four
takes 6 to 8 ms while readers keep the CPU busy. SQLite's takes under 1 ms.
That caps DuckDB at about 500 writes a second when it doesn't wait for
uploads, a quarter of SQLite's rate.

Reads go the other way. cloudrun-sqlite's reads wait for the write that is
committing or uploading, so under constant writes they take about as long as
an upload. cloudrun-duckdb's reads run against pinned transactions during
uploads and never wait, so they stay at 2 to 3 ms, mostly HTTP. With few
writes, SQLite's 0.3 ms reads beat DuckDB's 2.7 ms.

### Object-storage requests

`crbench` counts `fakegcs` requests. Cloud Storage bills creates and lists as
Class A operations and gets as Class B.

| Workload | Class A per write | Class B per write | Uploaded per minute |
|---|---:|---:|---:|
| 8 writers and 8 readers, durable | 0.26 | 0 | 8.4 MiB |
| 1 writer and 1 reader, durable | 1.04 | 0 | 8.5 MiB |
| Soak with failures, durable | 0.29 | 0.15 | 9.6 MiB |
| 8 writers and 8 readers, `DURABLE=false` | 0.003 | 0 | 23 MiB |

A durable batch is one create, as in cloudrun-sqlite. Snapshots add a few
creates and lists a minute and most of the bytes. At this size a WAL entry is
a few hundred bytes and a base is 1 to 2 MiB. Reads on a warm instance make
no requests; the Class B requests in the soak are cold starts.

## Limits

- The whole database lives on the instance. On Cloud Run that is the
  in-memory volume, so `memory_limit` must cover the database, DuckDB's
  `DUCKDB_MEMORY_LIMIT`, and the Go heap, and `scratch_size_limit` must
  cover the database and its WAL. A read-only replica briefly holds two
  copies while it switches to a new base.
- Cold starts and snapshots take time in proportion to the database's size.
- One goroutine commits every write, and a durable write waits for its
  upload. A snapshot holds up writes for as long as it takes to upload the
  file.
- A read-only replica reopens DuckDB after every poll that finds new
  entries, and replays the WAL since the base each time.
- `/admin/check` scans `items`, which makes DuckDB verify each block's
  checksum, then downloads the replica into a scratch directory and checks
  that it holds at least as many items. DuckDB has no `integrity_check`.
- `/metrics` serves Prometheus histograms with the same names as
  cloudrun-sqlite's. Unlike cloudrun-sqlite, the server doesn't export them
  to Cloud Monitoring or send traces to Cloud Trace.

## Run locally

Build the server and point it at a local directory:

```bash
go build -o cloudrun-duckdb .
./cloudrun-duckdb -replica-url file://$PWD/replica
```

Open <http://localhost:8080/> in two browser tabs and click in one. Both
tabs show the new count. To run a read-only replica beside it, start a
second server on the same replica after the writer:

```bash
./cloudrun-duckdb -replica-url file://$PWD/replica -read-only \
  -port 8081 -dir /tmp/cloudrun-duckdb-reader -poll-interval 1s \
  -writer-url http://localhost:8080/
```

The JSON endpoints are the same as cloudrun-sqlite's:

```bash
curl -X POST --data 'hello' localhost:8080/items   # {"id":1}
curl localhost:8080/items/1                        # {"body":"hello","id":1}
curl localhost:8080/stats
```

To use Cloud Storage from your machine, pass a `gs://` URL and a token:

```bash
export GOOGLE_OAUTH_ACCESS_TOKEN=$(gcloud auth print-access-token)
./cloudrun-duckdb -replica-url gs://BUCKET/db
```

`fakegcs` serves the Cloud Storage JSON API from a directory, optionally
with latproxy's latency model:

```bash
go build -o fakegcs ./cmd/fakegcs
./fakegcs -root /tmp/fakegcs -latency &
./cloudrun-duckdb -replica-url 'gs://bucket/db?endpoint=http://127.0.0.1:9100'
```

The server reads these environment variables:

| Variable | Default | Meaning |
|---|---|---|
| `REPLICA_URL` | none | `gs://` or `file://` replica URL |
| `PORT` | `8080` | listen port |
| `DATA_DIR` | `$TMPDIR/cloudrun-duckdb` | the database file and its WAL |
| `DURABLE` | `true` | acknowledge writes only after they are uploaded |
| `SNAPSHOT_MIN_ENTRIES` | `128` | fewest log entries after a base before a new one (`0` disables) |
| `SNAPSHOT_ENTRY_COST` | `65536` | bytes of base download that one entry's GET is worth |
| `POLL_INTERVAL` | `30s` | how often a read-only replica lists for new entries |
| `DUCKDB_MEMORY_LIMIT` | `256MB` | DuckDB's `memory_limit` |
| `DUCKDB_THREADS` | `2` | DuckDB's `threads` |
| `ADMIN_TOKEN` | none | bearer token that enables `/admin/check` and `/admin/snapshot` |
| `READ_ONLY` | `false` | follow the replica and never write |
| `WRITER_URL` | none | writer's URL, for the read-only page's link |
| `STORAGE_EMULATOR_HOST` | none | Cloud Storage endpoint, such as `fakegcs` |
| `GOOGLE_OAUTH_ACCESS_TOKEN` | none | Cloud Storage token off Google Cloud; on Cloud Run the metadata server provides one |

`seed` replaces a replica with a generated database, for benchmarks:

```bash
./cloudrun-duckdb seed -replica-url file://$PWD/replica -rows 1000000 -force
```

## Simulate Cloud Run

`crsim` and `crbench` are the same tools as cloudrun-sqlite's. `crbench`
also reports object-storage requests per acknowledged write when the replica
is a `fakegcs` server:

```bash
go build -o crsim ./cmd/crsim
go build -o crbench ./cmd/crbench
./fakegcs -root /tmp/fakegcs -latency &
EP='endpoint=http://127.0.0.1:9100'
./crbench soak -app ./cloudrun-duckdb -replica-url "gs://bench/soak?$EP" -duration 90s -throttle
./crbench soak -app ./cloudrun-duckdb -replica-url "gs://bench/steady?$EP" -duration 60s \
  -crash-every 0 -scale-every 0 -deploy-every 0
./crbench coldstart -app ./cloudrun-duckdb -replica-url "gs://bench/cold?$EP" -rows 10000,100000,1000000
```

## Deploy

Terraform in `terraform/` creates the bucket, the Artifact Registry
repository, the service accounts, the writer service limited to one
instance, and the read-only replica service. It builds the image with
[ko](https://ko.build) on `cgr.dev/chainguard/glibc-dynamic`, which includes
libstdc++. The build needs CGO and gcc on linux/amd64, which GitHub Actions
has.

The stack follows cloudrun-sqlite's. Apply `gcp/terraform` first, then run
the first apply of this stack from your machine:

```bash
cd cloudrun-duckdb/terraform
cp terraform.tfvars.example terraform.tfvars   # set project_id
tofu init -backend-config="bucket=BUCKET"
tofu apply
```

The app doesn't have a `gcp-deploy.json` yet, so `deploy-gcp.yml` neither
plans nor applies it. The workflow's plan account can only read the state
bucket, and `tofu init` writes an empty state for a stack that has none, so
a pull request can't plan this stack until the first apply has created its
state. After that, add `gcp-deploy.json` with `{"watch": ["cloudrun-duckdb"]}`,
add `cloudrun-duckdb/terraform/**` to the workflow's pull request paths, and
update the app list that `.github/scripts/discover-gcp-apps_test.sh`
expects. Then a pull request that changes the app runs `tofu plan`, and a
push to `main` runs `tofu apply`. See
[cloudrun-sqlite's Deploy section](../cloudrun-sqlite/README.md#deploy) for
the GitHub environment and the plan and deploy accounts.

The defaults give each instance 512 MiB with a 256 MiB in-memory volume,
enough for a database up to about 200 MiB. Raise `memory_limit` and
`scratch_size_limit` for more.

## Test

```bash
go test -race ./...
```

`TestCloudRunLifecycle` builds the server and runs it under the simulator
for 25 seconds of crashes, scale to zero, and overlapping deploys against
`fakegcs` with latproxy's latency, and fails if any acknowledged write is
missing afterward or the replica doesn't restore. `go test -short` skips it.
The store's tests cover restores, updates and deletes across snapshots,
reads during an upload, failed uploads, two instances racing, retention, and
a writer that went stale while retention deleted the entries after it.

# litestream-tenants

Local benches for a **GitHub-like** Litestream layout:

| DB | Contents | Write rate |
|----|----------|------------|
| `control.db` | tenants, users, orgs, members, repo registry, ACL | rare |
| `repo-{id}.db` | PRs, comments, check runs for one repo | request path |

**Every repo API operation** runs `AuthorizeRepo` on `control.db` first (explicit
`repo_access` or org membership), then reads/writes the repo DB.

File replicas under `replicas/` stand in for GCS. Modes: `local` (hot SQLite),
`vfs-write` / `vfs-read`, `restore`.

## Run

```bash
cd litestream-tenants
CGO_ENABLED=1 go test -tags vfs -v ./...
CGO_ENABLED=1 go run -tags vfs . api -duration 5s
CGO_ENABLED=1 go run -tags vfs . all
```

### `api` — QPS with ACL on every repo op

```bash
CGO_ENABLED=1 go run -tags vfs . api \
  -mode local -duration 5s \
  -tenants 3 -repos-per-tenant 4 -users 50 \
  -prs 200 -comments 8 -checks 15 \
  -readers 32 -writers 8 \
  -control-readers 16 -control-writers 1 \
  -repo-lru 12
```

Reports:

- `control-read` — ACL lookup only  
- `control-write` — grant/replace `repo_access` (throttled)  
- `repo-read+acl` — ACL + `SELECT` PR by number  
- `repo-write+acl` — ACL + `INSERT` comment  
- **effective QPS per repo** = aggregate repo QPS ÷ repo count (uniform mix)

### `cold-open`

Restore vs VFS open + first PR point-read for one seeded repo.

## Schema (abridged)

Control: `tenants` → `orgs` / `repos`; `users`; `org_members`; `repo_access`.  
Repo: `pull_requests`, `issue_comments`, `check_runs` (slim check output).

See `schema.go` for full DDL.

## What real-world traffic can we support per repo?

Numbers below are from **local** `api -mode local` on this harness (single
process, WAL SQLite, ACL join each time). Treat them as **upper bounds**;
Cloud Run + GCS/VFS will be lower (often ~5–20× for VFS, less for local disk
on Gen2 with always-on CPU).

### Measured on this machine (`api -mode local`)

ACL on every repo op; control DB always local/hot; ~150–200 PRs/repo.

| Scenario | Control read QPS | Repo read+ACL | Repo write+ACL | Per-repo read / write |
|----------|------------------|---------------|----------------|------------------------|
| **1 hot repo** | ~88k | ~67k | ~8k | **~67k / ~8k** |
| **12 active repos** (uniform) | ~61k | ~109k agg | ~24k agg | **~9k / ~2k** each |

Control writes are paced (~180/s here) to mimic rare ACL grants.

**Per repo** when traffic is spread evenly across \(R\) hot repos on one process:

\[
QPS_{repo} \approx QPS_{aggregate} / R
\]

Ceiling is the **shard**, not a magic per-repo quota: one hot repo can consume nearly all of the aggregate.

### Product translation (one Cloud Run writer shard)

Assume **local SQLite + Litestream → GCS** for control + open repo files (API
primary). Derate local benches for Cloud Run CPU/concurrency (~2–5× conservative).

| Repo popularity | Comfortable | Spike / dedicated |
|-----------------|-------------|-------------------|
| Quiet repo among many | **1–10 req/s** | 50/s |
| Normal active repo | **20–100 req/s** mixed | ~200/s |
| Hot repo alone on shard | **~1k–10k read/s**, **~0.5k–2k write/s** | bigger CPU / own shard |
| Webhooks (checks, sync) | **tens–low hundreds write/s** aggregate / shard | shard when sustained higher |

Most real GitHub-metadata traffic is **well below** these ceilings: a shard with
**hundreds of repos**, **tens of aggregate write QPS**, and **hundreds–thousands
of read QPS** is the intended zone. Use `hash(repo_id) % K` when the hot set or
SQLite write lock saturates.

### Cloud Run concurrency 1000 vs SQLite limits

Cloud Run’s **max concurrent requests / instance = 1000** caps *in-flight*
requests, not QPS:

\[
QPS \approx concurrency / latency
\]

| Avg handler latency | Max QPS at concurrency 1000 |
|---------------------|-----------------------------|
| 1 ms | ~1 000 000 |
| 5 ms | ~200 000 |
| 20 ms | ~50 000 |
| 100 ms | ~10 000 |

For our point ACL+PR ops (often **~1–20 ms** in-process), concurrency 1000
allows **far more QPS than SQLite writes can absorb**. Binding limits:

| Path | Practical per writer shard | Hits first |
|------|----------------------------|------------|
| **Writes** | **~1 k/s** comfortable (~few k/s lab ceiling) | SQLite single-writer lock — **not** CR concurrency |
| **Reads on writer** | tens of k/s possible | CPU / lock contention with writes; CR concurrency rarely first |
| **Reads on RO replicas** | scale out horizontally | Add reader shards **well before** ~8 k read QPS on one box if you want headroom |

So: **yes — for reads, add reader replicas (or more RO Cloud Run services)
before a single shard is near ~8 k read QPS.** Keep the writer focused on
writes + light reads; **~1 k writes/s per writer shard** is a solid planning
max (and is already a lot of GitHub-metadata traffic).

Use **instance-based billing / always-on CPU** for writer (+ Litestream). Avoid
request-based `$0.40 / M` at these QPS levels.

### Cost sketch (us-central1, order-of-magnitude)

Assumptions: instance-based Cloud Run; Litestream batches writes (~1 s sync);
reader replicas use **hydrated local RO** (`restore -f`) or warm VFS cache so
steady-state reads are **not** 1 GCS GET per request; Standard GCS regional;
**egress excluded unless noted** (often dominates if responses leave GCP).

#### Sustained **1 k writes/s** (one writer shard)

| Component | Assumption | ≈ $/month |
|-----------|------------|-----------|
| Cloud Run writer | 2 vCPU / 2 GiB always on | **~$105** |
| GCS Class A (LTX uploads) | ~1–10 objects/s after batching (1 DB vs many hot repos) | **~$13–130** |
| GCS storage | ~50–200 GiB retained LTX/snapshots | **~$1–4** |
| GCS Class B | compaction/readers polling light | **~$5–20** |
| Egress (optional) | 500 B ack × 1 k/s → ~1.2 TB/mo @ $0.12/GB | **~$150** if public internet |
| **Total (in-GCP, no egress)** | | **~$125–260** |
| **+ internet egress** | | **~$275–410** |

CPU/RAM: one mid-size always-on instance. Litestream does **not** charge per
app write — only per synced LTX object.

#### Sustained **10 k reads/s** across **10 reader shards** (1 k/s each)

| Component | Assumption | ≈ $/month |
|-----------|------------|-----------|
| Cloud Run readers | 10 × (1 vCPU / 1 GiB) always on | **~$530** |
| Writer (still needed for freshness) | 1 × (1–2 vCPU) | **~$50–105** |
| GCS ops (hydrated RO) | poll/follow LTX ~1/s/replica → ~10 Class B/s | **~$10** |
| GCS ops (cold VFS, miss-heavy) | avoid for this QPS — could be $100s–$1000s | n/a if hydrated |
| GCS storage | shared replica data (not ×10) | **~$1–4** |
| Egress (optional) | 2 KB × 10 k/s → ~50 TB/mo | **~$6 000** if public internet |
| **Total (in-GCP, no egress)** | | **~$600–650** |
| **+ internet egress** | | **~$6.5 k** |

CPU/RAM scales ~linear with reader count; **GCS storage does not** (one
replica tree). GCS ops stay cheap if replicas are local-hydrated; VFS
page-fault reads at 10 k/s would multiply Class B and are the wrong shape.

#### Relative takeaway

| | 1 k write/s | 10 k read/s (10 RO) |
|--|-------------|---------------------|
| Dominant cost (in-GCP) | Writer CPU + LTX Class A | Reader CPU × N |
| GCS storage | small | small (shared) |
| GCS ops | modest if batched | modest if hydrated |
| Egress | optional, can exceed compute | often **the** bill if clients are on the public internet |

Compared to Cloud SQL / a managed SQL at similar QPS, this scheme is usually
**cheaper on storage + idle**, and **predictable** if you keep always-on
shards sized for peak; egress and “VFS miss storm” are the costs to watch.

### VFS mode

`api -mode vfs-write` uses VFS only for **repo** DBs; control stays local/hot.
Expect lower and noisier write QPS than `local` (and real GCS RTT in prod). Prefer
**local + Litestream replicate** for steady API primaries; VFS for cold open /
scale-to-zero / read replicas.

### Cold start (repo DB)

With compacted replicas, first **point** PR read after VFS open stays sub-linear
in DB size; full restore and table scans scale with size. Prefer one DB per repo
so a huge monorepo doesn’t cold-start everyone else.

## Layout

```
litestream-tenants/
├── schema.go      # control + repo DDL, SeedWorld, AuthorizeRepo
├── harness.go     # Litestream open/replicate, DB LRU pool
├── bench_api.go   # api + cold-open benches
├── main.go        # CLI
└── bench_test.go
```

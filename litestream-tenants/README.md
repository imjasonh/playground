# litestream-tenants

Local experiments for **multi-tenant SQLite + Litestream**, aimed at a Cloud Run
shape: write locally (or via VFS), replicate to object storage (GCS in prod;
a `file://` replica tree here).

This continues the ideas in
[`terraform-playground/litestream`](https://github.com/imjasonh/terraform-playground/tree/main/litestream)
with newer Litestream (v0.5.x LTX + writable/read VFS).

## Requirements

- Go 1.24+ (`GOTOOLCHAIN=auto` is fine)
- CGO + a C compiler (`gcc`)
- Build tag `vfs` (Litestream’s VFS is behind that tag)

```bash
cd litestream-tenants
CGO_ENABLED=1 go test -tags vfs -v ./...
CGO_ENABLED=1 go run -tags vfs . all
```

## What it measures

| Command | Question |
|---------|----------|
| `cold-open` | Full `restore` vs VFS open+query for tiny/medium/large tenants |
| `rw` | Single writer + N readers RPS/latency (`-mode local\|vfs-write`) |
| `conflict` | Two VFS writers on one tenant → conflicts (unsafe) |
| `fanout` | Many tenants via LRU pool — open on demand, no boot restore |
| `shard` | Hash tenants onto K exclusive writer shards |

Examples:

```bash
CGO_ENABLED=1 go run -tags vfs . cold-open -rows 5000 -payload 1024
CGO_ENABLED=1 go run -tags vfs . rw -mode local -readers 64 -duration 5s
CGO_ENABLED=1 go run -tags vfs . rw -mode vfs-write -readers 16 -duration 5s
CGO_ENABLED=1 go run -tags vfs . fanout -tenants 50 -capacity 8 -rounds 3
CGO_ENABLED=1 go run -tags vfs . shard -tenants 30 -shards 5 -duration 5s
```

## Findings these benches are meant to show

### Single writer is still the rule

- **One writer per database** (SQLite + Litestream). Scaling Cloud Run writers
  against the *same* tenant replica will conflict or diverge.
- Within one process, WAL allows many concurrent readers beside that writer.
- The `conflict` command shows the sharp edge: local `INSERT`s often succeed
  (VFS write buffer) while sync-on-close races (`conflict detected`, LTX rename
  failures) show up in Litestream logs — so dual writers are unsafe even when
  the SQL API looks fine.

### Does VFS help cold start for many/large tenants?

**Yes — this is the main reason to prefer VFS for multi-tenant on-demand writers.**

| Approach | Cold path | Cost scales with |
|----------|-----------|------------------|
| Classic restore then write | Download full DB (+ LTX chain) to disk, then open | **DB size** |
| VFS write mode | Register VFS, fetch pages on demand, buffer writes, sync LTX | **Working set** (pages touched) |

So you do **not** need to restore every tenant DB at process start. Keep an LRU
of open tenant VFSes (`fanout` command); cold tenants pay page-fault latency into
the replica, not a full hydrate.

Tradeoffs of VFS write mode:

- Eventual durability (sync interval; default-ish 250ms–1s in these benches)
- Conflict detection if a second writer appears — not prevention
- Heavier per-page latency than a warm local file until cached/hydrated

Background hydration (`LITESTREAM_HYDRATION_*`) can optionally fill a local file
while serving; useful once a tenant is hot.

### Multi-tenant writer topologies on Cloud Run

**A. One service, many tenant DBs (recommended starting point)**  
`max-instances=1`, Gen2, CPU always allocated. Lazy-open tenants with VFS write
(or restore-on-first-use if you need local-disk latency). Litestream/VFS syncs
each tenant to `gs://bucket/tenants/<id>/`. Scale-to-zero loses in-memory/LRU
state; next cold start reopens via VFS without full restore.

**B. Sharded writer services**  
`tenant → shard = hash(tenant) % K`. Deploy `writer-0` … `writer-(K-1)`, each
`max-instances=1`, each owning a disjoint tenant set. The `shard` bench models
this locally with `-mode local` (local SQLite per tenant, as each Cloud Run
shard would run). Write RPS scales ~linearly with K **if** load is balanced
across tenants.

Avoid keeping many hot **VFS write** handles for different tenants under heavy
concurrent write churn in one process — this harness can hit `database disk
image is malformed` in that shape. Prefer VFS for **on-demand** open (fanout /
LRU) or one local DB per tenant inside a shard process.

**C. Sticky routing / GCLB**  

| Mechanism | Tenant affinity? |
|-----------|------------------|
| Cloud Run session affinity | **No** — per client cookie, best-effort, not tenant-aware |
| GCLB session affinity on serverless NEG | **Not supported** meaningfully for this |
| GCLB path/host → different Cloud Run services | **Yes** — e.g. `/shard/3/*` or `s3.example.com` → `writer-3` |
| GCLB URL mask / path to service name | **Yes** — map URL piece to `writer-N` |
| Thin router service | **Yes** — router hashes tenant → `writer-N` URL |

GCLB cannot hash an arbitrary tenant header onto backends by itself without a
URL/host scheme or a router. Practical patterns:

1. **Path prefix from the edge/API gateway:** client or BFF calls
   `/s/{shard}/...` where `shard = hash(tenant) % K`.
2. **One Cloud Run service per shard** behind a URL map.
3. **Single max-instances=1 writer** until you outgrow it; simplest.

Read replicas (optional): separate Cloud Run services using VFS **read-only** or
`litestream restore -f`, scaled out freely. They lag the primary by poll/sync
interval.

### Rough RPS expectations (prod, single writer instance)

Local `rw -mode local` on a laptop/CI VM is an upper bound; Cloud Run adds CPU
limits and concurrency caps.

| Mode | Ballpark on one Gen2 instance |
|------|-------------------------------|
| Local SQLite + Litestream replicate | Thousands of small reads/s; ~1k–5k small writes/s typical |
| VFS write (remote-first) | Lower — hundreds to low thousands depending on cache / GCS RTT |
| Comfortable mixed workload | Hundreds–low thousands RPS before you shard |

Use `rw` and `shard` here to calibrate for your row sizes and query shapes before
deploying.

## Layout

```
litestream-tenants/
├── main.go          # CLI
├── tenant.go        # seed, replicate, VFS/restore open, LRU pool
├── bench.go         # cold-open / rw / conflict / fanout / shard
├── stats.go         # latency + RPS helpers
└── bench_test.go    # smaller CI-friendly runs (-tags vfs)
```

Replica directory layout (local stand-in for GCS):

```
$DIR/replicas/<tenant>/   # LTX tree
$DIR/source/<tenant>.db   # seed source
$DIR/buffers/             # VFS write buffers
$DIR/restored/            # full restore outputs
```

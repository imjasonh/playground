# Design: a git smart-HTTP server on Cloudflare Workers

This document explains how the server works, why it is shaped the way it is,
and what it costs to run. The short version: **R2 holds immutable bulk data
(packs and indexes), one Durable Object per repo holds a tiny versioned state
document that names that data, and every expensive operation is either a
streaming copy or an index-guided ranged read.** Nothing ever needs the whole
repository — or even a whole pack — in memory.

## Constraints, and what they force

| Constraint | Consequence |
|---|---|
| Workers isolate: ~128 MiB memory, bounded CPU per request | never buffer a pack; all per-request state must be O(objects-touched), not O(repo) |
| No filesystem | git's own layout (loose objects, `.idx` mmap) is unavailable; storage must be object-store-native |
| R2: immutable objects, ranged reads, multipart writes, no append/rename | packs are write-once and content-named at upload time; "append" = multipart upload; indexes must make ranged reads precise |
| Durable Objects: per-key single-threaded, transactional storage | the natural (and only) linearization point for ref updates |
| Low cost at scale | avoid Class A ops (writes/lists) on read paths; avoid per-object requests; exploit free egress |
| Stock `git` clients (smart HTTP) | wire format is fixed: pkt-lines, packs, protocol v2 fetch, receive-pack push |

## Storage layout

All bulk data lives in one R2 bucket, namespaced per repo:

```
<repo>/pack/<id>.pack      # raw git packfile, byte-for-byte as pushed (or repacked)
<repo>/pack/<id>.idx       # GSIX index for that pack (see below)
<repo>/filelog/<id>        # file-log segment: per-path change records for one push
```

The only *mutable* state is a small JSON document owned by the repo's Durable
Object:

```json
{
  "head": "refs/heads/main",
  "refs": { "refs/heads/main": "<oid>", "refs/tags/v1": "<oid>" },
  "packs": [ { "id": "p-…", "bytes": 123456, "objects": 42 }, … ],
  "filelog": [ "p-…", … ]
}
```

The document is versioned. Maintenance (repack) updates it by whole-document
compare-and-swap on the version; pushes send a **delta** (per-ref old→new
updates plus pack/file-log appends) that the DO merges atomically against the
current state — per-ref CAS, git's actual contract. This split is the whole
consistency story:

* R2 objects are immutable and written *before* the state document references
  them, so a reader can never see a dangling reference.
* A push becomes visible atomically when its delta is applied: refs, the pack
  manifest, and the file-log manifest flip together. Readers always get a
  consistent snapshot (they read the state doc once per request).
* Two concurrent pushes to the same repo **merge**: updates to disjoint refs
  all land (pack appends commute), so pushes to different branches never
  conflict. Only a true same-ref race fails — per-ref, `ng … fetch first`,
  with other refs in the same push unaffected — and the loser's staged pack
  becomes garbage (cleaned by maintenance; it was never referenced). This is
  what lifts the per-repo write ceiling measured in
  [`loadtest-scaling.md`](loadtest-scaling.md): with a whole-document CAS the
  entire multi-second push pipeline was one conflict window, capping goodput
  at ~0.5 pushes/s per repo regardless of concurrency.

There are deliberately **no loose objects**: every object arrives in a pack
and stays in a pack. There is also deliberately **no `list` on hot paths** —
the pack manifest in the state document replaces R2 `List` (Class A, the
expensive tier) everywhere.

## The GSIX pack index

Git's own `.idx` format assumes mmap. Ours (`GSIX`, one per pack) is built for
"loaded in one small read, guides exact ranged reads":

per entry (82 bytes, sorted by oid): `oid`, `header_start`, `data_start`,
`data_end`, `stored_type`, `final_type`, `final_size`, `payload_size`,
`base_oid`.

Four fields do the heavy lifting:

* `data_start..data_end` — the exact compressed byte range, so reading an
  object's payload is **one** ranged GET of exactly the right size.
* `final_type`/`final_size` — the object's identity after delta resolution, so
  type/size queries never touch the pack.
* `payload_size` — the inflated size of the stored payload itself (the delta
  blob's size, for delta entries), so pack-copy paths can re-emit entry
  headers without inflating anything.
* `base_oid` — for delta entries, the *resolved* base object id. This turns
  delta chains into pure oid lookups at read time, and (crucially) lets
  repacking rewrite position-dependent `OFS_DELTA` entries as position-
  independent `REF_DELTA` without touching payload bytes.

An index entry is 82 B/object (~82 MB per million objects). The current
prototype loads a pack's whole index per request; the format is already
sorted, so the planned upgrade for very large packs is fanout + binary search
via ranged reads (log₂ probes of ~74 bytes each), plus a KV/Cache-API layer
for hot indexes. That changes `Odb::open`, nothing else.

## Push (receive-pack): streaming ingest

```
client ──pack stream──▶ Worker ──┬─▶ R2 multipart upload  (5 MiB parts)
                                 └─▶ PackScanner          (incremental)
```

1. **Command section** (pkt-lines) is parsed incrementally; the rest of the
   body is the pack.
2. **Every raw pack byte is teed** to an R2 multipart upload *and* to the
   incremental scanner. The scanner finds entry boundaries (inflating as it
   goes — zlib streams have no length prefix), records each entry's byte
   range/type/delta-base, hashes non-delta objects on the fly, and verifies
   the pack's trailing SHA-1. Memory: a partial-chunk carry buffer + 32 KiB
   inflate scratch + ~50 B/entry of metadata. The client's own compression is
   preserved — we never recompress a push.
3. **Delta resolution** then assigns final oids/types to delta entries by
   reading their payloads back from the just-uploaded pack with ranged reads,
   walking chains root-first with a byte-budgeted content cache. Thin-pack
   bases (git pushes are thin by default) come from the existing odb by oid.
   The result is the GSIX index, written next to the pack.
4. **Validation** (Worker-side, where the odb is): ref targets must exist and
   (for commits) have their root tree present. Honest clients are fully
   covered because the pack itself was verified
   self-contained-or-thin-against-us; full reachability audit is a documented
   maintenance-time job rather than a push-time cost. Ref *freshness* is not
   checked here — the snapshot may be stale.
5. **File-log segment** (below) is built for the new commits.
6. **Merge-apply the delta in the DO.** Each ref update lands iff the ref's
   *current* value equals the advertised old value (per-ref CAS); the pack and
   file-log appends commute with racing pushes. Only after this does
   report-status say `ok` — so every derived view is consistent the instant
   the client sees success.

## Fetch (upload-pack, protocol v2): copy, don't compress

`ls-refs` is a state-document read. `fetch` does:

1. **Object selection**: walk commits from wants, stopping at haves' ancestor
   set; collect trees/blobs of selected commits, excluding the tree closure of
   boundary commits (things the client provably has). This is the one
   genuinely history-proportional operation; see "Scaling read paths" below.
2. **Pack generation**, the cost-critical part. For each object, consult the
   index:
   * stored full → **copy the compressed bytes verbatim** (ranged read →
     response); zero CPU beyond SHA-1 of the output stream;
   * stored as delta whose base is also being sent (or which the client
     already has, when it offered `thin-pack`) → emit as `REF_DELTA`,
     **copying the compressed delta verbatim**;
   * stored as delta whose base isn't available to the client → materialize
     and deflate (the only recompression path, and the rarest).
3. **Negotiation is short-circuited**: we ACK all common haves and declare
   `ready` in the same response as the pack, so any fetch is one round trip
   (plus the advertisement GET). Stateless, Workers-friendly, and it
   minimizes billable requests on both sides.

The benchmark suite quantifies the copy-vs-compress design: verbatim copy
emits pack data ~5 orders of magnitude faster than deflating the same bytes
(`write/precompressed-copy` vs `write/full-objects` in `cargo bench`).

## File / tree / blame APIs and the push-time file-log

The product requirement: file contents at a ref, per-line blame, and per-file
"last commit" in a directory — **efficient and consistent immediately after a
push**. Classic blame walks the commit graph diffing trees; that is exactly
the O(history) work a Worker cannot do. Instead, the work is done once, at
push time, when the new commits are already in hand:

For each new commit (topologically ordered), diff its tree against its first
parent's (subtree-skipping: unchanged subtree oids are not descended). Each
changed path yields a record:

```
{ path, commit, time, change: Add|Modify|Delete, blob,
  prev_commit, prev_blob }   # the previous record for this path
```

Records for one push form one immutable *file-log segment* in R2 (a compact
binary format, `GSFL` — less than half the size of the equivalent JSON and
~10× faster to parse, which matters because read APIs load segments per
request); the state document lists segments; maintenance merges them. The
`prev_*` pointers chain each path's versions backwards through time.

**Path-range sharding.** Loading a whole merged history to answer a
one-path question was the measured hotspot of the read APIs (a 200k-record /
22 MiB history parses in ~50-90 ms — dominating blame and tree latency).
Merged segments are therefore *sharded by path range*: records are stably
sorted by path (preserving per-path chronological order) and split at path
boundaries into ~256 KiB shards, described by a small `GSFI` index object
`(shard → [min_path, max_path])`. A path's records are never split across
shards, so:

* **blame** (exact path) loads the index + exactly one shard;
* **tree** (directory prefix) loads the index + the shard(s) whose range
  intersects the prefix — usually one, fetched concurrently when several;
* **push prev-pointer lookup** scopes its load to the pushed paths' shards;
* the root listing (`prefix=""`) still intersects every shard — the honest
  worst case, no slower than the monolithic layout (shards are fetched
  concurrently and parse the same total bytes).

Maintenance writes the merged log sharded; an oversized *push* segment (a
huge initial import) is sharded immediately at push time too, so read APIs
are fast right away. Measured (`cargo bench --bench filelog`, 50k paths × 4
versions = 200k records, 90 shards):

| query | monolithic (before) | sharded (after) | speedup |
|---|---|---|---|
| blame chain (one path) | ~50 ms | **~0.6 ms** | ~85× |
| directory listing | ~85 ms | **~1.5 ms** | ~55× |
| root listing (worst case) | ~85 ms | ~75 ms (91 reads) | ~1× |

In the whole-lifecycle benchmark (1000 commits × 10k files, post-repack),
tree API latency went from ~90 ms to ~5 ms and blame from ~55 ms to ~10 ms.
Read APIs build a one-pass `FileLogView` (newest record per path, ordered so
directory-prefix queries are range scans) over whatever shards were loaded.
A remaining planned addition is an in-isolate parsed-shard cache keyed by
shard key (shards are immutable, so caching is trivially safe).

* **Directory listing with attribution**: newest record per path (or path
  prefix, for subdirectories) across segments, newest segment first.
* **Blame**: hop the chain to enumerate the file's versions newest→oldest
  (stopping at the introducing `Add`), read only those blob versions, and
  diff adjacent pairs (Myers, on line hashes, with an edit-distance cap):
  lines matching the older version inherit attribution; the rest belong to
  the newer commit. Cost ∝ the file's own change count — independent of repo
  history. The integration tests verify blame output line-by-line against
  `git blame`.

**Documented approximation**: the chain follows the first-parent line as
recorded at push time, so blame behaves like `git blame --first-parent` when
concurrent branches touch the same path, and the prototype's "latest record
for path" starting point is exact for tip commits (the UI case) but can pick
the wrong side of unmerged concurrent branches. The fix (planned, not built):
record per-branch chain heads in the state document, and start the chain from
the pushed ref's own head. Renames are not followed (as with `git blame`
without `-C`).

## Repacking (scheduled maintenance)

Every push adds a pack; each pack costs one index read per request, so
consolidation keeps reads O(1). The repack is designed around what Workers
are bad at (CPU, memory) and what R2 makes cheap (streaming copies):

* Iterate all oids (newest pack wins duplicates); copy every entry's
  compressed payload verbatim into one new pack via multipart upload,
  rewriting only entry *headers*: `OFS_DELTA` becomes `REF_DELTA` using the
  `base_oid` recorded in GSIX. **No inflation, no recompression, no delta
  re-discovery.** Per-byte CPU is effectively just the SHA-1 of the output.
* Merge file-log segments (concatenation in push order) and re-shard the
  result by path range (see "Path-range sharding" above).
* Write new pack + index + merged file-log, then CAS the state document
  (whole-document, versioned — unlike pushes, repack rewrites the pack list
  wholesale); only after the flip delete the old objects. A racing push bumps
  the version, so the repack's CAS fails and it discards its staged output
  and retries next schedule — pushes always win over maintenance.
* The scheduled handler walks a KV registry of repos (registered on push).

The current implementation consolidates **all** packs in one invocation and
holds O(objects) metadata in memory — fine for small/medium repos, but it
fails on very large ones (memory, then the per-invocation subrequest cap,
then CPU, in that order). The incremental, bounded, resumable redesign that
keeps repacking feasible for arbitrarily large repos — geometric
consolidation of the small end, leaving the large base pack immutable — is
sketched in [`large-repo-repacking.md`](large-repo-repacking.md).

## Block-cached reads: request count is the real currency

R2 charges per *request*, not per byte, and Worker→R2 bandwidth is free — so
the naive "one exact ranged GET per object" design, while byte-optimal, is
request-pessimal: the large-repo benchmark measured a full clone of a 175k-
object repo at ~250,000 Class B operations (~$0.09 *per clone*; a real R2
round-trip per object would also make it minutes slow).

Every bulk read path therefore goes through a `BlockReader`: 4 MiB-aligned
ranged reads with a small per-pack LRU (8 blocks, 32 MiB ceiling). To make
the cache hit, bulk operations are ordered by *pack offset* rather than
selection order:

* delta resolution already scans entries in pack order (bases cluster before
  their deltas — git writes packs that way);
* fetch pack generation sorts the send set by (source pack, offset) before
  copying — legal because we emit only full and `REF_DELTA` entries, which
  `git index-pack` accepts in any order;
* repack sorts its source entries the same way.

Measured effect on the 175k-object repo: clone went from ~250k Class B reads
to **12**, push from ~311k to ~31, repack from ~175k to ~14 — request counts
now scale with bytes/4 MiB, not with object count.

## Cost model

R2 pricing shape (2025): Class A (writes, multipart ops, lists) ≈ $4.50/M,
Class B (reads, ranged reads, head) ≈ $0.36/M, storage $0.015/GB-mo, **egress
free**. DO requests ≈ $0.15/M + duration; KV reads ≈ $0.50/M. Per operation:

| Operation | DO | R2 Class A | R2 Class B |
|---|---|---|---|
| push (P packs, size S) | 1 load + 1 commit | multipart: ⌈S/5MiB⌉+2; idx put: 1; filelog put(s) | P idx + ⌈S/4MiB⌉ block reads + scoped filelog shards |
| clone (1 pack repo, size S) | 1 load | 0 | 1 idx + ⌈S/4MiB⌉ block reads |
| incremental fetch | 1 load | 0 | P idx + blocks covering the objects sent |
| file API | 1 load | 0 | P idx + blocks covering the path walk |
| blame | 1 load | 0 | P idx + filelog index + ~1 shard + blocks covering the versions |
| repack (size S) | 1 load + 1 commit | ⌈S/5MiB⌉+2 + filelog shards + deletes | ⌈S/4MiB⌉ block reads + idx + filelog reads |

The MemStore/MemStateStore in the test suite count these classes (including
modelled 5 MiB UploadParts), the integration tests assert the bounds (e.g.
clone performs zero Class A operations), and `cargo bench --bench
large_repo` prices every phase.

### Measured $ and throughput

Two benchmark shapes: **bulk** (one 512 MiB incompressible blob — bytes
dominate) and **many-object** (1000 commits × 10k files, 175k objects,
57 MiB — requests dominate). Wall times are native release builds over
loopback with in-memory storage, so they measure *our* code plus the real
git client, not network or R2 latency; dollar figures are the marginal
request costs (R2 Class A/B + DO) from the op counters, which do not depend
on where they run.

**Bulk transfer — $ per GiB and GiB/s:**

| operation | request cost / GiB | dominated by | end-to-end throughput |
|---|---|---|---|
| push | **~$0.00096 / GiB** | ⌈GiB/5 MiB⌉ ≈ 205 UploadParts × $4.5/M | ~0.04 GiB/s (client zlib + server scan) |
| clone / pull | **~$0.000096 / GiB** | ⌈GiB/4 MiB⌉ = 256 block reads × $0.36/M | ~0.08 GiB/s (server copy is >1 GiB/s; client `index-pack` dominates) |
| repack | ~$0.001 / GiB per run | parts (A) + block reads (B) | ~0.25 GiB/s |
| storage | $0.015 / GiB·month | — | — |

Egress is free, so pull cost is *pure request overhead*: cloning the same
GiB a million times costs ~$96 in requests and $0 in bandwidth. (For
comparison, serving that from S3 would be ~$90,000 of egress.) Server-side
CPU is the other pull-side cost: pack copy is memcpy+SHA-1 (~2 s CPU/GiB ⇒
~$0.00004/GiB at $0.02 per million CPU-ms on Workers Standard); push-side
scan+resolve is zlib-bound (~30-75 MiB/s ⇒ ~$0.0003-0.0007/GiB). Even
all-in, **a GiB pushed costs ~$0.002 and a GiB pulled ~$0.0002**, plus
$0.015/GiB·month at rest.

**API calls — $ per op and latency** (many-object shape, post-repack,
i.e. worst realistic history size for these paths):

| API | requests (B + DO) | request cost / op | cost / 1M ops | latency (ours) |
|---|---|---|---|---|
| file | 4 + 1 | $0.0000016 | ~$1.60 | ~4-15 ms |
| tree (dir + last-commit) | 7 + 1 | $0.0000027 | ~$2.70 | ~5 ms |
| blame | 9 + 1 | $0.0000034 | ~$3.40 | ~10 ms |
| incremental push | 9 B + 4 A + 3 DO | $0.0000217 | ~$21.70 | ~30-80 ms |
| incremental pull | 7 + 2 | $0.0000028 | ~$2.80 | ~50-170 ms |

Add Workers invocation ($0.30/M requests) and CPU ($0.02/M CPU-ms; these
handlers use ~2-15 CPU-ms natively, call it 2-3× on wasm) and each read API
lands at **roughly $2-6 per million calls, all-in** — the R2/DO request
costs and the Worker costs are the same order of magnitude, and nothing
scales per-object or per-history. Every operation's request count is
O(bytes/block) or O(1), which is the property to defend as the design
evolves.

Also note the one KV touch: a push checks the maintenance registry with a
read ($0.50/M) and writes only on first push ($5.00/M once per repo) —
negligible.

One planned optimization still matters at scale, and it is a pure addition:

1. **`packfile-uris`**: after repack, keep a snapshot pack; serve full clones
   as a redirect to the R2 object (free egress, zero Worker CPU while the
   client downloads) plus a small top-up pack for commits since the snapshot.
   Protocol v2 supports this natively (`packfile-uris`); stock git clients
   opt in with `fetch.uriprotocols=https`. This is the single biggest lever
   for large-repo clone cost (it removes the Worker from the bulk-bytes path
   entirely) and is why "snapshot pack per repack" is part of the
   maintenance design.

Full clones additionally skip the reachability walk entirely: when a fetch
has no `have`s and wants every advertised tip, the server sends the whole
pack manifest as-is (objects awaiting maintenance GC ride along as dangling
objects, which git tolerates). This removes the one history-proportional
CPU cost from the most bandwidth-heavy operation.

## Memory & CPU discipline (Workers limits)

The isolate memory limit (128 MiB) is a *correctness* boundary, not a
tuning knob: exceeding it is Cloudflare error 1102, the client sees a 503,
and — because wasm linear memory never shrinks — one bloated request
permanently inflates the isolate for every request after it. The first
production deployment demonstrated this: buffered fetch responses made
pushes/clones of >~30 MiB repos fail intermittently. Three consequences:

* **Response bodies proportional to repo size are streamed, never
  buffered.** The fetch pack is emitted through `repo::PackEmitter` — the
  object-selection *plan* (~100 B/object) is built in the handler, then the
  response body is an async stream that copies each entry's compressed
  payload in ≤1 MiB pieces into side-band chunks. Large file-API blobs are
  chunked out of a single shared buffer. The Workers glue relays streams via
  `ReadableStream` (`Response::from_stream`), the same shape as piping an R2
  object to a response in JS.
* **Enforced in CI** (`tests/memory.rs`): a tracking global allocator
  measures peak live heap while a 48 MiB incompressible repo is pushed and
  cloned through the same handler the Worker runs; the test fails if a
  request's transient footprint exceeds a 64 MiB budget (headroom below the
  128 MiB limit for the wasm module, runtime, and JS-side copies). Measured
  after the streaming rewrite: push ≈ 32 MiB peak / ~0 transient over
  stored-bytes growth; clone ≈ 21 MiB peak while streaming 48 MiB.
* **Cache budgets are small and permanent-growth-aware** (wasm memory never
  returns to the OS): odb content cache 24 MiB, delta-resolution cache
  24 MiB, block cache 16 MiB per pack, multipart buffer 5 MiB.

Remaining bounds: push ingest is carry buffer + 32 KiB scratch + ~50 B/entry
(the pack streams through 5 MiB multipart parts); the peak resident item is
a single largest *materialized* object (a delta base must be whole to apply
a delta). Truly huge blobs (multi-GiB) would need the planned chunked-blob
path (store large blobs undeltified; stream inflate → deflate per block).
CPU: ingest scans ~30-75 MiB/s (zlib-bound), pack copy is memcpy+SHA-1;
Workers CPU limits (30 s HTTP, 15 min cron) bound a single push to roughly a
GiB per request-CPU-second budget; larger pushes need the documented
resumable-ingest extension.

## Size limits

What actually caps transfer sizes, post-streaming:

| Direction | Cap | Set by |
|---|---|---|
| **pull / clone** | none practical | streamed body; O(bytes/4 MiB) requests; copy-path CPU >1 GiB/s |
| **push** | **~100 MB per push** (Free/Pro zone; 200 MB Business, 500 MB Enterprise) | **Cloudflare's HTTP request-body limit — not our code** |

**Pull** footnotes: a delta entry whose base the client lacks (rare
`Materialize` mode) must fit in memory as one object (tens of MiB), and plan
metadata is ~100 B/object, so fetches of tens of millions of objects would
need the plan to spill — both far beyond prototype scale.

**Push is capped by Cloudflare, not by this design.** Git smart HTTP sends
the whole pack as a single POST body, and Cloudflare rejects over-limit
bodies with a 413 *before the Worker runs* — no server-side change can raise
it. This is the most important operational limitation of the service today.
Practical workaround for large imports: split history into several pushes
(`git push origin <old-sha>:refs/heads/main`, then progressively newer
commits), each under the limit; maintenance repacks the resulting packs into
one anyway. For repos too large to seed this way at all (13 GB+ monorepos),
the proposed answer is a server-side pull-based importer that sidesteps the
inbound cap entirely by making *us* the git client — see
[`large-repo-migration.md`](large-repo-migration.md).

**A paid Workers plan is required to reach that ceiling.** The push pipeline
scans the pack as it streams in (zlib-bound, ~30 MiB/s on wasm), so a large
push needs several CPU-seconds. The **free plan's ~2 s per-invocation CPU
cap** kills pushes at ~40 MB — and, tellingly, the failure surfaces to the
client as a bare `error code: 1102` / 503, *identical to an out-of-memory
kill* unless you look at the invocation's `outcome` field
(`exceededCpu` vs `exceededMemory`). That ambiguity sent an early
investigation chasing a memory bug that wasn't there; enabling persistent
logs (the `outcome` field) is what finally distinguished them. The paid plan
(Workers Standard, $5/mo) lets us raise the budget via `limits.cpu_ms`; we
set the maximum (`cpu_ms = 300000` in `wrangler.toml`), which makes CPU a
non-issue below the request-body cap. **Measured on the paid plan:** a real
`git push` of a 90 MB incompressible repo completes (`outcome: ok`,
~2.75 s CPU) and clones back byte-identical. Behind the edge cap sit only
our own (higher) bounds now: ~50 B/entry scan metadata (~1M objects per
push comfortably) and the per-push size guard.

Note the memory/CPU split by plan: the **128 MiB isolate memory limit
applies on every plan** (so the streamed fetch/clone response — never
buffering a whole pack — is load-bearing regardless of plan), whereas the
CPU cap is the only thing the paid upgrade lifts. Ingest itself is bounded
memory on any plan (streamed straight to the R2 multipart upload while
scanned in place — a carry buffer + 32 KiB inflate scratch + ~50 B/entry),
so it is CPU, not memory, that gates push size.

**Enforced locally, not just at the edge.** Because the 413 happens in
Cloudflare's proxy, neither the native harness nor workerd under `wrangler
dev` would otherwise exhibit it — a test could pass with a 500 MB push that
production rejects. `receive_pack` therefore enforces the same limit itself
(`GitHttp::push_limit_bytes`, default 100 MB, overridable via the
`PUSH_LIMIT_BYTES` var for higher-tier zones), counting body bytes as they
stream and aborting the staged upload with a readable report-status error
(including the split-push hint). The integration suite exercises the
rejection path with a shrunken limit
(`tests/integration.rs::rejects_push_over_size_limit`): the over-limit push
fails with the hint, the ref is untouched, and no staged pack is published.

Adjacent, about repo *shape* rather than transfer size: the state document
is one Durable Object value, and DO values cap at 128 KiB — roughly a few
thousand refs plus the pack manifest. A refs-heavy repo needs the state doc
sharded (e.g. refs split across keys) before any transfer limit matters.

## Observability

The deployed Worker reports the same quantities the cost model and the
native benchmarks are built on, so production assumptions are checkable
instead of hopeful. Everything is collected per request by a thread-local
in `src/metrics.rs` (a few clock reads per backend call; no allocation
until emission) and emitted two ways:

* **`Server-Timing` response header** on every response — standard,
  machine-parseable, visible in `curl -v`, browser dev tools, and RUM
  tooling:

  ```
  Server-Timing: total;dur=35.0, backend;dur=34.0, r2a;desc="0",
    r2b;desc="5", do;desc="1", kv;desc="0", cost;desc="1.950u$",
    filelog_load_parse;dur=1.0, ...
  ```

  `total` is handler wall time, `backend` is milliseconds awaited on
  R2/DO/KV (the gap between them is our own CPU), the `desc` counters are
  the R2 Class A/B, Durable Object, and KV op counts, `cost` prices them at
  list rates, and each pipeline phase (`src/timing.rs` spans: scan, resolve,
  filelog build, fetch selection, pack build…) gets its own entry.

* **One structured JSON log line per request** (`{"evt":"req",...}` with
  method, path, status, ms, backend_ms, op counts, bytes in/out, cost, and
  a phase map) via `console.log` — queryable in the Workers Logs dashboard
  and streamable with `npx wrangler tail --format json`. This is the only
  window into the git-protocol endpoints, whose response headers a git
  client never surfaces. Scheduled repacks log an equivalent
  `{"evt":"req","method":"CRON",...}` line per repo.

Persistent invocation logs are enabled in `wrangler.toml`
(`[observability]`; it is opt-in and was initially missed, which is why the
first production incident had to be diagnosed by live probing). Every
invocation stores Cloudflare's `outcome` field alongside our log lines —
diagnostic signatures worth knowing:

| Symptom | Signature in logs |
|---|---|
| client saw 503, body `error code: 1102` | `outcome: "exceededMemory"`, **no** `{"evt":"req"}` line (isolate killed before our logging ran) |
| client saw 503/504 on a huge push | `outcome: "exceededCpu"` |
| client saw 413 | *nothing* — the edge rejected it before the Worker ran; no invocation exists |
| handler bug | `outcome: "exception"` with the panic/exception text |

The native test server and benches emit the identical header (the in-memory
stores feed the same collector), an integration test asserts its shape, and
**`scripts/bench-remote.sh`** turns it into a report: it pushes/clones a
synthetic repo against `GIT_SERVER_URL` (or a local `wrangler dev`),
measures client-side GiB/s and per-API median latency, and prints the
server's own backend-ms/op-count/µ$ figures per endpoint, before and after
repack. Run it after deploying to validate the cost table above with real
network and R2 latency in the loop.

Not built yet (documented options): a typed Workers Analytics Engine
binding doesn't exist in worker-rs 0.5, so time-series metrics would
currently need raw JS interop — Workers Logs covers the need for now;
request logs are unsampled (one line per request), which is fine at
prototype traffic and a knob to add before serious volume; and for
*streamed* response bodies (fetch packs, large blobs) the Server-Timing
header and log line cover the handler phase only — backend ops issued while
the body streams are not yet folded into the totals.

## Consistency summary

| Guarantee | Mechanism |
|---|---|
| Push atomicity (all-or-nothing visibility) | one DO transaction merge-applies the push's delta (refs + pack + file-log together) |
| Read snapshot isolation | state doc read once per request; all R2 objects it names are immutable |
| Blame/file APIs consistent immediately after push | file-log segment referenced in the same DO transaction, before report-status |
| Concurrent pushes | merged in the DO: disjoint refs all land; a same-ref race gets a per-ref `ng … fetch first` |
| Repack vs push race | repack's whole-document CAS loses (every applied push bumps the version), discards staged output |
| Crash mid-push | staged pack unreferenced; state untouched; multipart upload GC |
| Push retry after dropped response | delta appends are idempotent (packs content-addressed, deduped by id) |

The whole-document CAS caps a single repo at ~0.5 successful pushes/s (the
CAS window spans the entire push pipeline, so goodput is `1 / push latency`
regardless of concurrency). A production load test measured this exactly;
[`loadtest-scaling.md`](loadtest-scaling.md) has the methodology, numbers,
and the plan to lift it (merge disjoint ref updates in the DO instead of
whole-document CAS).

## What's deliberately out of scope (prototype)

* **Auth**: single hook point at the router; Workers-native options (service
  tokens, Access) slot in front.
* **Shallow clone (`--depth` / `deepen`)**: supported — a depth-bounded
  commit walk with a `shallow-info` response section (`ls-refs`/`fetch`
  advertise `shallow`), including `--unshallow` deepening. **Partial clone
  (`filter=…`) and date/ref-based shallow (`deepen-since` / `deepen-not`)**
  remain rejected with a clean protocol error.
* **Symrefs beyond HEAD, reflogs, hooks, force-push policy** — policy layers
  above the CAS, not storage problems.
* **SHA-256 repos**: `Oid` is 20 bytes today; format negotiation exists in
  the advertisement.
* **Sub-pack GSIX lookups, filelog sharding by path prefix**: needed for
  million-object repos; formats already sort-ordered to allow it.

## Testing & benchmarking strategy

Same core, three harnesses (this is why the crate keeps runtime glue thin):

1. **Native** (`cargo test`): unit tests per module, plus integration tests
   that run a real `git` binary against the router over localhost HTTP with
   in-memory storage — clone, push, pull, tags, deletes, non-fast-forward
   rejection, large binaries, blame-vs-`git blame`, repack, and cost-counter
   assertions.
2. **workerd/miniflare** (`scripts/e2e.sh`): builds the actual wasm Worker
   and runs the same lifecycle through `wrangler dev --local` (real workerd,
   local R2/DO/KV simulators) with a real git client.
3. **Deployed** (`GIT_SERVER_URL=https://… scripts/e2e.sh`): identical suite
   against production, safe to run anytime (uses a uniquely named repo).

`cargo bench` measures the CPU hot paths natively (scan, resolve, index
serialize, pack write both paths, diff) with throughput reporting, and
`cargo bench --bench large_repo` runs a whole-lifecycle benchmark — a real
git client pushing/cloning/pulling a synthetic repo (default 200 commits /
2k files; `LR_COMMITS`/`LR_FILES`/`LR_DIRS` to scale it up) — reporting
wall time and R2 Class A/B op counts per phase. Set `GIT_SERVER_TIMING=1`
to break server time down by pipeline phase (scan, resolve, filelog build,
fetch selection, pack build).

Current large-repo numbers (175k objects, 57 MiB, 1000 commits × 10k files,
native release build): initial push ~6 s server CPU (0.7 s scan, 1.1 s
resolve, 1.9 s file-log build), full clone ~2 s end-to-end (~150 ms of that
is server pack-build; the rest is the git client indexing and checking out),
incremental push/pull ~100-200 ms, file API ~5-15 ms, tree/blame APIs
~50-100 ms (dominated by file-log segment parse — see above), repack ~0.4 s.

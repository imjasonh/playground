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

The document is versioned; updates are compare-and-swap on the version. This
split is the whole consistency story:

* R2 objects are immutable and written *before* the state document references
  them, so a reader can never see a dangling reference.
* A push becomes visible atomically when the CAS lands: refs, the pack
  manifest, and the file-log manifest flip together. Readers always get a
  consistent snapshot (they read the state doc once per request).
* Two concurrent pushes to the same repo: one CAS wins, the loser's commands
  are all reported `ng … concurrent update, retry` and its staged pack becomes
  garbage (cleaned by maintenance; it was never referenced).

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
4. **Validation**: each pushed ref must CAS from its advertised old value;
   ref targets must exist and (for commits) have their root tree present.
   Honest clients are fully covered because the pack itself was verified
   self-contained-or-thin-against-us; full reachability audit is a documented
   maintenance-time job rather than a push-time cost.
5. **File-log segment** (below) is built for the new commits.
6. **CAS the state document.** Only after this does report-status say `ok` —
   so every derived view is consistent the instant the client sees success.

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

Read APIs build a one-pass `FileLogView` (newest record per path, ordered so
directory-prefix queries are range scans) per request. The known scaling
limit is segment *load* time: a merged segment for a 100k-change history
parses in ~30-50 ms, which dominates tree/blame API latency on big repos.
The planned fixes are sharding segments by path prefix (so a request loads
only the shard it needs) and an in-isolate parsed-segment cache keyed by
segment id (segments are immutable, so caching is trivially safe).

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
* Merge file-log segments into one (concatenation in push order).
* Write new pack + index + merged segment, then CAS the state document; only
  after the flip delete the old objects. A racing push fails the CAS and the
  repack discards its staged output and retries next schedule — pushes always
  win over maintenance.
* The scheduled handler walks a KV registry of repos (registered on push).

Because entries are copied by (offset-sorted would be ideal; currently
oid-iteration) ranged reads, a future refinement is iterating in pack-offset
order to make source reads sequential, and coalescing adjacent ranges into
single GETs. For truly huge repos the same budgeted, resumable structure
applies: consolidate the K smallest packs per run (geometric repacking)
instead of all packs at once.

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
| push (P packs, size S) | 1 load + 1 commit | multipart: ⌈S/5MiB⌉+2; idx put: 1; filelog put: 1 | P idx + ⌈S/4MiB⌉ block reads + filelog load |
| clone (1 pack repo, size S) | 1 load | 0 | 1 idx + ⌈S/4MiB⌉ block reads |
| incremental fetch | 1 load | 0 | P idx + blocks covering the objects sent |
| file API | 1 load | 0 | P idx + blocks covering the path walk |
| blame | 1 load | 0 | P idx + filelog + blocks covering the versions |
| repack (size S) | 1 load + 1 commit | ⌈S/5MiB⌉+2 + deletes | ⌈S/4MiB⌉ block reads + idx reads |

Measured on the large-repo benchmark (175k objects, 57 MiB stored): push 31
Class B, clone 12, incremental push/pull ≤ 8, file/tree/blame APIs ≤ 10,
repack 14. The MemStore in the test suite counts these classes, and the
integration tests assert the bounds (e.g. clone performs zero Class A
operations).

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

* Push ingest: carry buffer + 32 KiB scratch + ~50 B/entry; the pack itself
  streams through 5 MiB multipart parts.
* Delta resolution: byte-budgeted cache (32 MiB); worst case one full object
  + its delta resident at once.
* Odb reads: byte-budgeted cache (48 MiB) shared within a request.
* Pack generation: writer buffer drained per entry.
* The peak resident item is a single largest object (a delta base must be
  materialized to apply a delta). Truly huge blobs (multi-GiB) would need the
  planned chunked-blob path (store large blobs undeltified; stream inflate →
  deflate per block); the wire format permits it because blob payloads can be
  copied verbatim when stored full.
* CPU: measured on the native benches, ingest scans ~30-75 MiB/s (dominated by
  zlib inflate) and pack copy ~800 GiB/s-equivalent (memcpy + SHA-1). Workers
  CPU limits (30 s HTTP, 15 min cron) bound a single push's pack scan to
  roughly a GiB per request-CPU-second budget; larger pushes need the
  documented resumable-ingest extension (scan continues from a byte offset via
  ranged reads after the upload completes).

## Consistency summary

| Guarantee | Mechanism |
|---|---|
| Push atomicity (all-or-nothing visibility) | single CAS on the DO state document |
| Read snapshot isolation | state doc read once per request; all R2 objects it names are immutable |
| Blame/file APIs consistent immediately after push | file-log segment built and referenced in the same CAS, before report-status |
| Concurrent pushes | DO CAS; loser gets `ng … retry` |
| Repack vs push race | repack CAS loses, discards staged output |
| Crash mid-push | staged pack unreferenced; state untouched; multipart upload GC |

## What's deliberately out of scope (prototype)

* **Auth**: single hook point at the router; Workers-native options (service
  tokens, Access) slot in front.
* **Shallow/partial clone (`filter`, `deepen`)**: rejected with a clean
  protocol error; design accommodates them later (the object walk is already
  the isolation point).
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

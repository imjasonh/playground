# Design: migrating large repositories (`/migrate`)

Status: **design only, not yet built.** This document proposes how to ingest
repositories that are too large to arrive through a normal `git push`, and how
to keep them current afterward.

## The problem

Real monorepos are 13 GB+. A stock `git push` cannot deliver one, and no
amount of server code changes that, because the wall is upstream of us:

* **Git smart-HTTP `receive-pack` is a single POST**, whose body is the whole
  pack. Cloudflare caps request bodies at the *edge*, before the Worker runs
  (~100 MB on our plan; 200/500 MB on Business/Enterprise). See
  [`design.md` → Size limits](design.md).
* Even if the bytes arrived, **one invocation cannot process 13 GB**: the pack
  scan is zlib-bound (~33 MiB/s on wasm), and the paid CPU ceiling
  (`cpu_ms = 300000`) allows ~10 GB of scan per invocation. 13 GB exceeds a
  single invocation regardless of the body cap.

So bulk ingest must be **chunked and spread across many invocations**, and the
bytes must reach us by a path that isn't the capped inbound POST.

### Can a single 13 GB push be made to work? (options considered)

| Approach | Verdict |
|---|---|
| Stock `git push` (one POST) | **No** — 100 MB edge cap, single body. |
| Raise the zone tier / Enterprise custom limit | Buys 200–500 MB, not 13 GB. |
| Grey-cloud (DNS-only) to bypass the edge cap | Removes the proxy — **and Workers with it**. Non-starter. |
| Client-side custom remote helper (`git-remote-*`) doing presigned-R2 multipart upload | **Works, and removes the cap entirely** — but requires a client install, violating the "stock git only" constraint. Worth revisiting later; noted as a future path. |
| **Server pulls from the source in bounded slices** | **Yes** — the cap is on requests *to* us; response bodies to fetches *we* make are uncapped. This is the design below. |

## Key insight: be the client, not the server

The ~100 MB limit is on **inbound requests to the Worker**. When the Worker
itself issues an outbound `fetch()` subrequest, the *response* body is not
subject to that cap. So instead of asking the user to push 13 GB *to* us, the
Worker **pulls** the repository *from* its existing home (GitHub, GitLab, any
smart-HTTP git host) as a git client, streaming each response pack to R2 —
exactly the streaming discipline the rest of the service already uses.

This reuses almost everything we have:

* `PackScanner` / pack indexing / `Odb` thin-pack base resolution
  (`OdbBases`) — a pulled pack is ingested identically to a pushed one.
* R2 multipart streaming, the `GSIX` index, `RepoState` CAS in the per-repo
  Durable Object.
* Repack for post-migration consolidation.

What's *new* is a small **git fetch client** (protocol v2 `ls-refs` + `fetch`
request emission and response parsing — the mirror of the server code we
already have) plus a **job driver**.

## The enabler for arbitrary chunking: partial clone + `want` batching

Shallow/deepen bounds history by *commit count*, which does not bound *bytes*
(one commit can introduce a multi-GB blob). The clean lever is **partial
clone** (`filter=blob:none`), which every major host supports:

1. **Skeleton fetch** — `fetch` with `filter=blob:none` returns all commits
   and trees but **no blob contents**. This is a small fraction of total size
   (the "shape" of the repo) and is what lets us enumerate everything without
   moving bulk bytes yet. For pathological histories it can still be large, so
   it may itself be split by commit range / deepen rounds.
2. **Blob backfill** — walk the stored trees to list every blob oid (and its
   size, available from the tree/pack metadata), then fetch blobs in
   **byte-bounded batches** via explicit `want <oid>` lists. Because *we*
   choose how many oids per batch, each fetch is sized to fit one invocation's
   CPU/memory/wall budget. Each batch is a self-contained pack, independently
   scannable — which is why this beats a single giant bundle (below): there is
   never a pack too big to process in one invocation.

Thin packs fall out naturally: a backfill pack's blobs attach to trees/commits
already stored, and our existing thin-pack resolution (`OdbBases` against the
current odb) handles that with no new logic.

## Endpoint & job model

```
POST /migrate            { "source": "https://…/repo.git",
                           "auth":   "<optional token>",
                           "refs":   ["refs/heads/*", …] }   → { "job": "<id>" }
GET  /migrate/<job>      → { phase, refs_discovered, objects_done,
                            bytes_done, bytes_total_est, batches_done,
                            batches_total, errors[], done: bool }
DELETE /migrate/<job>   → cancel (best-effort; leaves staged data for GC)
```

A migration is a **state machine owned by the repo's Durable Object** (the
same single-writer serialization point that makes pushes atomic), advanced by
either **Durable Object alarms** or a **Cloudflare Queue** consumer — each
wake does one bounded unit of work and schedules the next. Nothing runs in the
request that created the job; `/migrate` just enqueues and returns.

### Surfaced through the repo status API

The repo status endpoint (`GET /api/<repo>/status`) is the front door for "is
this repo usable yet?", so migration state is reported there too, not only
under `/migrate/<job>`. Its `status` field — today `EMPTY` (never pushed) or
`READY` — gains a third value **`MIGRATING`** while an import is in flight,
alongside a `migration` progress object:

```jsonc
GET /api/<repo>/status
{
  "status": "MIGRATING",              // EMPTY | READY | MIGRATING
  "head": "refs/heads/main",
  "default_branch": "main",
  "last_push_ms": null,               // no accepted push yet during initial import
  "objects": 812345, "bytes": 4123456789,   // grows as batches land
  "migration": {
    "job": "<id>",
    "phase": "backfill",              // discover | skeleton | enumerate | backfill | finalize
    "batches_done": 6, "batches_total": 14,
    "bytes_done": 4123456789, "bytes_total_est": 9876543210,
    "started_ms": 1783726000000,
    "errors": []
  }
}
```

Because migration objects stay under the `refs/migrate/*` staging namespace
until the final atomic CAS, a repo reads `MIGRATING` (not `READY`) for the
whole import even as bytes accumulate; it flips to `READY` — with the target
refs and a normal `last_push_ms` / `head_commit` — only at finalize. A repo
with no active job never shows `MIGRATING`. So a client or UI can poll
`/api/<repo>/status` alone to render both "ready to clone" and "importing,
N% done" without knowing the job id. (The `EMPTY`/`READY` states and the
non-migration fields exist today; `MIGRATING` + `migration` arrive with this
importer.)

### Phases

1. **Discover** — `ls-refs` the source; record target refs and tips; estimate
   size if the host exposes it. Persist the target ref set (not yet published).
2. **Skeleton** — partial fetch (`filter=blob:none`), deepening in rounds if
   needed; stream each commit/tree pack to R2; scan + index. After this the
   full commit/tree graph is present; only blob contents are missing.
3. **Enumerate & plan** — walk stored trees to produce the set of blob oids not
   yet present, partitioned into byte-bounded batches (target ~1 GB each, well
   under the ~10 GB CPU ceiling, leaving margin for memory and wall time). The
   batch frontier is checkpointed so enumeration itself is resumable.
4. **Backfill** — for each batch: `fetch` the `want` list from the source,
   stream the pack to R2, scan/index. Batches are independent, so this is the
   parallelizable phase (though index/state writes still serialize at the DO).
   A cursor advances only when a batch is durably complete.
5. **Finalize** — verify connectivity of each target tip (every reachable
   object now present), then **atomically publish the target refs via one DO
   CAS**. Optionally trigger a repack to consolidate the many migration packs
   into one.
6. **Steady state** — normal pushes keep the repo current; or a scheduled
   re-pull reuses phases 1–5 incrementally to mirror an upstream.

Until finalize, migration objects live under a **staging ref namespace**
(e.g. `refs/migrate/<job>/…`) so a half-done import is never visible on the
real refs, and a concurrent normal push can proceed through the same DO
without seeing partial state.

## Bounding each invocation

| Budget | Limit | Batch target | Basis |
|---|---|---|---|
| CPU | 300 s (`cpu_ms`) | ~1 GB | ~33 MiB/s scan ⇒ ~10 GB ceiling; 1 GB ≈ 30 s, generous margin |
| Memory | 128 MiB isolate | streamed | pack streamed to R2; scanner holds carry buffer + 32 KiB scratch + ~50 B/entry |
| Wall time | Queue/alarm budget | one batch | one fetch + stream per wake; chain to next |
| R2 | — | multipart per batch | Class A writes per part; egress from source is inbound (free); serving later is free egress |

**Cost of a one-time 13 GB import** is dominated by R2 storage
($0.015/GB·month ≈ $0.20/mo for 13 GB) plus Class A writes for the multipart
uploads and indexes — a handful of dollars once, then normal read costs. The
pull bandwidth from the source is free ingress on the Workers side.

## Consistency, resumability, idempotency

* **Single writer.** The DO owns the job and all state transitions; no races
  with pushes or with itself.
* **Content-addressed packs.** Re-running a batch is idempotent — packs are
  named by their checksum, and state advances only by CAS.
* **Crash/timeout mid-batch** leaves either a completed+indexed pack or a
  discarded staged upload; the batch cursor never advances on partial work, so
  the next wake retries cleanly.
* **Atomic cutover.** Target refs appear only at finalize, in one CAS — the
  repo is either pre-migration or fully migrated to the caller, never
  half-populated.
* **Cancellation / GC.** Cancelled or abandoned jobs leave staging packs that
  a scheduled sweep (or the existing repack/orphan logic) reclaims.

## Failure handling

* Per-batch retry with backoff; a batch that repeatedly fails (e.g. a single
  object larger than a batch/CPU budget) is surfaced in job status rather than
  wedging the job.
* Source rate-limiting or downtime → backoff and resume; the job is durable.
* Auth for private sources: the token is used for the job's fetches and should
  be held only as long as needed (encrypted at rest if persisted across
  wakes); document the trust boundary.

## Steady state — and a correction on "1 GB pushes"

One assumption to flag: **steady-state pushes are still bound by the same
~100 MB inbound cap**, not 1 GB. A push under ~100 MB just works. Between
~100 MB and ~1 GB it must be delivered as **several sequential ≤100 MB
pushes** (`git push origin <older-sha>:<ref>`, then progressively newer
commits) — which the architecture already supports transparently: each push is
independent, and the nightly repack consolidates the resulting packs. So 1 GB
of new history is "reasonably achievable" as ~10+ chained pushes (scriptable
as a thin wrapper), not as one atomic push. If genuine single >100 MB pushes
become a hard requirement, the options are a higher zone tier or the
client-side remote helper noted above. Alternatively, a repo that has a
canonical upstream can skip pushing entirely and rely on scheduled re-pull
(phases 1–5).

## Alternative migration path: bundle-to-R2 (no fetch client)

For a **one-time import where the operator has a working clone**, a simpler
path avoids implementing a git client at all:

1. Client runs `git bundle create repo.bundle --all` and uploads it to a
   **presigned R2 URL** (direct to R2, bypassing the Worker and its inbound
   cap; multipart supports up to 5 TB).
2. A `/ingest-bundle` endpoint reads the bundle from R2 and ingests its pack.

Trade-off: a bundle is a *single* pack, so ingesting a 13 GB bundle hits the
same per-invocation CPU wall — it works only up to the ~few-GB scan ceiling
**unless** we build a resumable scanner (serialize inflate state across
invocations; the "resumable ingest" extension). The client can sidestep that
by producing **multiple bundles by commit range**, each under the ceiling —
essentially split-push over presigned R2 uploads. This path needs no source
credentials and no fetch-client code, at the cost of client-side scripting and
(for the multi-bundle case) manual range selection. Good for a controlled
one-shot migration; the pull-based design is better for mirroring an upstream
and for ongoing sync.

## What building this requires (not in scope now)

* A minimal **protocol-v2 git fetch client** in the Worker: emit
  `ls-refs`/`fetch` (incl. `filter` and explicit `want` batches), parse the
  acknowledgments + packfile side-band response. This is the mirror of code we
  already have on the server side and reuses the pack scanner/indexer verbatim.
* A **job driver** (DO alarms or a Queue) and the `/migrate` + status API.
* Blob **enumeration + byte-bounded batching** with a resumable frontier.
* Optional: presigned-R2 upload + `/ingest-bundle` for the alternative path.
* Note: our *server* currently rejects inbound `filter`/`deepen` fetch options
  (we don't yet *serve* partial clones). That is independent of *emitting*
  them as a client; serving partial clones is separate future work.

## Open questions & risks

* **Source capability.** Partial clone requires the source to support
  `filter`. GitHub/GitLab do; an arbitrary host may not — fall back to
  shallow + deepen by commit range, which bounds by commits, not bytes (risk:
  a single commit introducing huge blobs).
* **Single object larger than the CPU budget.** An individual blob that cannot
  be inflated + hashed within ~300 s CPU (~10 GB) is a hard limit — genuinely
  LFS territory; such objects should be detected during enumeration and
  reported rather than retried forever.
* **Skeleton size.** For extreme histories the `filter=blob:none` skeleton is
  itself large; deepen-round splitting must be able to bound it.
* **Interaction with repack.** Migration produces many packs; finalize should
  hand off to repack so the first clone after migration is served from one
  consolidated pack.

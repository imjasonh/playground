# Design: incremental repacking for large repositories

Status: **core algorithm implemented; hard cases still future.** The bounded
consolidation below shipped in `maintenance::repack`: budget-bounded
contiguous selection (bytes / objects / pack count, sliding-window, never
selecting a pack too big to fold), partial odb open (only selected indexes),
verbatim streaming copy, scoped file-log merge, and an atomic manifest
**swap** in the Durable Object that replaces exactly the consumed ids — so
racing pushes (which only append) never conflict with maintenance, only a
concurrent repack does — plus **deferred deletion** (consumed ids move to a
`retired` list at swap time; a later run deletes their storage after a grace
period and sweeps the list, closing the read-under-delete race noted below).
What was *not* built yet: the **segmented/checkpointed base rewrite** and
**GC**. The urgency came from a different direction than this doc
anticipated: the write-scaling load test
([`loadtest-scaling.md`](loadtest-scaling.md)) showed a *busy* repo hits the
whole-repo-repack wall via pack **count** (hundreds of small packs outrunning
consolidation, inflating every push/clone) long before any repo hits it via
size.

## Why the original whole-repo repack couldn't scale

`maintenance::repack` originally consolidated **every** pack into one, in a
single invocation, holding O(objects) metadata in memory (`all_oids()`, a
`sources` vector, a `records` vector, and every pack's whole `GSIX` index via
the odb). It was correct and cheap at the tested scale (hundreds of objects,
tens of MB) but hits three independent walls on a 13 GB / multi-million-object
repo, in this order:

1. **Memory** (~250K objects): the several O(objects) vectors + all in-memory
   indexes blow the 128 MiB isolate.
2. **Subrequest cap** (~2 GB): one invocation is limited to ~1000 subrequests;
   ranged reads + multipart part-writes for a large pack exceed it.
3. **CPU** (tens of GB): SHA-1 over the whole output pack against the 300 s
   `cpu_ms` ceiling.

See [`design.md` → Repacking](design.md). The fix is not "do the same thing
with a bigger budget" — it is to change what repack *is*.

## Change the goal: bounded pack **count**, not one pack

The current design assumes the end state is a single pack. That assumption is
what makes it O(repo). Drop it. The job of repacking is to **keep the number
of packs bounded** so reads don't fan out across hundreds of indexes — *not*
to merge everything into one file. A repo can perfectly well be served from a
handful of packs.

This reframing is what makes the work boundable, and one property of the
system makes it clean: **pushes are capped at ~100 MB** (the request-body
limit — see [`design.md` → Size limits](design.md)), so **every
incrementally-added pack is already ≤100 MB.** Maintenance therefore never has
to look at an unbounded pack unless it deliberately chooses to; it consolidates
the small end and leaves the large base pack alone.

## Steady state: an immutable base + small recent packs

```
manifest (in the Durable Object):
  [ base pack  (large, immutable)      ]   ← from an earlier consolidation / import
  [ tier pack  (≤ run budget)          ]   ← previously merged small packs
  [ push pack, push pack, …  (≤100 MB) ]   ← recent pushes, newest last
```

Reads open all packs (a handful) and locate objects newest-pack-first, as
today. Maintenance's steady-state job is only to fold accumulated push packs
into the tier, and occasionally fold the tier forward — **never to rewrite the
base.** In normal operation the base is written once (by import or a rare full
rebuild) and never touched again.

## The incremental consolidation algorithm (the core)

One maintenance run:

1. **Select** — from the manifest, take packs from the small end while the
   running totals stay within *all* per-run budgets (below): cumulative
   bytes, object count, and estimated subrequests. Never select the base
   unless a base rebuild was explicitly requested. Typical selection: the
   recent push packs plus the current tier pack, when their combined size is
   within budget.
2. **Open only the selected packs.** This is the crucial feasibility point:
   consolidation loads only the `GSIX` indexes of the packs it is merging
   (bounded by the object budget) and **never opens the base pack.** It does
   *not* need the base, because objects are copied **verbatim** — a
   `REF_DELTA` entry is copied compressed with its recorded base oid
   (position-independent), so resolving the delta (which would need the base)
   is unnecessary. No base index load, no base bytes read.
3. **Stream-copy** the selected objects into one new pack via an R2 multipart
   upload, in `(source pack, offset)` order so reads walk each source
   sequentially through the block cache; payloads copied in ≤1 MiB pieces so
   no whole object is resident. Build the new pack's `GSIX` from the copied
   entries' recorded metadata (bounded by the object budget). De-duplicate
   oids that appear in more than one selected pack, keeping the
   newest-manifest copy.
4. **Merge file-log** segments for exactly the selected packs into one
   re-sharded segment (already bounded — the segments belong to ≤100 MB
   pushes; see [`design.md` → Path-range sharding](design.md)).
5. **Atomic swap** — one Durable Object CAS replaces the selected pack ids
   (and their file-log segment ids) in the manifest with the single new pack
   (and merged segment). Because the manifest is the sole source of truth and
   packs are immutable, readers see either the pre- or post-consolidation set,
   never a mix.
6. **Deferred deletion** — the superseded packs/indexes/segments are *not*
   deleted immediately (a reader that loaded the old manifest may still be
   reading them). They are tombstoned and swept by a later run after a grace
   period, once no request could still hold the old manifest. (The current
   repack deletes immediately after CAS — a narrow but real race this design
   closes.)

Everything here is bounded by the selection budget, so one invocation always
suffices; no resumability is needed for the steady-state path.

## Per-run budgets (tied to the limits)

| Budget | Cap | Per-run target | Why |
|---|---|---|---|
| Subrequests | ~1000 / invocation | ≤ ~800 ops ⇒ **≤ ~1 GiB** merged | reads (÷4 MiB) + multipart parts (÷5 MiB) ≈ 0.45 ops/MiB |
| Memory | 128 MiB isolate | **≤ ~250K objects** | merged indexes + new index records, resident at once |
| CPU | 300 s (`cpu_ms`) | ≪ ceiling at ≤1 GiB | verbatim copy is memcpy + SHA-1 of output only |

Selection stops at the first budget hit. Since push packs are ≤100 MB, a run
always folds in *some* progress (at least one pack), so the backlog cannot
grow unboundedly faster than maintenance clears it.

## Bounding the pack count (geometric tiers)

To keep reads from fanning across many packs, consolidation follows a
**geometric** rule (as git's own repacking does): maintain packs so each is
at least *f*× (e.g. 2×) the next smaller. A run merges the smallest packs
whose combined size is under the run budget *and* would not exceed the next
tier. This keeps the pack count at **O(log(total size))** — a 13 GB repo
settles at a small, constant-ish number of packs (base + a few tiers + the
newest pushes), each read-cheap.

A hard cap on the number of "large" packs (say 4–8) bounds read fan-out even
in the worst case; reaching it is the only trigger for the expensive base
rewrite below.

## The hard cases (lower priority): base rewrite & GC

Two operations genuinely need to touch a >budget pack:

* **Reclaiming unreferenced objects** (force-pushed-away history, deleted
  refs) — true garbage collection.
* **Merging a grown tier into the base** when the large-pack cap is hit.

Both rewrite an unbounded pack and so cannot finish in one invocation. Sketch
of the safe, resumable form:

* **Segment, don't monolith.** Produce the rebuilt base as **multiple
  bounded segment packs** (each built in one invocation, ≤ run budget) rather
  than one giant pack streamed across invocations (which would need a
  multipart upload held open across scheduler gaps — fragile). The repo is
  always a set of ≤budget packs; "the base" is just the oldest segment(s).
* **Checkpointed cursor.** Progress (which source objects have been emitted
  into which new segment) is checkpointed in the DO/R2 between runs; a crash
  or timeout resumes from the last checkpoint. New segments are unreferenced
  until a final CAS swaps the whole set, so partial work is never visible.
* **GC safety — retain delta bases.** An object may be unreachable from any
  ref yet still be the base of a `REF_DELTA` object we are keeping. "Removable"
  must mean *neither reachable nor a delta base of a retained object*; a naive
  reachability sweep would dangle deltas. The conservative rule: only drop an
  object if it is unreachable **and** no retained object deltas against it
  (or, undeltify such dependents as they're copied). GC is rare and storage
  is cheap ($0.015/GB·month), so this path is low priority — consolidation
  (pack count), not GC (space), is the actual pressure.

## Companion: on-R2 index lookup for large bases

Incremental consolidation itself avoids the base, so it does **not** need this.
But *serving* a repo whose base pack has millions of objects still hits the
"load the whole `GSIX` into memory" wall in `Odb::open`. The companion piece
(already noted in [`design.md`](design.md)) is an **on-R2 index**: the sorted
`GSIX` gains a fan-out table so lookups do a handful of ranged reads
(log₂ probes) instead of loading the index, with a small hot-index cache.
Repacking and serving share this need for the base; they are companion
workstreams, and this doc's algorithm is designed so repacking can land first
(it only touches bounded packs) while base serving gets the on-R2 index.

## Safety summary

| Property | Mechanism |
|---|---|
| Atomic cutover | one DO CAS swaps manifest pack/segment ids |
| Reader isolation | manifest snapshot per request; packs immutable |
| No delete-under-reader | deferred deletion + grace-period orphan sweep |
| Crash / timeout | staged packs unreferenced until CAS; content-addressed; resumable path checkpoints |
| Racing push wins | push CASes the manifest; a stale repack CAS conflicts, aborts, and discards its staged pack (swept) |
| One repack at a time | per-repo Durable Object single-writer (+ a lease flag) |
| Delta resolvability | consolidation copies all objects of selected packs (drops nothing); GC honors the retain-delta-bases rule |

## Scheduling & observability

The nightly cron already walks the repo registry and runs `repack` per repo;
this design keeps that entry point but makes each call do **bounded** work and
return an outcome (`NoOp` / `Consolidated{packs,objects,bytes}` / `LostRace` /
`Deferred{remaining}`), logged via the existing per-invocation structured log
(`{"evt":"req","method":"CRON",…}`). A repo needing more than one run's worth
of consolidation simply makes progress each night and converges; a busy repo
can be scheduled more often.

## What building this requires (not in scope now)

* Manifest-driven **pack selection** with byte/object/subrequest budgets and
  the geometric tier rule.
* A **partial odb open** (selected packs only; never the base).
* **Deferred deletion / orphan sweep** with a grace period (replacing the
  current immediate post-CAS delete).
* For the hard cases: **segmented, checkpointed base rewrite** and a
  GC pass with the retain-delta-bases rule.
* Companion (separate): **on-R2 `GSIX` lookup** for serving large bases.

## Open questions & risks

* **Grace period length** for deferred deletion vs. request duration — long
  enough to outlast any in-flight read, short enough to bound orphan storage.
* **Tier factor & large-pack cap** tuning — trades read fan-out against how
  often the expensive base rewrite triggers.
* **Backlog vs. push rate** — if pushes arrive faster than a bounded run can
  fold them, pack count grows until maintenance catches up; needs a
  more-frequent schedule or a larger per-run budget (bounded by the caps).
* **Interaction with `/migrate`** — bulk import produces many bounded packs;
  it should hand off to this consolidation rather than attempt a single final
  repack (see [`large-repo-migration.md`](large-repo-migration.md)).

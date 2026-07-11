# Load test: per-repo write scaling

Status: **round 1 measured → fix shipped → round 2 measured.** Round 1 (after
the shallow-clone deploy, PR #91) found the per-repo write ceiling: the
whole-document CAS capped goodput at ~0.5 pushes/s regardless of concurrency.
The fix it recommended — **merge disjoint ref updates in the Durable Object
instead of whole-document CAS** — shipped in **PR #95** (the merge-apply
delta path; see [`design.md` → Storage layout](design.md)). Round 2, run
against that deploy, confirmed the ceiling is gone (12× goodput demonstrated,
zero conflicts, no server knee found) and exposed the **next** bound: under
sustained writes, packs accumulate faster than whole-repo repack consolidates
them, inflating every subsequent push and clone. Symptoms and numbers in
[Round 2](#round-2-after-merge-apply-pr-95) below.

## Round 1: the whole-document CAS ceiling

*This section describes the design **before PR #95**, in its then-current
terms — kept as measured.*

### Question under test

Every push serializes through one CAS on the repo's `RepoState` document in
its Durable Object. What successful-push throughput ("goodput") can one repo
sustain, how does it degrade under concurrency, and how far is the measured
number from the theoretical limit of the design?

#### Theoretical ceiling (derived before measuring)

The naive estimate — "only the two DO hops serialize, so a few hundred ms per
cycle, ~3–7 pushes/s" — is **wrong**, because of *where* the CAS window opens.
`receive_pack` loads the state document (capturing `version`) **before reading
the request body**, and `apply_push` CASes at that version only **after** all
the work: pack scan, thin-pack base resolution, `GSIX` indexing, file-log
build, R2 writes. Two pushes that overlap *anywhere* in that window race for
one version; the loser's entire effort is discarded and every command is
reported `ng … concurrent update, retry`.

So the true theoretical goodput of the current design is

```
goodput ≈ 1 / (full push latency)      — regardless of concurrency
```

A small push's server time is ~1.3 s (client-observed ~2 s), predicting
**~0.5 successful pushes/s per repo**, with all surplus offered load turning
into conflicts. That is exactly what the test measured.

Note the conflict unit is the **repo**, not the ref: pushes to *different
branches* still race, because both CAS the same monolithic state document.

### Methodology

One seeded repo on the production Worker (`git.imjasonh.workers.dev`),
~180 generated source files across 12 directories, ~200 KB packed.

* **Writers** (N concurrent loops): each owns a branch `load/w<N>`; per
  iteration it appends a few lines to three pseudo-random source files,
  commits, and pushes; on `concurrent update, retry` it retries with small
  jitter (up to 10 attempts). Every attempt is logged with wall-clock latency
  and outcome (`ok` / `conflict` / `err`).
* **Readers** (M concurrent loops): `git clone --depth 1` into a fresh
  directory, timed, then deleted — simulating CI fetch load.
* **Ramp**: stages of ~40 s each — writers 1, 2, 4, 8, 16, 24; then mixed
  8 writers + 32 readers; then 48 readers alone. Between stages, `POST
  /api/<repo>/repack` consolidates accumulated push packs so pack-count growth
  doesn't confound later stages.
* **Instrumentation**: client-side per-attempt timings; server-side
  `Server-Timing` headers (phase durations, R2/DO/KV op counts, µ$ cost) on
  probe requests.

Scale and cost: ~1,700 push attempts, ~2,300 shallow clones, total spend well
under $0.10. (Bounded on purpose — the knee was visible immediately, so
pushing to ~5k of each would only have burned time and pennies.)

Caveats: the load generator was a single laptop, which capped offered read
load (relevant below); a handful of clone samples during the write-only stages
came from stray reader loops of an aborted first script run and were excluded
from conclusions.

### Findings

#### 1. Push goodput is flat at ~0.5/s per repo; concurrency buys only conflicts

| writers | goodput (ok/s) | ok | conflicts | push p50 | push p95 |
|---|---|---|---|---|---|
| 1  | 0.42 | 15 | 0   | 2.2 s | 4.0 s |
| 2  | 0.42 | 16 | 16  | 2.1 s | 3.3 s |
| 4  | 0.55 | 9  | 27  | 1.5 s | 2.2 s |
| 8  | 0.46 | 20 | 121 | 2.1 s | 3.5 s |
| 16 | 0.46 | 20 | 264 | 2.0 s | 2.8 s |
| 24 | 0.50 | 22 | 403 | 2.0 s | 2.8 s |

Goodput never moves from ~0.45–0.55/s — i.e. **the measured ceiling equals the
theoretical `1 / push-latency` limit**; there is no headroom being lost to
anything else. Added concurrency converts 1:1 into conflicts: at 24 writers,
~95% of attempts lose the race, and each loser has already paid the full
scan + resolve + file-log + R2 cost before finding out (the CAS is the last
step). Winner latency stays flat (no queue buildup) and nothing errored — the
system degrades exactly as designed, just wastefully.

#### 2. Reads scale; no server ceiling found

* 8 writers + 32 readers: **18.7 clones/s**, zero errors, p50 1.4 s — and push
  goodput was unchanged (0.46/s), so reads don't interfere with writes.
* 48 readers: **29.3 clones/s**, zero errors, p50 still ~1.4 s.

Clone latency stayed flat as readers were added, meaning the *client* machine
was the bottleneck, not the Worker. Reads take no CAS (one read-only DO load
each) and fan out across isolates; the read ceiling is somewhere above what
one laptop can offer.

#### 3. Where the ~2 s push cycle actually goes

`Server-Timing` from a probe push of a three-line change:

```
total=1328ms  r2a=5 r2b=19 do=2 kv=1  cost=30µ$
push_stream_scan=286  push_resolve_index=355  filelog_load_parse=140  push_filelog_build=365
```

The two DO ops are nearly free. The cycle is dominated by **19 R2 reads** —
thin-pack base resolution against existing packs plus file-log segment loads —
each tens of ms of latency. The DO itself could sustain orders of magnitude
more commits per second; it is the R2-read-heavy pipeline *inside the CAS
window* that sets the ceiling.

#### 4. Repack held up under churn

Between stages, on-demand repack consolidated 21–23 accumulated push packs
(up to ~1,300 objects) in 4.5–9.5 s, every time, while load continued. (At
round 1's ~0.5 pushes/s this was comfortable; round 2's higher write rates
broke exactly this — see below.)

### What this means

~0.5 pushes/s ≈ 30 pushes/min per repo is fine for a team pushing feature
branches, and tight for a busy monorepo's CI/merge-queue traffic. Two facts
from the data point at the fix:

1. The contention is **artificial** for the common case. The concurrent
   writers touched disjoint refs; they conflict only because the CAS covers
   the whole state document. git's own semantics only require per-ref
   compare-and-swap (`old → new`), which `apply_push` already validates
   per-command ("fetch first").
2. The waste is **maximal**. Losers discover the conflict after doing all the
   work, so at high concurrency ~95% of compute + R2 spend is thrown away.

### Recommendation: merge disjoint ref updates in the Durable Object

**This shipped in PR #95**, essentially as specified below (the DO serves the
delta at `/apply`; `RepoState::merge_push` is the shared pure merge; every
applied push still bumps the document version so repack's whole-document CAS
loses to any racing push).

Replace the whole-document CAS with a **transactional merge apply** in the DO.
Instead of `commit(version, next_state)` — reject if anything changed — the
Worker sends the DO a *delta*:

```
apply_push_delta {
  ref_updates: [ { name, old, new } … ]   // per-ref CAS, git's actual contract
  new_pack:    PackMeta                   // append
  new_filelog: segment id(s)              // append
  last_push_ms
}
```

The DO (already the single writer) applies it atomically against its
*current* state:

* each `ref_update` succeeds iff that ref's current value equals `old`
  (per-ref CAS — same "fetch first" rule `apply_push` enforces today);
* `packs` / `filelog` are append-only sets, so concurrent pushes' appends
  commute;
* `head` fallback and `last_push_ms` are recomputed/stamped DO-side.

Two pushes to different branches now **both land**, in DO-arrival order. A
true same-ref race still fails cleanly for the loser — but per-ref, with the
other refs in its push unaffected, matching stock git behavior on a busy
remote. The loser's staged pack becomes an orphan for the existing sweep,
exactly as today.

#### Why this is the right lever

* **Ceiling moves from `1/push-latency` to DO apply throughput.** The
  serialized section shrinks from the whole ~1.3 s pipeline to one DO
  transaction (sub-ms compute + storage write). Disjoint-ref goodput scales
  with however many pushes the Workers fleet can *prepare* concurrently —
  orders of magnitude above 0.5/s.
* **It eliminates the wasted work, not just the failures.** Losers today burn
  full scan/R2 cost; under merge-apply there are almost no losers, so cost
  per landed push stops inflating under load.
* **Consistency is preserved.** The DO remains the sole writer and the
  atomicity point; a push is still all-or-nothing visible (refs + pack +
  file-log referenced in one DO transaction, before report-status). The
  consistency table in [`design.md`](design.md) changes only in the
  "concurrent pushes" row: *serialize via merge-apply; only true same-ref
  races retry*.
* **It is a small change.** `apply_push` already computes everything the delta
  needs; the change is moving the last step (validate-old + write) across the
  DO boundary instead of shipping the whole document back. `MemStateStore`
  gets the same merge-apply for native tests.

#### Details to get right

* **Validation stays where the data is.** Connectivity checks ("missing
  necessary objects") need the odb and stay in the Worker, *before* sending
  the delta; the DO validates only `old`-value freshness. A push whose base
  moved after validation but whose `old` still matches is fine — that is
  git's own contract.
* **Ref deletes** (`new = 0`) and the HEAD-fallback rule move DO-side (they
  depend on post-merge state).
* **Repack keeps whole-document CAS semantics** (it rewrites the pack list
  wholesale and must lose to any racing push), which the merge-apply API can
  express as "fail if any pack id I consumed is gone" — or simply keep the
  versioned commit path alongside for maintenance.
* **Idempotency/retries**: DO transactions are atomic; a Worker retry after a
  dropped response must not double-append the pack (dedupe by pack id —
  already content-addressed).

#### Secondary lever (independent): shrink the push cycle itself

Even with merge-apply, single-writer latency (~2 s per push) is set by the 19
R2 reads. Cutting them — cache hot pack blocks / file-log tips across requests
(isolate-level caches already exist; hit rate is the issue for cold isolates),
or resolve thin-pack bases with better locality — improves *latency* for every
push, and raises the ceiling proportionally for anyone not adopting
merge-apply yet. Worth doing, but it only multiplies the serial ceiling by a
constant; merge-apply removes the serialization class entirely. Do merge-apply
first.

## Round 2: after merge-apply (PR #95)

Same methodology and a fresh seeded repo, run against the deployed
merge-apply build, with the writer ramp extended (1 → 48) since the old
ceiling was expected to be gone.

### The CAS ceiling is gone

| writers | round 1 (ok/s) | round 1 conflicts | round 2 (ok/s) | round 2 conflicts | round 2 push p50 |
|---|---|---|---|---|---|
| 1  | 0.42 | 0   | 0.39 | 0 | 2.3 s |
| 2  | 0.42 | 16  | 0.67 | 0 | 2.9 s |
| 4  | 0.55 | 27  | 1.04 | 0 | 3.5 s |
| 8  | 0.46 | 121 | 1.60 | 0 | 4.6 s |
| 16 | 0.46 | 264 | 2.46 | 0 | 5.7 s |
| 24 | 0.50 | 403 | 2.68 | 0 | 6.8 s |
| 32 | —    | —   | 3.29 | 0 | 7.5 s |
| 48 | —    | —   | **5.87** | **0** | 5.4 s |

* **Zero conflicts across ~900 concurrent branch pushes** (round 1: ~95% of
  attempts lost at 24 writers). The state document advanced through ~920
  versions without one rejected apply — the DO is nowhere near its limit.
* **Goodput scales with offered concurrency**: 12× the old ceiling at 48
  writers, and still climbing when the load generator (one laptop running 48
  `git` loops) became the bottleneck. No server-side knee was found for
  merge-apply itself.
* Mixed load sustained 2.3 pushes/s + 5.0 shallow clones/s simultaneously.

### The next ceiling: packs outrunning repack

Round 2's data shows a new, different failure shape — not a hard cap but a
**self-inflicted slowdown loop under sustained writes**:

1. Every successful push appends one pack (and usually one file-log segment)
   to the manifest. At round 1's ~0.5 pushes/s, the between-stage repack
   comfortably reset this. At several pushes/s it cannot: live pack count
   grew 17 → ~190 within minutes despite repacks between every stage.
2. **Per-push work scales with live pack count**, so each push gets slower
   and more expensive as the backlog grows. The smoking gun is a probe push
   of a three-line change at ~160 packs / ~50 file-log segments:

   ```
   total=15393ms  r2a=5 r2b=483 do=2  cost=197µ$
   push_stream_scan=400  push_resolve_index=181
   filelog_load_parse=5638  push_filelog_build=5773
   ```

   versus the same probe on a freshly-repacked repo (round 1):

   ```
   total=1328ms   r2a=5 r2b=19  do=2  cost=30µ$
   ```

   **483 R2 reads instead of 19; 15.4 s instead of 1.3 s; 6.5× the cost** —
   dominated by loading/parsing every file-log segment and resolving
   thin-pack bases across every live pack. This is what dragged push p50
   from 2.3 s (1 writer, few packs) to ~7.5 s (32 writers, ~190 packs) in
   the table above: the latency growth is pack-count inflation, not
   contention.
3. **Clones degrade the same way**: shallow-clone p50 was 1.4 s against one
   pack in round 1, ~5.4 s against ~127 packs in round 2's mixed stage —
   every read fans out across the whole pack list.
4. **Repack itself stops keeping up, then becomes a casualty.** Whole-repo
   repack time grows with pack count: 6 s at 17 packs, 23 s at 77, 56 s at
   187. During the 48-writer stage one repack invocation stalled past 10
   minutes and never returned; a retry after load stopped succeeded in 46 s
   and collapsed the repo back to one pack — after which the probe push cost
   returned to normal. Whole-repo repack is on a straight path to the
   per-invocation subrequest/CPU walls, exactly as anticipated in
   [`large-repo-repacking.md`](large-repo-repacking.md).

In short: merge-apply moved the bottleneck from *concurrency control* to
*maintenance cadence*. Sustained write throughput is now bounded by how fast
consolidation keeps the live pack/file-log count low, because per-push and
per-clone work grows linearly with that count between repacks.

### Recommended next step

Implement **incremental, bounded repacking**
([`large-repo-repacking.md`](large-repo-repacking.md)): each run folds a
budget-bounded batch of small packs (geometric tiers), so maintenance does
constant-ish work per invocation and can run frequently enough to keep the
live pack count small under sustained writes — the design was written for
the large-repo case, but round 2 shows a *busy* repo hits the same wall via
pack count rather than pack size. A smaller companion lever: bound what a
push must *read* (e.g. keep file-log tip data summarized or consolidated more
eagerly), so push latency stays flat between consolidations instead of
growing with segment count.

## Reproducing

The harness is a self-contained script (writers/readers/stage ramp, CSV event
log, per-stage repack). It is not checked in; recreate from this doc or the
PR discussion. Sketch:

```bash
# seed once
git init …; <generate ~180 files>; git push origin main
# stage loop: N writers × (commit-3-file-change; push HEAD:load/w$i; retry on
# rejection), M readers × (git clone --depth 1; rm -rf), 40 s each,
# POST /api/<repo>/repack between stages; log every attempt to CSV.
# Round 1 ramp: w1..w24 + mixed + readers-only. Round 2: w1..w48 + mixed.
```

Analysis: bucket events by stage; report ok/s, conflict count, p50/p95 per
kind. Grab `Server-Timing` from a probe push (`GIT_TRACE_CURL=1 git push …`)
for the server-side phase breakdown.

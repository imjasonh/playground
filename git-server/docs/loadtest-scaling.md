# Load test: per-repo scaling

Status: **four write rounds, each fixing what the previous one found, plus a
read-ceiling hunt.**

| Round | Against | Found | Fix (next round's deploy) |
|---|---|---|---|
| 1 | whole-document CAS (post-#91) | goodput capped at ~0.5 pushes/s regardless of concurrency; surplus → conflicts | merge-apply push deltas in the DO (**PR #95**) |
| 2 | merge-apply | CAS ceiling gone (12×, zero conflicts) — but packs accumulate faster than whole-repo repack consolidates, inflating every push/clone | incremental budget-bounded repack + push-commuting swap (**PR #98**) |
| 3 | incremental repack | repack now keeps up **and** exposed delete-at-swap-time as a real bug (~5% pushes 500 mid-maintenance) | deferred deletion (retire + grace sweep, **PR #98**); then self-triggering maintenance (**PR #98**) |
| 4 | self-triggering maintenance | steady state: repo maintains itself under load, zero errors, best goodput/latency of all rounds | — (remaining levers noted at the end) |
| [Reads](#the-read-ceiling-hunting-it-from-one-machine) | round-4 build | every wall was client-side: ~46 real-git clones/s (process overhead), ~150 pack-fetches/s (client bandwidth), 7.5k+ advert req/s — server latency flat, zero errors | — (needs distributed load gen) |

Headline, per repo: **~6.7 pushes/s** and **~150 shallow-clone fetches/s**
measured simultaneously-capable on one repo, with every measured limit
sitting on the client side. And these are **per-repo** numbers: the
serialization point (Durable Object) and maintenance are per-repo, and packs
live under per-repo R2 prefixes, so two repos each sustain this
independently — total throughput scales with repo count.

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
  last_push_ms                            // internal epoch ms; API exposes RFC 3339
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

## Round 3: incremental repack (PR #98) — and a bug it flushed out

Same methodology, against the incremental-repack build, with one change:
maintenance ran **during** the write stages (a loop POSTing `/repack` every
~5 s), since "pack count stays bounded under sustained writes" was the claim
under test.

### The bounded swap works — repack stopped losing

Every consolidation landed *while pushes were in flight*: 27 consecutive
runs, all `Repacked … remaining: 0`, zero `LostRace`, each 2–16 s (vs 40–56 s
and a >10-minute stall for whole-repo repack in round 2). That confirms both
halves: bounded runs stay small, and the id-swap commutes with racing pushes
— with round 2's whole-document CAS, a repack overlapping a multi-push-per-
second workload would have lost essentially every race.

### The bug: delete-at-swap-time corrupts in-flight readers

The first round-3 run had **~5% of pushes fail with HTTP 500**: a push that
loaded the pre-swap manifest went to resolve thin-pack bases from packs the
just-landed swap had already deleted. The deferred-deletion race that the
design docs had filed under "narrow, future work" is, under sustained load,
**the common case** — a swap always lands while other requests are mid-
flight. Fixed in the same PR: swaps *retire* consumed ids into the state
document; a later run deletes their storage only after a grace period
(default 15 min, longer than any plausible request) and sweeps the list.
With that fix, the rerun had **zero failed pushes** — and better goodput at
every concurrency level than round 2:

| writers | round 2 (ok/s) | round 3 (ok/s) | round 3 errors | packs (peak → post-fold) |
|---|---|---|---|---|
| 8  | 1.60 | 2.97 | 0 | ~24 → ~12 |
| 16 | 2.46 | 3.89 | 0 | ~42 → ~22 |
| 32 | 3.29 | 4.89 | 0 | ~60 |
| 48 | 5.87 | 5.55 | 0 | ~115 → ~17 |

Pack count now oscillates in a band and resets, instead of round 2's
monotonic growth to ~190. The residual gap: with maintenance driven by an
*external* 5 s loop, a 48-writer burst still builds a transient ~115-pack
backlog before folding — and every pack of backlog taxes every request.

## Round 4: self-triggering maintenance (PR #98)

Final piece: after an accepted push, if the repo holds ≥ 8 packs
(`REPACK_TRIGGER_PACKS`), the Worker runs a bounded repack **in the same
invocation's background** (`ctx.wait_until` — it never adds push latency).
A per-repo **maintenance lease** in the DO (test-and-set with TTL) collapses
concurrent triggers — per-push, cron, on-demand — to one runner; losers skip
with one cheap DO call (`Busy`) instead of consolidating in parallel and
losing the swap. Maintenance now scales with the push rate by construction.

The round-4 run had **no external maintenance at all** — only a passive
pack-count sampler. The repo maintained itself:

| writers | round 3 (ok/s) | **round 4 (ok/s)** | round 4 push p50 | packs median/peak |
|---|---|---|---|---|
| 8  | 2.97 | **3.69** | 1.9 s | 11 / 13 |
| 16 | 3.89 | **5.08** | 2.8 s | 19 / 28 |
| 32 | 4.89 | **5.74** | 4.7 s | 38 / 54 |
| 48 | 5.55 | **6.71** | 6.1 s | 53 / 88 |
| 16w + 32r | 2.57 + 7.2 clones/s | **4.26 + 9.8 clones/s** | 3.3 s | 20 / 55 |

Zero errors, zero conflicts, ~1,290 pushes + ~600 clones. Best goodput and
latency of all rounds at every level — single-writer p50 is back to ~1.9 s
(round 2 under backlog: up to 7.5 s), and the mixed stage sustained ~14
requests/s of combined git traffic on a self-maintaining repo. Pack count
tracks the write rate (roughly `writers + trigger`) instead of time, which
is the designed steady state: the backlog a push sees is bounded by what
accumulates during one bounded repack run.

### Where the ceiling sits now

Not found yet — goodput was still climbing at 48 writers with the load
generator (one laptop) saturated, and p50 latency growth at high concurrency
tracks the transient backlog (~50 packs), which is client-offered-rate
dependent. The remaining known levers, in likely order of value:

1. **Bound what a push reads while backlog exists** — thin-pack base
   resolution and file-log loading still fan out across the live packs, so
   per-push cost rises with the in-band backlog (~50 packs ⇒ ~6 s p50 at 48
   writers). File-log tip summaries or hot-index caching would flatten it.
2. **Distributed load generation** to find the true server-side knee (the
   read-ceiling hunt below confirms one machine can't reach it).
3. The large-repo hard cases (base rewrite, GC) from
   [`large-repo-repacking.md`](large-repo-repacking.md) — orthogonal to
   write throughput.

## The read ceiling: hunting it from one machine

Round 1 measured 29.3 shallow clones/s and blamed the client without proof.
This run set out to find the actual pull ceiling reachable from one laptop
(18 cores, ~230 Mbit/s uplink), against the round-4 build and a
freshly-consolidated single-pack repo (~9,700 objects, ~900 KB packed,
~190 KB depth-1 pack). Three experiments, three *different* walls — all
client-side:

### 1. Real `git clone --depth 1 --bare`: ~46 clones/s, git-process-bound

| reader loops | clones/s | p50 | p95 | errors |
|---|---|---|---|---|
| 48  | **45.6** | 0.9 s | 1.6 s | 0 |
| 96  | 40.3 | 2.0 s | 4.6 s | 0 |
| 160 | 37.1 | 3.4 s | 8.4 s | 0 |
| 256 | 28.1 | 6.8 s | 16.8 s | 0 |

More concurrency makes it *worse* while total client CPU sits at ~55% — the
signature of per-clone process overhead (spawn + TLS handshake + disk churn)
congesting locally, not a server limit. Bare clones at the sweet spot
(~48 loops) beat round 1's non-bare 29.3/s by 1.6×.

### 2. Raw fetch POST (the expensive half of a clone): ~150/s, bandwidth-bound

Replaying the protocol-v2 fetch request directly (persistent connections, no
git, no disk) — each response is the server *building and streaming* the
~190 KB depth-1 pack:

| threads | fetches/s | client p50 | server p50 | throughput |
|---|---|---|---|---|
| 1   | 5.3   | 183 ms | 76 ms | 1.0 MB/s |
| 16  | 74.0  | 202 ms | 76 ms | 14.4 MB/s |
| 32  | 123.5 | 239 ms | 84 ms | 24.0 MB/s |
| 64  | **149.8** | 396 ms | 89 ms | **29.2 MB/s** |
| 128 | 143.9 | 827 ms | 101 ms | 28.0 MB/s |

The plateau is exactly the client's ~29 MB/s (~230 Mbit/s) link. The tell
that the server isn't the wall: **`Server-Timing` stays flat (~76–101 ms
p50) across the entire ramp** while client-observed latency quadruples —
requests are queueing on this side of the wire. Zero errors.

### 3. Raw `info/refs` (the cheap half): 7,500+ req/s, no wall found

| threads | req/s | p50 |
|---|---|---|
| 64  | 2,772 | 22 ms |
| 128 | 4,970 | 25 ms |
| 256 | **7,573** | 32 ms |

Still scaling linearly with threads at the highest offered load, server time
~0 ms, zero errors across ~230k requests. This is the request-handling path
without bulk bytes; one machine simply cannot stress it.

### Conclusion

**The server-side read ceiling was not reached by any experiment.** From one
machine: ~46 clones/s with stock git (client process overhead), ~150
clone-equivalent fetches/s at the protocol level (client bandwidth), and
7.5k+ req/s on the advertisement path (still climbing). Reads take no DO
write and fan out across Workers isolates, so the expected scaling is
horizontal until R2 or the DO's read path saturates — finding that number
needs distributed load generation (several machines, or a Workers-based
generator inside Cloudflare's network). At the measured 150 fetches/s the
repo cost ~$0.0004/s in ops (~$1.40/hour of *maximum* sustained load from
this client), so reads are cheap as well as fast.

**All of these are per-repo figures** — the DO serialization point,
maintenance lease, and R2 key prefixes are all per-repo, so N repos sustain
N× this traffic in aggregate. Two repos could each take ~6.7 pushes/s +
~150 fetches/s simultaneously without sharing any bottleneck.

## Reproducing

The harness is a self-contained script (writers/readers/stage ramp, CSV event
log, per-stage repack). It is not checked in; recreate from this doc or the
PR discussion. Sketch:

```bash
# seed once
git init …; <generate ~180 files>; git push origin main
# stage loop: N writers × (commit-3-file-change; push HEAD:load/w$i; retry on
# rejection), M readers × (git clone --depth 1; rm -rf), 40-45 s each; log
# every attempt to CSV.
# Round 1 ramp: w1..w24 + mixed + readers-only; repack between stages.
# Round 2: w1..w48 + mixed; repack between stages.
# Round 3: w8..w48 + mixed; repack POSTed every ~5 s DURING stages.
# Round 4: w8..w48 + mixed; no client-side repack at all (server
#          self-triggers); a sampler polls the status API for pack count.
# Read ceiling: (a) bare-clone loops ramped 48..256; (b) a small Python
#          harness replaying raw info/refs GETs and protocol-v2 fetch POSTs
#          (persistent connections, N threads), reporting rps, client and
#          Server-Timing latency, and MB/s.
```

Analysis: bucket events by stage; report ok/s, conflict count, p50/p95 per
kind. Grab `Server-Timing` from a probe push (`GIT_TRACE_CURL=1 git push …`)
for the server-side phase breakdown.

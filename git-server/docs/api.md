# API reference

The HTTP surface `git` exposes today. Two families share one Worker:

* the **git smart-HTTP protocol** (what `git clone` / `push` / `fetch` speak);
* a small **JSON/read API** under `/api/…` for inspecting a repo without a
  git client.

> **Keep this current:** every request path the router handles is listed here.
> Adding or changing an API method means updating this file in the same change
> (see `AGENTS.md`).

Conventions used throughout:

* `<repo>` is a single path segment: ASCII alphanumerics plus `- _ .`, not
  starting with `.`, ≤100 chars. A trailing `.git` is accepted and stripped,
  so `/foo` and `/foo.git` are the same repo.
* `<refish>` resolves in this order: a full 40-hex object id (peeled to a
  commit), `HEAD`, a branch (`refs/heads/<name>`), a tag
  (`refs/tags/<name>`), or a full ref name.
* `<path>` is a repo-relative path; the empty path means the root tree.
* Errors are JSON `{"error": "<message>"}` with a non-2xx status.
* Every response carries a `Server-Timing` header with backend op counts,
  per-phase timings, and an estimated request cost (see
  [`design.md` → Observability](design.md)).
* **No authentication** — anyone can read or push. Prototype only.

---

## git smart-HTTP

Stock `git` uses these automatically; they're documented for completeness.

### `GET /<repo>/info/refs?service=git-upload-pack`
Fetch capability advertisement. **Requires** the header `Git-Protocol:
version=2` (this server is protocol-v2-only for fetch; git ≥ 2.26 sends it by
default). Returns `application/x-git-upload-pack-advertisement`. Without the
header: `400`.

### `GET /<repo>/info/refs?service=git-receive-pack`
Push (v0) ref advertisement. Returns
`application/x-git-receive-pack-advertisement`.

### `POST /<repo>/git-upload-pack`
Protocol-v2 fetch (`ls-refs` / `fetch`). Request body is the pkt-line command;
the response (`application/x-git-upload-pack-result`) streams the packfile.
Negotiation is single-round (server ACKs and sends the pack in one response).
Shallow clone (`deepen <n>`) is supported (with a `shallow-info` section and
`--unshallow` deepening). Partial clone (`filter <spec>`) is supported for
`blob:none`, `blob:limit=<n>` (with `k`/`m`/`g` suffixes), and `tree:<depth>`;
objects that fail the filter are omitted unless named in an explicit `want`
(so a follow-up blob fetch after `blob:none` works). `deepen-since` /
`deepen-not` are rejected in-band.

Unless the client sends `no-progress`, the packfile section also carries
side-band **PROGRESS** lines with repo debug (`packs` / `objects` / `bytes` /
`retired`, `last_push` / `last_repack` / `lease_until`, and `ray` when the
edge supplied a CF-Ray) and a Server-Timing-style summary (same tokens as
the HTTP `Server-Timing` header).

### `POST /<repo>/git-receive-pack`
Push. Body is the ref-update commands followed by the packfile, streamed to R2
as it arrives. Response (`application/x-git-receive-pack-result`) is the
report-status. When the client negotiated `side-band-64k` (stock git does),
the same PROGRESS debug + Server-Timing-style lines are emitted after the
report-status. **Size limit:** the body is subject to Cloudflare's request
cap (~100 MB on our plan); over-limit pushes are refused with a readable
report-status error (see [`design.md` → Size limits](design.md)).

---

## JSON / read API

All under `/api/<repo>/…`.

### `GET /api/<repo>/refs`
All refs and the HEAD symref target.

```json
{ "head": "refs/heads/main",
  "refs": { "refs/heads/main": "<oid>", "refs/tags/v1": "<oid>" } }
```

### `GET /api/<repo>`
Repository summary — the one call for "is this repo usable, and how big?".

```jsonc
{
  "status": "READY",          // "EMPTY" (never pushed) | "READY"
  "head": "refs/heads/main",
  "default_branch": "main",   // HEAD's branch, or null if HEAD isn't a local branch
  "head_commit": "<oid>",     // oid HEAD resolves to, or null
  "last_push": "2026-07-11T14:28:00.123Z",  // RFC 3339 UTC of last accepted push, or null
  "last_repack": "2026-07-11T15:00:00.000Z", // RFC 3339 UTC of last pack consolidation, or null
  "repack_lease_until": null, // RFC 3339 UTC while a repack holds the lease, else null
  "refs": 3,                  // ref count
  "packs": 1,                 // stored pack count
  "retired": 0,               // packs/segments awaiting deferred deletion
  "objects": 12345,
  "bytes": 6789012,           // total stored pack bytes
  "version": 7                // monotonic state version
}
```

Timestamps in API responses are always RFC 3339 UTC with millisecond
precision (e.g. `2026-07-11T14:28:00.123Z`), never epoch milliseconds.

Never returns `404` for a valid repo name: an unknown repo reports
`"status": "EMPTY"`. (A future `"MIGRATING"` state with import progress is
specified in [`large-repo-migration.md`](large-repo-migration.md).)

### `GET /api/<repo>/file/<refish>/<path>`
Raw bytes of a blob at a ref/commit, as `application/octet-stream`.
`404` if the path is absent or names a directory. `404` if the repo is empty.

### `GET /api/<repo>/tree/<refish>/<path>`
Directory listing, with each entry attributed to the commit that last touched
it (from the push-time file-log index — no history walk). `<path>` empty =
root tree. `404` if the path isn't a directory.

```jsonc
{
  "commit": "<oid>",          // the resolved commit
  "path": "src",
  "entries": [
    {
      "name": "lib.rs",
      "mode": "100644",
      "kind": "blob",         // "blob" | "tree"
      "oid": "<oid>",
      "size": 2048,           // blobs only; omitted for trees
      "last_commit": "<oid>", // commit that last touched this entry; omitted if unknown
      "last_commit_time": 1700000000  // epoch seconds; omitted if unknown
    }
  ]
}
```

### `GET /api/<repo>/blame/<refish>/<path>`
Per-line attribution for a file, powered by the push-time file-log chain
(cost is proportional to the file's own change count, not repo history).
Follows the first-parent line (like `git blame --first-parent`); no rename
following. `404` if the path has no blame (never touched / not a file).

```jsonc
{
  "commit": "<oid>",
  "path": "src/lib.rs",
  "lines": [
    { "line": 1, "commit": "<oid>", "time": 1700000000 }  // line is 1-based; time is epoch seconds
  ]
}
```

### `POST /api/<repo>/loadtest`
Run a budget-capped push/pull load test against this repo from *inside* the
Worker (or the native test server). Seeds an empty repo with a small synthetic
pack when needed. Requires `"confirm": true`.

```jsonc
{
  "confirm": true,              // required guard
  "budget_usd": 0.10,           // hard spend cap (default 0.10, max 5.00)
  "duration_secs": 20,          // per-stage wall time (default 20, max 120)
  "shards": 1,                  // split concurrency across isolates (same repo)
  "stages": [                   // optional; default = writer ramp 1..48 then 64 readers
    { "writers": 8, "readers": 0 },
    { "writers": 0, "readers": 64 }
  ]
}
```

Response:

```jsonc
{
  "repo": "lt-demo",
  "tip": "<oid>",
  "budget_usd": 0.10,
  "total_cost_usd": 0.042,
  "budget_limited": false,      // true if spend hit the cap mid-run
  "peak_pushes_per_sec": 6.2,
  "peak_pulls_per_sec": 140.5,
  "cost_per_push": {
    "samples": 120,
    "mean_r2_class_a": 5.0,
    "mean_r2_class_b": 19.0,
    "mean_do": 2.0,
    "mean_kv": 1.0,
    "mean_cost_usd": 0.00003,
    "mean_ms": 180.0          // mean backend-await ms (R2/DO/KV), not isolate wall
  },
  "cost_per_pull": { "samples": 800, "mean_r2_class_a": 0, "mean_r2_class_b": 5,
                     "mean_do": 1, "mean_kv": 0, "mean_cost_usd": 0.000002, "mean_ms": 40.0 },
  "stages": [ /* per-stage goodput + costs */ ],
  "duration_ms": 45000,
  "shards": 1
}
```

Each synthetic push/pull is a normal request on the hot path, so Workers
Traces and the structured `{"evt":"req",…}` logs cover the load. The
in-process harness mirrors production auto-repack after accepted pushes
(so pack count does not climb without bound and inflate R2B) and attributes
`mean_ms` from backend awaits so concurrent writers on one isolate do not
queue into each other's latency. When
`budget_limited` is true, the peak QPS fields are still the best observed
before the cap stopped the run. Auth: same `LOADTEST_TOKEN` as
[`GET /loadtest`](#get-loadtest) (`token` JSON field, `?token=`, or
`X-Loadtest-Token`). See [`loadtest-scaling.md`](loadtest-scaling.md)
→ "In-Worker loadtest".

### `POST /api/<repo>/repack`
Trigger one pack-consolidation run now (normally a nightly cron). Each run is
budget-bounded: it folds a contiguous selection of packs and reports how many
packs it left untouched (`remaining: 0` means the repo is now one pack); call
repeatedly to converge a backlog. Returns the outcome:

```json
{ "result": "Repacked { packs: 3, objects: 549, remaining: 0 }" }
```

Other outcomes: `NoOp` (nothing to fold within budget) and `LostRace` (a
concurrent repack consumed one of the selected packs; racing *pushes* never
conflict with repack). See [`design.md` → Repacking](design.md).

---

## Root

### `GET /`
Plain-text banner identifying the service.

### `GET /loadtest`
Phone-friendly HTML load test. Open this URL in a browser:

* without `run=1` — landing page with a **cost budget** control and **Run**;
* with `?run=1` — runs immediately in-process into **one** disposable repo
  (bookmark / curl convenience; the landing **Run** button uses browser
  auto-ramp instead).

The landing **Run** button **auto-ramps** writers `1 → 2 → 4 → 8 → 16`
(one writer = one isolate; shards always equal writers). Seed is
`ensure_seeded` only (empty stages — no `load/w0` writer). Each ramp step
uses a unique `shard_index` namespace so later steps do not recreate earlier
branches. After each step it shows pushes/s live and **stops when the gain
is under 10%** (or when a step gets zero successful pushes), then measures
readers at that concurrency. Between write levels it **repacks** so the next
cold isolate does not open a multi-pack backlog; write shard POSTs run
**serially**; if a level returns Cloudflare 1101 the UI **keeps the best
completed level** and continues. The browser POSTs shards then
`POST /loadtest/merge` for the HTML report. Worker self-fetch fan-out is not
used (Cloudflare blocks same-zone Worker→Worker).

Each writer owns its own branch (`refs/heads/load/wN`); disjoint-branch
pushes merge-apply without conflicting. Defaults: `budget=0.10`,
`duration=4` seconds per ramp step, ramp ceiling `16`.

Each shard POST runs nested push/pull loops **inside one Worker
invocation**. That isolate has a shared subrequest budget and 128 MiB heap —
concurrent writers and inline auto-repack under multi-shard backlog both
threw Cloudflare Error 1101. The UI keeps **≤1 writer / ≤1 reader per
isolate**, runs **one ramp step per POST**, **skips inline auto-repack on
shard POSTs**, caps attempts per loop, opens a short pack-index tail on push
and bookends on fetch, and is guarded by
`cargo test --test phone_budget_tune` (soft subrequest/heap caps + optional
`PHONE_BUDGET_TUNE=1` search).
Heavier single-isolate ramps belong on distributed clients, not nested
in-Worker loops.

**Auth:** production requires the Worker secret `LOADTEST_TOKEN`. Pass it as
`?token=…`, or as the `X-Loadtest-Token` header. Without a matching token the
run returns 401 (HTML error page for GET). If the secret is unset, loadtests
return 503.

Optional query: `budget` (USD, default `0.10`, max `5`), `peak` (ramp
ceiling, default `16`, max `48`), `duration` (seconds per ramp step, default
`4`). Bookmark `https://git.<account>.workers.dev/loadtest?token=…` and tap
Run, or `…/loadtest?run=1&budget=0.10&token=…` for one-tap.

### `POST /loadtest/merge`
Merge shard JSON reports from a browser fan-out into one HTML report. Body:

```json
{ "confirm": true, "budget_usd": 0.10, "parts": [ /* LoadTestReport… */ ] }
```

Query: `peak`, `duration`, `token` (same auth as other loadtest routes).

Any other unmatched path is `404`.

---

## Not yet supported

* Authentication / authorization on git smart-HTTP and most `/api/…`
  routes (loadtest endpoints are gated by `LOADTEST_TOKEN` — see above).
* Date-based shallow (`--shallow-since` / `deepen-since`, `deepen-not`) —
  rejected in-band. (Depth-based shallow and partial clone `--filter` *are*
  supported.)
* SHA-256 repos.
* `/migrate` bulk import — proposed in
  [`large-repo-migration.md`](large-repo-migration.md).

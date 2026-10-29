# Plan: transactional events, a reconciler, and read-only replicas

This plan builds on the live click count and the read-only replica. It makes
events part of the write's transaction, lets pages resume where they left
off, and adds a reconciler for resources stored in the same database. Each
phase says how to demonstrate it and what to measure.

The read-only replica service is done. Everything else here is a plan, and
any number not marked as measured is an estimate to check in that phase.

## What exists today

- One writer. Cloud Run runs at most one instance, and the conditional L0
  upload rejects a second writer's commit if two instances overlap during a
  rollout.
- `Store.Write` batches concurrent requests into one SQLite transaction and
  one upload. It reruns the whole batch after a conflict, so anything a write
  computes must come from SQL inside the transaction, not from Go state.
- `internal/fanout` sends the new count to pages on the writer after the
  write returns. It is in memory and best effort.
- The read-only replica (`READ_ONLY=true`) opens the database read-only, can
  only read the bucket, and refuses POSTs. It reads the count every 100 ms,
  and sees new writes when its VFS polls, every `POLL_INTERVAL`.

## Measured baseline

Measured locally on a `file://` replica on October 29, 2026, with the
writer and one replica on the same machine:

| Measurement | Result |
|---|---|
| Click to writer page | p50 4 ms, p90 5 ms, max 21 ms (30 clicks) |
| Click to replica page, 1 s poll, 1 s count check | p50 1,364 ms, p90 1,885 ms, max 2,003 ms |
| Click to replica page, 1 s poll, 100 ms count check | p50 576 ms, p90 986 ms, max 1,069 ms |
| Replica storage requests with no writes, 2 s poll | 60 LISTs a minute (2 per poll), 4 GETs |
| Replica storage requests at 1 write a second, 2 s poll | 62 LISTs and 186 GETs a minute |
| Replica count checks between polls | 51 in 5 s, no storage reads |

On Cloud Storage, the deployed writer's uploads took 78 ms at the median
and its GETs 35 ms once warm (see the README's
[Deployed service](../README.md#deployed-service)). Expect the replica's
delay to be the poll interval plus one LIST and a few GETs.

## Prices used for estimates

- Cloud Storage, regional Standard: $0.005 per 1,000 Class A operations
  (LIST, PUT) and $0.0004 per 1,000 Class B operations (GET). See
  [Cloud Storage pricing](https://cloud.google.com/storage/pricing).
- Cloud Run, request-based billing, tier 1: $0.000024 per vCPU-second and
  $0.0000025 per GiB-second, with no free tier counted. See
  [Cloud Run pricing](https://cloud.google.com/run/pricing).
- A month is 730 hours.

Check both pages before relying on a number here.

## Phases

| Phase | Ideas | Depends on |
|---|---|---|
| 1. Events in the transaction | Outbox table, SSE event IDs and `Last-Event-ID` replay, replica fan-out from the outbox | None |
| 2. Resources and a reconciler | Resource table, in-transaction cursor, `kube` work queue | Phase 1 |
| 3. Cheap resync | Partial index on pending work, `next_reconcile_at` timer queue, chunked keyset sweep, narrow tables and covering indexes | Phase 2 |
| 4. Scale and failure | Hydration trade-offs, leader election options, load balancer split | Phases 1 to 3 |

Each phase is its own pull request with its tests, and its measurements go
in this file when it lands.

## Phase 1: events in the transaction

### Outbox table

Add a table that each write fills inside its own savepoint:

```sql
CREATE TABLE events (
  seq     INTEGER PRIMARY KEY,  -- rowid: assigned by SQLite in the transaction
  kind    TEXT    NOT NULL,     -- for example 'click'
  subject TEXT    NOT NULL,     -- for example 'counter/clicks'
  body    TEXT    NOT NULL,     -- JSON
  at      INTEGER NOT NULL      -- unix milliseconds
);
```

`POST /click` runs `UPDATE counters ...` and `INSERT INTO events ...` in the
same `Store.Write` function, so the count and its event commit together or
not at all. `seq` comes from SQLite, so a batch that reruns after a
conflict gets fresh numbers with no Go-side counter to roll back.

After the write returns, the writer reads the new rows
(`SELECT ... WHERE seq > ?`) and sends them to its pages, instead of
building the event from the request. The hub then relays committed rows
only.

A retention write deletes events older than the replay window (for
example, 10 minutes or the newest 10,000) in a later batch, never in the
request's own savepoint.

- **Performance estimate:** one more row and index entry in a transaction
  that already writes a page. SQLite time stays under 1 ms; the upload,
  78 ms on Cloud Storage, doesn't change.
- **Cost estimate:** no extra requests, because events ride in the same LTX
  upload. The LTX file grows by about one page (4 KiB) per batch.
- **Risk:** the outbox grows if retention stops. Export the row count as a
  metric.

### SSE event IDs and replay

Each SSE message carries `id: <seq>`. When the browser reconnects, it sends
`Last-Event-ID`, and the handler replays `SELECT ... WHERE seq > ? ORDER BY
seq LIMIT 1000` before it subscribes to new events. To close the race
between the replay query and the subscription, subscribe first, buffer, run
the query, then send the buffer, dropping rows at or below the last
replayed `seq`.

If `Last-Event-ID` is older than the oldest retained event, send a `reset`
event with the current state instead. The page treats that like a first
connection.

htmx's SSE extension reconnects with the browser's `EventSource`, which
sends `Last-Event-ID` automatically.

- **Performance estimate:** a replay reads a few index and table pages. On a
  warm instance that is under 1 ms; on a cold replica, a few GETs, about
  35 ms each.
- **Cost estimate:** Cloud Run closes each page's connection at the request
  timeout, 300 s by default, so each open page reconnects 12 times an hour.
  Raising the timeout to 3,600 s cuts that to once an hour.

### Replica fan-out from the outbox

Replace the replica's count check with the same `seq > last` query, every
100 ms. The replica then delivers every event, in order, with the same IDs
as the writer, so a page can move between the writer and a replica and
resume with `Last-Event-ID`. That property matters once a load balancer
spreads GETs across both.

- **Performance:** the measured replica delay stays the same: up to one poll
  plus 100 ms.
- **Cost:** no change from the measured baseline. Checks between polls read
  cached pages.

### Demonstrate phase 1

1. A store test that writes the count and event in one `Store.Write`,
   forces a conflict rerun (the existing conflict tests do this), and checks
   that no `seq` repeats or skips across the rerun.
1. A server test that connects, reads events 1 to 3, disconnects, makes two
   more clicks, reconnects with `Last-Event-ID: 3`, and gets 4 and 5 once
   each.
1. The same test against the replica, then a test that moves a page from
   the writer to the replica mid-stream.
1. A `crbench fanout` mode: N simulated pages on the writer and M on the
   replica, a click rate, and forced reconnects. It reports delivery delay
   (event `at` to receipt) at p50 and p99, lost events (must be 0),
   duplicates (allowed, counted), and replay sizes. Run it under
   `crbench soak` failure injection and with `-roll`.
1. In the UI, show the event ID next to each notice, and add a button that
   drops the connection, to show replay.

### Measure phase 1

| Metric | Target |
|---|---|
| Lost events after replay | 0 |
| Duplicate deliveries | Counted; allowed |
| Writer delivery delay p99 | Within 10 ms of today's measurement |
| Replica delivery delay p99 | Poll interval plus 200 ms |
| Outbox rows | Bounded by the retention setting |

## Phase 2: resources and a reconciler

### Resource table and in-transaction cursor

```sql
CREATE TABLE resources (
  id                  INTEGER PRIMARY KEY,
  name                TEXT    NOT NULL UNIQUE,
  generation          INTEGER NOT NULL DEFAULT 1,  -- bumped on spec change
  observed_generation INTEGER NOT NULL DEFAULT 0,  -- set by the reconciler
  next_reconcile_at   INTEGER,                     -- unix ms, or NULL
  spec                TEXT    NOT NULL,            -- JSON
  status              TEXT                         -- JSON
);
```

A spec change bumps `generation` and inserts an outbox event in the same
transaction. The reconciler writes `status`, `observed_generation`, and its
own cursor (`reconciler_cursor.seq`, the last outbox event it handled) in
one `Store.Write`. After a crash, it resumes from the cursor, and a
resource whose `observed_generation` is below its `generation` is still
pending. A status write therefore never commits without the progress that
explains it.

A status change also writes an outbox event, so pages see status the same
way they see clicks.

### Reconciler on the kube work queue

The reconciler runs on the writer only. A replica can't write, so it never
starts one. Keys are resource IDs. It reuses `kube/internal/queue`, which
already deduplicates keys, never gives one key to two workers, re-runs a key
added while it was processing, backs off on failures, and supports
`AddAfter` and two priorities.

That package is internal to `kube`, so cloudrun-sqlite can't import it.
Either move it to an exported `kube/queue` package in its own pull request
(cloudrun-sqlite then adds `replace github.com/imjasonh/playground/kube =>
../kube`, and CI tests it when `kube/` changes), or copy it. Moving it keeps
one implementation; copying keeps cloudrun-sqlite independent of `kube`'s
dependencies. Moving it is the recommendation, because the queue imports
only the standard library.

Inputs to the queue:

1. Outbox events after the cursor, at high priority, from the same 100 ms
   check that feeds pages.
1. A startup resync of pending resources, at low priority (phase 3 makes
   this cheap).
1. `next_reconcile_at` timers, through `AddAfter`.

Gaps that remain, compared with `kube`:

- No watch on an external system. A reconciler that calls an external API
  has to poll it or use `next_reconcile_at`.
- No server-side apply or field ownership. Two writers of one resource's
  status overwrite each other. Keep the reconciler the only status writer.
- External side effects aren't in the transaction. Make each one idempotent,
  keyed by resource ID and generation, because a crash between the external
  call and the status write repeats it.

### Demonstrate phase 2

1. `POST /resources`, `PUT /resources/{name}`, and a page that lists
   resources with generation, observed generation, and status, updated over
   SSE.
1. A fake external system (an in-process HTTP server in tests, a toggle in
   the demo) that counts calls per idempotency key.
1. A `crsim` test that kills the writer between the external call and the
   status write, and between the status write and the response, then checks
   convergence and that each generation's side effect ran at least once and
   was applied once.

### Measure phase 2

| Metric | Target or estimate |
|---|---|
| Convergence time from spec write to observed | p50 about one upload (78 ms) plus reconcile time; measure p99 |
| Resources stuck pending after a chaos soak | 0 |
| External calls per generation | At least 1; record the duplicate rate |
| PUTs per reconcile | Under 1; reconcile writes share batches with requests |

Cost estimate: a reconcile that writes status is one savepoint in a batch.
Unbatched, a million reconciles a month is a million PUTs, $5.

## Phase 3: cheap resync

Today a resync means reading every row. Without hydration, each cold page
is a storage GET on the store's one read connection, so a table that
doesn't fit the page cache costs time more than money: at 35 ms per GET,
2,500 cold pages (about 10 MB) take about 90 seconds and cost $0.001. That
is an estimate; measure it first.

### Partial index on pending work

```sql
CREATE INDEX resources_pending ON resources(id)
  WHERE observed_generation < generation;
```

The startup resync becomes `SELECT id FROM resources WHERE
observed_generation < generation`, which reads only that index. Its size
is the pending count, not the table size, so a resync with nothing pending
reads one page.

### Timer queue

```sql
CREATE INDEX resources_due ON resources(next_reconcile_at)
  WHERE next_reconcile_at IS NOT NULL;
```

A periodic recheck sets `next_reconcile_at` instead of relying on a full
resync. At startup, the reconciler reads the next due rows in order
(`ORDER BY next_reconcile_at LIMIT 1000`) and schedules them with
`AddAfter`. It reads further when the scheduled ones run out.

### Chunked keyset sweep

A full sweep, for drift you can't index, reads `WHERE id > ? ORDER BY id
LIMIT 500` in separate `Read` calls. Each chunk holds the read connection
briefly, so requests interleave with the sweep instead of waiting behind
it. Store the last ID in a row so a restart resumes the sweep. Never use
`OFFSET`; it reads every skipped row.

### Narrow tables and covering indexes

Move `spec` and `status` to a separate table keyed by `id`, so the hot
table holds only the scheduling columns: about 40 bytes a row, roughly 100
rows per 4 KiB page, against about 2 rows per page with 2 KB of JSON
inline. A
covering index such as `(observed_generation, generation, id)` serves the
pending query without reading table pages at all.

### Demonstrate phase 3

Extend `seed` to create N resources with a given fraction pending, and add
a `crbench resync` mode that cold-starts the server and reports time to
first reconcile, storage GETs, and bytes read for each strategy:

| Strategy | Expected cold reads |
|---|---|
| Full scan, JSON inline | Every table page |
| Full scan, narrow table | About 1 in 50 of those (estimate) |
| Partial index, 0.1% pending | A few index pages |
| Chunked sweep | Every table page, spread over time |

Run each at 10,000, 100,000, and 1,000,000 rows, with and without
`HYDRATE`.

### Measure phase 3

| Metric | Target |
|---|---|
| Resync with nothing pending, 1,000,000 rows | Under 100 ms and a handful of GETs |
| Request latency p99 during a chunked sweep | Within 2 times the idle p99 |
| Pending rows missed by the indexed resync | 0, checked against a full scan |

## Phase 4: scale and failure

### Hydration trade-offs

`HYDRATE=true` downloads the whole database in the background, after
which reads, including sweeps, are local. It costs a GET per object at
cold start and memory or disk for the copy (the scratch volume is in
memory). It suits the writer once full sweeps matter. For a replica,
hydration means each new instance downloads the database before its reads
are local, so leave it off for a small database and measure cold-start
time and GETs at 100 MB and 1 GB before turning it on.

### Leader election options

The reconciler has to run in one place. In order of preference:

1. **Cloud Run `max_instance_count = 1`, fenced by the conditional upload.**
   Two writers can overlap during a rollout, but only one commit per TXID
   uploads, so database effects stay single-writer. External side effects
   from the losing instance aren't fenced; idempotency keys cover them. No
   new code. This is the current setup.
1. **A lease row in the database.** `holder`, `expires_at`, renewed by a
   write. A write that renews the lease is fenced by the conditional upload
   too, so a holder that loses a conflict knows right away. This adds a
   write every renewal interval (one PUT, $0.005 per 1,000) and stops a
   second instance from starting reconciles at all.
1. **A lease object in Cloud Storage with generation preconditions.** It
   works without the database but duplicates what the conditional upload
   already does.
1. **`kube` shard Leases.** Needs a Kubernetes API server; not a fit for
   Cloud Run.

Demonstrate with a `crsim` rollout that overlaps two writers for 30
seconds, and count fenced commits (`conflicts` in `/stats`) and duplicate
external calls under options 1 and 2.

### Load balancer split

Later, one URL can front both services: an external Application Load
Balancer with serverless network endpoint groups for the writer and the
replica, sending GETs to the replica and other methods to the writer. Check
that the URL map can match on the method; if it can't, move writes under a
path prefix and route on that. A page served by the replica keeps its SSE
connection there, and phase 1's shared event IDs make a reconnect to either
service correct.

## Reliability checks across phases

Run `crbench soak` with failure injection after each phase, and add these
checks to its report:

- Acknowledged writes missing after a roll: 0 (`crbench live -roll` checks
  this today).
- Events lost after replay, on the writer and on the replica: 0.
- Resources pending after the soak drains: 0.
- Duplicate external calls: reported, with their keys.
- Replay requests older than retention: reported. Each one is a `reset`.

## Cost estimates

All monthly, at list prices, for one instance kept running all month by
open pages (an open SSE page is an active request, so request-based billing
charges for it and Cloud Run doesn't scale to zero):

| Item | Driver | Estimate |
|---|---|---|
| Writer compute | 1 vCPU and 512 MiB, active all month | $63.07 CPU + $3.29 memory = $66.36 |
| Replica compute | Same, per instance with an open page | $66.36 |
| Replica LISTs | 2 per poll; measured | 2 s poll: $13.14; 1 s: $26.28; 5 s: $5.26; 10 s: $2.63 |
| Replica GETs | About 3 per write; measured at 1 write a second | $3.15 at 1 write a second, proportional to the rate |
| Outbox | Rides in existing uploads | $0 in requests |
| Replay | 12 reconnects an hour per page at the default timeout, a few GETs each when cold | About $0.01 per page; nothing when the pages are cached |
| Reconciler writes | Shares batches; worst case 1 PUT each | $5 per million reconciles |
| Lease renewals (option 2) | 1 PUT per renewal | $1.31 at one every 10 s |

A replica with no open pages scales to zero and costs nothing; its CPU is
frozen between requests, so it doesn't poll either. One replica instance
with an open page at a 2 s poll and 1 write a second is about $83 a month,
and most of that is compute. `reader_max_instances` caps the worst case at
3 instances, about $250, but with a request concurrency of 1,000, one
instance holds most pages. Phase 1 adds one metric that this table
depends on: instance-hours kept active by SSE connections, from Cloud Run's
billable instance time metric.

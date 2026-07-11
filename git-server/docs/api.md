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
Plain-text banner identifying the service. Any other unmatched path is `404`.

---

## Not yet supported

* Authentication / authorization, and push-time policy checks — proposed in
  [`auth-and-push-policy.md`](auth-and-push-policy.md).
* Date-based shallow (`--shallow-since` / `deepen-since`, `deepen-not`) —
  rejected in-band. (Depth-based shallow and partial clone `--filter` *are*
  supported.)
* SHA-256 repos.
* `/migrate` bulk import — proposed in
  [`large-repo-migration.md`](large-repo-migration.md).

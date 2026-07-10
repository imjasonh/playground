# git-server

A **git smart-HTTP server** that runs on Cloudflare Workers (Rust → wasm),
storing repositories in **R2** with per-repo **Durable Objects** for
transactional ref updates. Stock `git` clients push and pull against it; a
JSON API serves file contents, directory listings, and line-level blame that
are consistent the moment a push is acknowledged.

See [`docs/design.md`](docs/design.md) for the architecture, streaming
strategy, cost model, and repacking design.

```
git clone https://<worker-host>/<repo>          # protocol v2 fetch
git push  https://<worker-host>/<repo> main     # receive-pack push

GET  /api/<repo>/refs                           # {head, refs}
GET  /api/<repo>/file/<refish>/<path>           # raw blob at branch/tag/oid
GET  /api/<repo>/tree/<refish>/<path>           # JSON listing + last-commit per entry
GET  /api/<repo>/blame/<refish>/<path>          # JSON per-line {commit, time}
POST /api/<repo>/repack                         # consolidate packs now
```

There is **no authentication** in this prototype — anyone can push. Don't
point it at anything you care about.

## Layout

| Piece | Where |
|---|---|
| pkt-line framing | `src/pktline.rs` |
| object model (SHA-1 oids, trees, commits) | `src/object.rs` |
| streaming pack scan / delta resolution / GSIX index / pack write | `src/pack/` |
| object database (ranged reads over R2) | `src/odb.rs` |
| versioned repo state (refs + pack manifest) | `src/refs.rs` |
| push pipeline, fetch selection, file-log index | `src/repo.rs` |
| protocol v2 fetch + receive-pack | `src/protocol.rs` |
| file/tree API, blame, line diff | `src/fileapi.rs`, `src/blame.rs`, `src/diff.rs` |
| repacking | `src/maintenance.rs` |
| HTTP router (shared by all runtimes) | `src/http.rs` |
| Workers glue (R2, Durable Object, KV, cron) | `src/worker_entry.rs` |

Everything except `worker_entry.rs` compiles and runs natively; the Workers
runtime is glue over the same code that the native tests exercise.

## Test

```bash
cargo test          # unit + integration (real `git` client) + isolate-memory tests
cargo bench         # hot-path benchmarks (pack scan/resolve/write, diff)
cargo clippy --all-targets

# Whole-lifecycle benchmark: real git client + synthetic large repo, with
# per-phase wall time, R2/DO operation counts, throughput, and estimated $
# cost per operation (LR_* env vars scale it up; LR_BLOB_MB adds a bulk
# binary payload; GIT_SERVER_TIMING=1 breaks down server-side phases).
cargo bench --bench large_repo

# File-log layout microbenchmark: monolithic vs path-range-sharded queries.
cargo bench --bench filelog
```

## Observability & remote benchmarking

Every response carries a `Server-Timing` header with handler/backend
milliseconds, R2/DO/KV op counts, per-phase timings, and the estimated
request cost; every request also logs one structured JSON line (view with
`npx wrangler tail --format json` or the Workers Logs dashboard — that's
where push/clone metrics live, since git clients don't surface response
headers). See "Observability" in [`docs/design.md`](docs/design.md).

```bash
# Measure a deployed backend: bulk push/clone GiB/s, per-API latency, and
# the server's own op-count/cost figures per endpoint (before/after repack).
GIT_SERVER_URL=https://git.example.workers.dev ./scripts/bench-remote.sh

# Same report against a local `wrangler dev --local` (starts it for you).
./scripts/bench-remote.sh
```

The integration tests start a localhost HTTP server backed by in-memory
storage and run actual `git clone` / `push` / `pull` / `fsck` / `blame`
against it, verifying our blame output line-by-line against `git blame`.

`tests/memory.rs` enforces the **Workers isolate memory limit** in CI: a
tracking allocator measures peak heap while a 48 MiB repo is pushed and
cloned, and fails the build if a request's transient footprint could not
fit the 128 MiB isolate (the failure mode is production 503s via
Cloudflare error 1102, so this is the regression test for it).

## End-to-end against workerd (miniflare) or a deployment

```bash
# Local: builds the wasm Worker, runs it under `wrangler dev --local`
# (real workerd with R2/DO/KV simulators), then runs the git lifecycle.
# Needs: node/npx, rust wasm32 target, worker-build
#   (cargo +stable install worker-build@0.1.14)
./scripts/e2e.sh

# Same suite against a deployed backend (creates a uniquely named repo):
GIT_SERVER_URL=https://git.example.workers.dev ./scripts/e2e.sh
```

## Deploy

Deployed by `.github/workflows/deploy-workers.yml` on pushes to `main`, like
the other Worker apps. The deploy self-provisions everything the Worker
declares: the KV repo registry (`provision-worker-kv.py` substitutes the
placeholder id) and the R2 bucket (`provision-worker-r2.py` creates
`git-server-repos` if absent). The Durable Object migration is declared in
`wrangler.toml`. A nightly cron consolidates each repo's accumulated push
packs (see `src/maintenance.rs`).

## Requirements & limitations (prototype)

* **Pushes are capped at ~100 MB each** (Cloudflare's HTTP request-body
  limit on Free/Pro zones — a push is one POST; rejected with a 413 before
  the Worker runs). The server enforces the same limit itself (configurable
  via `PUSH_LIMIT_BYTES`), so local testing behaves like production and
  clients get a readable error with the workaround: split large imports
  into several pushes of ≤100 MB (`git push origin <old-sha>:refs/heads/main`,
  then newer commits). Pulls/clones are streamed and have no practical size
  cap. See "Size limits" in [`docs/design.md`](docs/design.md).
* Clients need git ≥ 2.26 (protocol v2 for fetch — the default since 2.26).
* SHA-1 repositories (git's default object format).
* No shallow or partial clone (`--depth`, `--filter`) yet; rejected cleanly.
* Blame follows the first-parent line (like `git blame --first-parent`) and
  does not follow renames.
* No auth.

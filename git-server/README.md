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
cargo test          # unit tests + integration tests driving a real `git` client
cargo bench         # hot-path benchmarks (pack scan/resolve/write, diff)
cargo clippy --all-targets
```

The integration tests start a localhost HTTP server backed by in-memory
storage and run actual `git clone` / `push` / `pull` / `fsck` / `blame`
against it, verifying our blame output line-by-line against `git blame`.

## End-to-end against workerd (miniflare) or a deployment

```bash
# Local: builds the wasm Worker, runs it under `wrangler dev --local`
# (real workerd with R2/DO/KV simulators), then runs the git lifecycle.
# Needs: node/npx, rust wasm32 target, worker-build
#   (cargo +stable install worker-build@0.1.14)
./scripts/e2e.sh

# Same suite against a deployed backend (creates a uniquely named repo):
GIT_SERVER_URL=https://git-server-worker.example.workers.dev ./scripts/e2e.sh
```

## Deploy

Deployed by `.github/workflows/deploy-workers.yml` on pushes to `main`, like
the other Worker apps. One manual prerequisite (the deploy workflow
self-provisions KV, but not R2):

```bash
wrangler r2 bucket create git-server-repos
```

The Durable Object migration and the KV repo registry are declared in
`wrangler.toml`. A nightly cron consolidates each repo's accumulated push
packs (see `src/maintenance.rs`).

## Requirements & limitations (prototype)

* Clients need git ≥ 2.26 (protocol v2 for fetch — the default since 2.26).
* SHA-1 repositories (git's default object format).
* No shallow or partial clone (`--depth`, `--filter`) yet; rejected cleanly.
* Blame follows the first-parent line (like `git blame --first-parent`) and
  does not follow renames.
* No auth.

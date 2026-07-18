# litestream-tenants

Local benches for a **GitHub-like** Litestream layout:

| DB | Contents | Write rate |
|----|----------|------------|
| `control.db` | tenants, users, orgs, members, repo registry, ACL | rare |
| `repo-{id}.db` | PRs, comments, check runs for one repo | request path |

**Every repo API operation** runs `AuthorizeRepo` on `control.db` first (explicit
`repo_access` or org membership), then reads/writes the repo DB.

File replicas under `replicas/` stand in for GCS. Modes: `local` (hot SQLite),
`vfs-write` / `vfs-read`, `restore`.

## Run

```bash
cd litestream-tenants
CGO_ENABLED=1 go test -tags vfs -v ./...
CGO_ENABLED=1 go run -tags vfs . api -duration 5s
CGO_ENABLED=1 go run -tags vfs . all
```

### `api` — QPS with ACL on every repo op

```bash
CGO_ENABLED=1 go run -tags vfs . api \
  -mode local -duration 5s \
  -tenants 3 -repos-per-tenant 4 -users 50 \
  -prs 200 -comments 8 -checks 15 \
  -readers 32 -writers 8 \
  -control-readers 16 -control-writers 1 \
  -repo-lru 12
```

Reports:

- `control-read` — ACL lookup only  
- `control-write` — grant/replace `repo_access` (throttled)  
- `repo-read+acl` — ACL + `SELECT` PR by number  
- `repo-write+acl` — ACL + `INSERT` comment  
- **effective QPS per repo** = aggregate repo QPS ÷ repo count (uniform mix)

### `cold-open`

Restore vs VFS open + first PR point-read for one seeded repo.

## Schema (abridged)

Control: `tenants` → `orgs` / `repos`; `users`; `org_members`; `repo_access`.  
Repo: `pull_requests`, `issue_comments`, `check_runs` (slim check output).

See `schema.go` for full DDL.

## What real-world traffic can we support per repo?

Numbers below are from **local** `api -mode local` on this harness (single
process, WAL SQLite, ACL join each time). Treat them as **upper bounds**;
Cloud Run + GCS/VFS will be lower (often ~5–20× for VFS, less for local disk
on Gen2 with always-on CPU).

### Measured on this machine (`api -mode local`)

ACL on every repo op; control DB always local/hot; ~150–200 PRs/repo.

| Scenario | Control read QPS | Repo read+ACL | Repo write+ACL | Per-repo read / write |
|----------|------------------|---------------|----------------|------------------------|
| **1 hot repo** | ~88k | ~67k | ~8k | **~67k / ~8k** |
| **12 active repos** (uniform) | ~61k | ~109k agg | ~24k agg | **~9k / ~2k** each |

Control writes are paced (~180/s here) to mimic rare ACL grants.

**Per repo** when traffic is spread evenly across \(R\) hot repos on one process:

\[
QPS_{repo} \approx QPS_{aggregate} / R
\]

Ceiling is the **shard**, not a magic per-repo quota: one hot repo can consume nearly all of the aggregate.

### Product translation (one Cloud Run writer shard)

Assume **local SQLite + Litestream → GCS** for control + open repo files (API
primary). Derate local benches for Cloud Run CPU/concurrency (~2–5× conservative).

| Repo popularity | Comfortable | Spike / dedicated |
|-----------------|-------------|-------------------|
| Quiet repo among many | **1–10 req/s** | 50/s |
| Normal active repo | **20–100 req/s** mixed | ~200/s |
| Hot repo alone on shard | **~1k–10k read/s**, **~0.5k–2k write/s** | bigger CPU / own shard |
| Webhooks (checks, sync) | **tens–low hundreds write/s** aggregate / shard | shard when sustained higher |

Most real GitHub-metadata traffic is **well below** these ceilings: a shard with
**hundreds of repos**, **tens of aggregate write QPS**, and **hundreds–thousands
of read QPS** is the intended zone. Use `hash(repo_id) % K` when the hot set or
SQLite write lock saturates.

### VFS mode

`api -mode vfs-write` uses VFS only for **repo** DBs; control stays local/hot.
Expect lower and noisier write QPS than `local` (and real GCS RTT in prod). Prefer
**local + Litestream replicate** for steady API primaries; VFS for cold open /
scale-to-zero / read replicas.

### Cold start (repo DB)

With compacted replicas, first **point** PR read after VFS open stays sub-linear
in DB size; full restore and table scans scale with size. Prefer one DB per repo
so a huge monorepo doesn’t cold-start everyone else.

## Layout

```
litestream-tenants/
├── schema.go      # control + repo DDL, SeedWorld, AuthorizeRepo
├── harness.go     # Litestream open/replicate, DB LRU pool
├── bench_api.go   # api + cold-open benches
├── main.go        # CLI
└── bench_test.go
```

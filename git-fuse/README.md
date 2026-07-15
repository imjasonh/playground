# git-fuse

A **read-only FUSE adapter for [`git-server`](../git-server/)**: mount a
repository over HTTP and browse any commit as plain files — without waiting
for a clone.

```
git-fuse https://<worker-host>/<repo> /mnt/repo

cat /mnt/repo/refs/heads/main                 # -> "<sha>\n"
cat /mnt/repo/refs/HEAD                       # sha of the default branch
ls  /mnt/repo/commits/<sha>/src/              # any commit's tree
cat /mnt/repo/commits/<sha>/src/lib.rs        # any file at any commit

# The composition it's built for:
ls -R "/mnt/repo/commits/$(cat /mnt/repo/refs/heads/main)"
```

Unmount with Ctrl-C or `fusermount3 -u /mnt/repo`.

## Layout

| Path | Meaning |
|---|---|
| `/refs/<ref>` | file containing `<sha>\n` — the ref namespace with the `refs/` prefix stripped (`refs/heads/main`, `refs/tags/v1`) |
| `/refs/HEAD` | sha the default branch points at |
| `/commits/<sha>/<path>` | the tree of any commit; symlinks and exec bits preserved; submodule pointers hidden |

`/commits` itself lists nothing (its namespace is every commit), but any
existing full 40-hex sha resolves on lookup. Commit-addressed data is
immutable, so the kernel caches it aggressively; ref files are served with
short TTLs and direct IO so a `cat` always sees the current sha (default
freshness window 2 s, `--refs-ttl` to change).

## How it stays fast

Every query tries two sources, cheapest first:

1. **A shared local bare-repo cache** — one per remote URL (default
   `~/.cache/git-fuse/<repo>-<hash>.git`, `--cache-dir` to override), read
   through a persistent `git cat-file --batch-command` process. A miss costs
   microseconds, a hit serves at local-disk speed. `git maintenance run
   --auto` runs after fetches so a long-lived cache doesn't accumulate
   packs; the whole directory is disposable — deleting it just means the
   next mount warms from scratch.
2. **git-server's JSON read API** (`/api/<repo>/refs`, `/tree/…`, `/file/…`)
   — one HTTP round trip per directory or blob, no pack transfer.

At mount time nothing blocks on cloning: a background thread warms the cache
in stages — a **shallow fetch of the default branch only** (the tips almost
every read wants first; a repo like kubernetes has dozens of release
branches that would multiply this stage), then **all refs and full
history** — while reads fall through to the API. Objects switch to local
serving the moment they land. The warmup **retries with capped backoff
until the cache is a complete mirror**, so as long as a mount lives the
cache converges to all history of all files even across remote outages —
without ever making a single-file read wait on it.

**`--lazy-history`** trades that convergence for disk and bandwidth: the
warmup stops at the ref tips (every branch and tag at depth 1 — for
kubernetes ~510 MiB instead of the ~1.3 GiB full mirror), and new commits
keep accreting as tips move forward. Reading an *older* commit still works
instantly via the API; it then backfills in the background — first the
commit's snapshot (pinned with a keep-ref), then the **intervening history**
between the shallow boundary and that commit, found by deepening the
shallow clone with doubling depth until the commit connects to a ref tip
(git-server supports depth-based shallow only, so "deepen down to <sha>"
is a search). History you never read is never downloaded. Anything the staged fetches haven't covered
yet — another branch, old history, even a dangling sha — is served from the
API immediately *and* pulled into the cache by a targeted background
`git fetch <sha>`, so the next read of it is local. The mount discovers
**new pushes** via the periodic refs refresh; a changed head triggers one
incremental `git fetch`, so a repo that's already cached only ever
transfers the new objects. A second mount of the same remote reuses the
warmed cache and is local-speed immediately.

FUSE-side, requests are answered from a worker pool (a slow remote read
never stalls the mount), directory listings use `READDIRPLUS` (names +
attributes in one round trip), and blob reads are served from a
byte-budgeted in-memory LRU. Each `open()` additionally pins its blob for
the handle's lifetime, so a file bigger than the LRU budget is still
fetched once per open — never once per 128 KiB read request — and
concurrent cold reads of one blob share a single fetch.

Content integrity holds across both sources: objects arriving via
`git fetch` are hash-verified by git itself, and bytes served by the JSON
API are verified against the blob's object id before use. Blobs over 1 GiB
are refused with an error, never truncated. On-demand-fetched commits are
pinned with `refs/git-fuse/keep/*` refs in the cache so git's gc can't
prune them (the mirror refspec covers only `refs/heads/*` and
`refs/tags/*`, keeping that private namespace safe from pruning fetches),
and annotated tag shas peel to their commits identically whether served
locally or by the remote API.

## Measured performance

Both benchmarks run against the same local git-server lookalike the e2e
suite uses, with 25 ms of injected per-request latency (`BENCH_DELAY_MS` to
vary).

**`cargo bench --bench large_repo`** — a real mirror of
**kubernetes/kubernetes** (~1.3 GiB, 1.77 M objects, ~37 k tree entries at
HEAD, 1200+ refs; one-time clone cached under `target/`, or point
`LARGE_REPO_GIT_DIR` at an existing mirror):

| scenario | git-fuse | shallow clone |
|---|---|---|
| time to first byte, from nothing | **~0.25 s** | ~6.0 s (24× slower) |
| read a file at `HEAD~1000` (history on demand) | **~0.13 s** | ~2.7 s (`fetch <sha>` + read) |
| `ls -R` the whole tree (shallow-warm cache) | ~0.8 s | ~40 ms (worktree already on disk) |
| default branch fully local after | ~4.4 s | 6.0 s (the clone itself) |
| all refs + full history local after | ~105 s (background) | — (single branch only) |

**`cargo bench --bench fuse_vs_clone`** — synthetic: 201 source files plus
one 24 MiB binary asset:

| scenario | git-fuse | shallow clone + read |
|---|---|---|
| time to first byte, from nothing | **~190 ms** | ~430 ms (2.2× slower) |
| read whole tree, from nothing | ~440–550 ms | ~450 ms (≈ parity) |
| read whole tree, cache warm | ~75 ms | — (clone already paid) |

First byte never waits for a clone: it costs a couple of tree lookups plus
one blob fetch over the API, so the gap over `git clone --depth=1` grows
with repo size (2.2× on the synthetic repo, 24× on kubernetes). Historical
commits answer at API speed and then become local via the targeted fetch.
Reading *everything* cold converges to clone speed (the same bytes have to
move; the walk starts remote and finishes local as the background fetch
overtakes it), and once the cache is warm reads don't touch the network at
all.

## Run

```bash
cargo build --release
target/release/git-fuse [--cache-dir DIR] [--refs-ttl SECS] [--no-warmup] \
    [--lazy-history] [--allow-other] [--verbose] <REMOTE-URL> <MOUNTPOINT>
```

Needs `/dev/fuse` and `fusermount3` (package `fuse3`; the default features
link no libfuse). The remote must be a git-server deployment (or anything
that serves its JSON read API plus smart-HTTP).

## Test

```bash
cargo test          # unit + e2e (mounts real FUSE filesystems)
cargo bench --bench fuse_vs_clone
cargo clippy --all-targets
```

The e2e suite (`tests/e2e.rs`) starts a localhost git-server lookalike —
real smart-HTTP via the `git http-backend` CGI plus the JSON read API
implemented with git plumbing (`src/testutil.rs`) — mounts it, and drives it
through ordinary syscalls: `ls -R` composition, traversal equality against
`git ls-tree -r`, symlinks/exec bits, cold reads with smart-HTTP disabled,
offline reads from a warm cache, cache reuse across mounts, and new-commit
discovery after mount. Tests skip (loudly) when `/dev/fuse` is unavailable.

## Code layout

| Piece | Where |
|---|---|
| CLI | `src/main.rs` |
| mount lifecycle, options | `src/lib.rs` |
| FUSE filesystem (inodes, readdirplus, worker pool) | `src/fs.rs` |
| local cache (bare repo, warmup fetches, cat-file) | `src/cache.rs` |
| remote JSON API client | `src/remote.rs` |
| local-vs-remote read layer + in-memory caches | `src/source.rs` |
| test/bench harness (git-server lookalike) | `src/testutil.rs` |

## Limitations

* Read-only by design; writes are refused with `EROFS`.
* SHA-1 repos and `http(s)://` remotes only (other git transports are
  refused), matching git-server.
* `<mount>/commits` requires full 40-hex shas (no abbreviations).
* Blobs are materialized in memory per open; the hard cap is 1 GiB per
  blob (over-cap reads error — never truncate).
* Tree entry names that aren't valid UTF-8 are listed lossily: reading
  them works from the local cache (object-id addressed) but not through
  the remote API (path addressed), and two names that lossy-decode
  identically collide. The JSON API itself is UTF-8-bound.
* No authentication — same as git-server.

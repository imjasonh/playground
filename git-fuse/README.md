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
   microseconds, a hit serves at local-disk speed.
2. **git-server's JSON read API** (`/api/<repo>/refs`, `/tree/…`, `/file/…`)
   — one HTTP round trip per directory or blob, no pack transfer.

At mount time nothing blocks on cloning: a background thread warms the cache
with a **shallow fetch, then deepens to a full fetch**, while reads fall
through to the API. Objects switch to local serving the moment they land.
The mount discovers **new pushes** via the periodic refs refresh; a changed
head triggers one incremental `git fetch`, so a repo that's already cached
only ever transfers the new objects. A second mount of the same remote
reuses the warmed cache and is local-speed immediately.

FUSE-side, requests are answered from a worker pool (a slow remote read
never stalls the mount), directory listings use `READDIRPLUS` (names +
attributes in one round trip), and blob reads are served from a
byte-budgeted in-memory LRU.

## Measured performance

`cargo bench --bench fuse_vs_clone` — 201 source files plus one 24 MiB
binary asset, 25 ms of injected server latency (`BENCH_DELAY_MS` to vary),
against the same local test server the e2e suite uses:

| scenario | git-fuse | shallow clone + read |
|---|---|---|
| time to first byte, from nothing | **~190 ms** | ~430 ms (2.2× slower) |
| read whole tree, from nothing | ~440–550 ms | ~450 ms (≈ parity) |
| read whole tree, cache warm | ~75 ms | — (clone already paid) |

First byte never waits for the clone: it costs one tree walk plus one blob
fetch over the API, so the gap over `git clone --depth=1` grows with repo
size. Reading *everything* cold converges to clone speed (the same bytes
have to move; the walk starts remote and finishes local as the background
fetch overtakes it), and once the cache is warm reads don't touch the
network at all.

## Run

```bash
cargo build --release
target/release/git-fuse [--cache-dir DIR] [--refs-ttl SECS] [--no-warmup] \
    [--allow-other] [--verbose] <REMOTE-URL> <MOUNTPOINT>
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
* SHA-1 repos, matching git-server.
* `<mount>/commits` requires full 40-hex shas (no abbreviations).
* Inode table grows with distinct paths visited (no `forget` reclamation);
  fine for tool-lifetime mounts.
* No authentication — same as git-server.

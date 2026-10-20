# litevfs

`vfs.go` and `vfs_config.go` are Litestream's VFS with one unmerged fix
applied. Everything else comes from the upstream module pinned in `go.mod`.
Delete this package and use `litestream.VFS` (build tag `vfs`) once upstream
releases a fix for
[benbjohnson/litestream#1018](https://github.com/benbjohnson/litestream/issues/1018).

## Source

- Upstream: `github.com/benbjohnson/litestream` at
  [`716acc5`](https://github.com/benbjohnson/litestream/commit/716acc52ee804b2b198309d126f1315fae3c94b7)
  (`main`, 2026-10-19), the same commit `go.mod` requires.
- Merged in:
  [benbjohnson/litestream#1293](https://github.com/benbjohnson/litestream/pull/1293)
  at `8315f7d`, "fix(vfs): malformed database from stale reads during
  sustained sync writes".

The copy differs from upstream only in the package name, the removed `vfs`
build tag, and the merge. `litestream.go` aliases the upstream names the copy
uses unqualified.

## Why both

Sustained writes through the write-enabled VFS corrupt the database on every
released version and on `main`. Each fix covers a different race:

- `main` (#1478) stops an older L1 page index entry from replacing a newer L0
  entry. Without it, enabling VFS compaction corrupts the database within
  seconds, even with #1293.
- #1293 makes the poller compare remote commits against the page index it has
  installed, instead of `f.commit`, which already includes unsynced pages. On
  `main` alone, a poll that races a sync sees a "commit shrink" and replaces
  the whole index with one L0 file's pages.

## Conflict resolution

The merge conflicts in `vfs.go` resolve to #1293's sync semantics and
`main`'s L1 handling:

- A sync keeps uploaded pages in the `synced` overlay until the poller
  installs index entries for them. It does not publish the page index or
  advance `pos` itself; mixing `main`'s publish-at-sync with #1293's poller
  makes the poller re-read the writer's own files as a commit shrink.
- `pollReplicaClient` takes `pos`, the installed-index high-water mark, and
  the L1 anchor state in one critical section.
- `Lock` uses `main`'s per-replica `lastSyncedTXID` map (#1549) without
  moving `pos`.

Upstream's `go test -tags vfs .` passes on the merged tree after one
assertion change. `TestVFSFile_WriteModeCompactionPollKeepsNewerPage`
expects a sync to update the page index itself, which only `main`'s sync
does; checking that a read returns the new page instead makes it pass,
including its final check that a compacted L1 poll doesn't regress the page.

To see the full delta, diff these files against upstream `vfs.go` and
`vfs_config.go` at `716acc5`.

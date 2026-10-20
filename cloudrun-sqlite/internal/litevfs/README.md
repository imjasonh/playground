# litevfs

`vfs.go` and `vfs_config.go` are Litestream's VFS with one unmerged pull
request and two more fixes applied. Everything else comes from the upstream
module pinned in `go.mod`. Delete this package and use `litestream.VFS`
(build tag `vfs`) once upstream releases a fix for
[benbjohnson/litestream#1018](https://github.com/benbjohnson/litestream/issues/1018)
and for the two shrink fixes described in
[What each change covers](#what-each-change-covers).

## Source

- Upstream: `github.com/benbjohnson/litestream` at
  [`716acc5`](https://github.com/benbjohnson/litestream/commit/716acc52ee804b2b198309d126f1315fae3c94b7)
  (`main`, 2026-10-19), the same commit `go.mod` requires.
- Merged in:
  [benbjohnson/litestream#1293](https://github.com/benbjohnson/litestream/pull/1293)
  at `8315f7d`, "fix(vfs): malformed database from stale reads during
  sustained sync writes".
- Changed here:
  - The shrink check: `pollLevel` compares an LTX header's commit only with a
    commit at the same or an earlier TXID when it decides whether the
    database shrank.
  - Shrink truncation: when the database does shrink, the page index drops
    only the pages past the new commit, instead of every page that the files
    from the shrink on don't contain. `Truncate`, `buildIndexMap`, and the
    poller all truncate this way. A reader that holds the index during the
    poll keeps it until `Unlock`, which replaces `pendingReplace` with
    `pendingShrink` and `pendingShrinkTo`.

The copy differs from upstream only in the package name, the removed `vfs`
build tag, the merge, and the two shrink fixes. `litestream.go` aliases the
upstream names the copy uses unqualified.

## What each change covers

Sustained writes through the write-enabled VFS corrupt the database on every
released version and on `main`. Each change covers a different race:

- `main` (#1478) has two guards this copy needs. The poller doesn't treat an
  L1 file that ends before the L0 position as a shrink, and an older page
  index entry never replaces a newer one. With #1293 alone, compaction
  corrupts the database within seconds: an L1 file from before the newest L0
  file has a smaller commit, the poller takes that as a shrink, and it
  replaces the page index with that file's pages. With only the first guard,
  older L1 entries still replace newer L0 entries within one poll, the writer
  changes pages it read through them, and the replica itself is corrupt.
- #1293 makes the poller compare remote commits against the page index it has
  installed, instead of `f.commit`, which already includes unsynced pages. On
  `main` alone, a poll that races a sync sees a "commit shrink" and replaces
  the whole index with one L0 file's pages.
- The shrink check isn't upstream. `main` honors an L1 shrink when the last L1
  file in a poll reaches the L0 position, but the smaller commit can come from
  an earlier, older file in the same poll. When one poll finds two new L1
  files and the database grew after the first, the poller replaces the index
  with those files' pages and drops every page they don't contain. That needs
  two L1 compactions between polls. The server's defaults run both every 30
  seconds, so it happens when a poll and a compaction finish in a different
  order than they did in the previous period. `main` has the same bug.
- Shrink truncation isn't upstream either. With `auto_vacuum`, a `DELETE`
  shrinks the database and writes only the pages it changes, and Litestream
  replicates it as one file with a smaller commit. `main` replaces the page
  index with the pages of the files from the shrink on, which is right only
  when the transaction rewrote every page that remains, as `VACUUM` does.
  Every other page disappears. A reader on `main` takes the written pages
  for the whole database, and on the merge it fails with `page not found`,
  which SQLite reports as `database disk image is malformed`. The writer's
  `FileSize` also stayed at the old size, because `Truncate` left index
  entries past the new end, and a cold start kept those pages, because
  `buildIndexMap` merged every file without truncating. Finally, an L1 file
  compacted from L0 files older than a shrink can reach a poll after the
  shrink, so each poll also drops entries past its commit.

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

## Upstream tests

Upstream's `go test -tags vfs .` passes with this copy's `vfs.go` after three
assertion changes:

- `TestVFSFile_WriteModeCompactionPollKeepsNewerPage` expects a sync to
  update the page index itself, which only `main`'s sync does. Checking that
  a read returns the new page instead makes it pass, including its final
  check that a compacted L1 poll doesn't regress the page. The merge needs
  this change with or without the shrink fixes.
- `TestVFSFile_PendingIndexReplacementRemovesStalePages` checks the
  `pendingReplace` flag. Check `pendingShrink` and `pendingShrinkTo == 2`
  instead.
- `TestVFSFile_PollReplacementEvictsSyncedByVisibleState` shrinks the
  database to 2 pages with a file that writes only page 1, and asserts that
  page 2 is then missing from the page index. Page 2 keeps its entry from
  the writer's earlier file, so assert that the index covers it and that
  the synced copy is evicted.

`go test -tags vfs ./cmd/litestream-vfs` fails the same four
`TestHydration_E2E_SQLiteCLI` tests with this copy as on unmodified `main`;
they could not load the extension's init symbol from the `sqlite3` command
line where they ran.

To see the full delta, diff these files against upstream `vfs.go` and
`vfs_config.go` at `716acc5`.

## Interleaving tests

`interleave_test.go` drives a `VFSFile` without SQLite, against an in-memory
replica client. Polls and L1 compactions run on their own goroutines and
pause at each storage call, so a test chooses when each listing and upload
happens relative to writes, syncs, and reads. Every page read is compared
with the last version written, which fails a test at the read that returned
a stale page.

- Six named tests replay the races in
  [What each change covers](#what-each-change-covers). Two of them shrink
  the database and check the writer, a reader that polls, a reader that
  holds `SHARED` during the poll, and a cold start.
- `TestInterleaveRandom` runs 200 random schedules, or 50 with `-short`. To
  run more, set `LITEVFS_INTERLEAVE_SEEDS`. To replay a failure, set
  `LITEVFS_INTERLEAVE_SEED` to the seed it printed.
- `TestInterleaveRandomShrink` runs the same number of schedules with
  transactions that shrink the database mixed in, and reads the same
  variables. 20,000 schedules pass.
- `go test -run '^$' -fuzz=FuzzInterleave ./internal/litevfs` searches for
  failing schedules with coverage-guided fuzzing. Its schedules don't
  shrink the database.

The same file runs against an upstream checkout if you copy it into the
repository root, change its package to `litestream`, and add
`//go:build vfs`. On v0.5.17, `main`, and #1293 alone, the first random
schedule fails. On the merge without the shrink check, seed 176 fails. The
two named shrink tests and the first shrink schedule fail on v0.5.17,
`main`, #1293 alone, and the merge with or without the shrink check.

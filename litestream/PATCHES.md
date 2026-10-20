# Playground patches to Litestream

This directory is [benbjohnson/litestream](https://github.com/benbjohnson/litestream)
imported with `git subtree`, plus the patches listed here. `cloudrun-sqlite`
builds against it with
`replace github.com/benbjohnson/litestream => ../litestream`. The patches fix
data corruption in the write-enabled VFS
([benbjohnson/litestream#1018](https://github.com/benbjohnson/litestream/issues/1018))
and make its writes cheaper. Each one is meant for upstream.

## Patches

| Commit | Change | Upstream |
|---|---|---|
| `bb5a2cdc` | Merge #1293: polls compare remote commits with the installed page index, and synced pages stay in an overlay until a poll installs them | [#1293](https://github.com/benbjohnson/litestream/pull/1293), open |
| `f59dddd2` | Compare commits by TXID when looking for a shrink | Not proposed |
| `5d832c37` | Truncate the page index when the database shrinks | Not proposed |
| `b4dff65e` | Interleaving tests for the VFS | Not proposed |
| `f9801067` | Keep written pages cached when the poller installs them | Not proposed |
| `f9b60a91` | `VFS.ConflictCheckInterval`, which skips the conflict-check LIST while a writer's position is fresh | Not proposed; it needs conditional L0 uploads, which upstream's replica clients don't do |

To see every change against upstream, diff against the last import:

```bash
git diff "$(git log --grep='^git-subtree-dir: litestream$' --format=%H -1):" HEAD:litestream
```

## Rules

- Change this directory only for a patch that's meant for upstream. Don't
  restyle it: pasta skips it, and the Go dependency update leaves its
  `go.mod` at upstream's versions, so pulls from upstream merge cleanly.
- Make each patch one commit whose subject starts with `litestream:`, and
  update the table in the same commit.
- When upstream merges a patch, the next pull brings upstream's version.
  Keep upstream's version and delete the row.

## Updating from upstream

Every night, `.github/workflows/update-litestream.yml` runs
`.github/scripts/update-litestream.sh`, which runs:

```bash
git subtree pull --prefix=litestream https://github.com/benbjohnson/litestream main --squash
```

When the merge is clean, the workflow opens a pull request from
`automation/litestream-update` and enables auto-merge, so the update lands
when CI passes. When upstream's changes conflict with a patch, it commits the
merge with the conflict markers, opens the pull request without auto-merge,
and fails the run. To finish that update, check out the branch, resolve the
markers, run the tests, and push. The workflow doesn't overwrite a branch
that someone else has pushed to.

`git subtree` finds the previous import through the merge history, so pull
requests must keep landing as merge commits.

## Testing

CI runs the packages that upstream's CI unit-tests. Only the root package
gets the `vfs` build tag, because `cmd/litestream` doesn't link SQLite, which
the VFS needs:

```bash
go test -race -count=1 -tags vfs .
go test -race -count=1 ./internal ./abs ./file ./gs ./nats ./s3 ./sftp ./cmd/litestream
```

`vfs_interleave_test.go` drives a `VFSFile` without SQLite, against an
in-memory replica client. Polls and L1 compactions run on their own
goroutines and pause at each storage call, so a test chooses when each
listing and upload happens relative to writes, syncs, and reads. Every page
read is compared with the last version written. The race detector reports
none of these bugs, because every access happens under the VFS mutex.

- Six named tests replay the races in
  [What each change covers](#what-each-change-covers).
- `TestInterleaveRandom` and `TestInterleaveRandomShrink` run 200 random
  schedules each, or 50 with `-short`; the second mixes in transactions that
  shrink the database. To run more, set `LITEVFS_INTERLEAVE_SEEDS`. To replay
  a failure, set `LITEVFS_INTERLEAVE_SEED` to the seed it printed.
- `go test -tags vfs -run '^$' -fuzz=FuzzInterleave .` searches for failing
  schedules with coverage-guided fuzzing. Its schedules don't shrink the
  database.

`cloudrun-sqlite/repro` runs sustained writes through the VFS for a set time
and then checks the database; its README shows how to point it at this
directory.

## What each change covers

Sustained writes through the write-enabled VFS corrupt the database on every
released version and on `main`. Each change covers a different race:

- #1293 makes the poller compare remote commits with the page index it has
  installed, instead of `f.commit`, which already counts unsynced pages. On
  `main` alone, a poll that races a sync sees a "commit shrink" and replaces
  the whole index with one L0 file's pages. #1293 last merged `main` at
  `b052aad`, and #1455, #1506, #1478, and #1549 touched `vfs.go` since. The
  conflicts resolve to #1293's sync semantics and `main`'s L1 handling: a
  sync doesn't publish the page index or move `pos`, because mixing `main`'s
  publish-at-sync with #1293's poller makes the poller re-read the writer's
  own files as a shrink; `pollReplicaClient` takes `pos`, the
  installed-index high-water mark, and the L1 anchor in one critical
  section; and `Lock` uses #1549's per-replica `lastSyncedTXID` without
  moving `pos`.
- The TXID check: `main` (#1478) ignores an L1 file that ends before the L0
  position, but when one poll finds two new L1 files and the database grew
  after the first, the older file's smaller commit still looked like a
  shrink. The poller replaced the index with those files' pages and dropped
  every page they don't contain. That takes two L1 compactions between
  polls; with polls and L1 compactions both every 30 seconds, it happens
  when they finish in a different order than in the previous period.
- Shrink truncation: with `auto_vacuum`, a `DELETE` shrinks the database and
  writes only the pages it changes, and Litestream replicates it as one file
  with a smaller commit. The VFS replaced the page index with the pages of
  the files from the shrink on, which is right only when the transaction
  rewrote every page that remains, as `VACUUM` does. A reader on `main` took
  the written pages for the whole database, and with #1293 it failed with
  `page not found`, which SQLite reports as `database disk image is
  malformed`. The writer's `FileSize` stayed at the old size, because
  `Truncate` left index entries past the new end, and a cold start kept
  those pages, because `buildIndexMap` merged every file without truncating.
  An L1 file compacted from L0 files older than a shrink can reach a poll
  after the shrink, so each poll also drops entries past its commit.
- Cached written pages: a poll that installs a page this file uploaded
  dropped it from the synced overlay, so the next read downloaded it again.
  An entry at the same TXID holds the same bytes, so the page moves into the
  cache instead.
- `ConflictCheckInterval`: with conditional L0 uploads, an upload fails if
  another writer already published its TXID, unless that writer's file was
  deleted. The conflict-check LIST before each upload matters only for a
  writer that fell behind by more than the age at which L0 files can be
  deleted. Within the interval, a sync relies on its last listing or upload
  instead. It still lists when a poll has installed a TXID past its base,
  and when its base moved without such evidence.

## Upstream tests the patches change

- The #1293 merge: `TestVFSFile_WriteModeCompactionPollKeepsNewerPage`
  expected a sync to update the page index itself, which only `main`'s sync
  does. It checks that a read returns the new page instead.
- Shrink truncation: `TestVFSFile_PendingIndexReplacementRemovesStalePages`
  checked the `pendingReplace` flag and now checks `pendingShrink` and
  `pendingShrinkTo`. `TestVFSFile_PollReplacementEvictsSyncedByVisibleState`
  shrinks the database to 2 pages with a file that writes only page 1, and
  asserted that page 2 then left the page index. Page 2 keeps its entry from
  the writer's earlier file, so the test now expects the index to cover it.

`go test -tags vfs ./cmd/litestream-vfs` fails four
`TestHydration_E2E_SQLiteCLI` tests here with or without the patches; they
could not load the extension's init symbol from the `sqlite3` command line
where they ran. Upstream's CI doesn't run that package.

## Sending a patch upstream

Export a patch commit with paths relative to this directory, then apply it
in a Litestream checkout:

```bash
git format-patch --relative=litestream -1 <commit>
git am 0001-*.patch
```

To move the fork into its own repository, start from upstream at the last
import and apply each patch commit the same way.

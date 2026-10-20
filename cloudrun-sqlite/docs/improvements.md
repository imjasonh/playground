# Improvements

These changes make the store faster, cheaper to run, or both. The first two
are done: they're patches in the Litestream fork
([`PATCHES.md`](../../litestream/PATCHES.md)), and the store turns on the
first one. The others aren't done. Each section gives the benefit, the
reasons you might not want the change, and what it takes to keep the store
correct.

The numbers come from MinIO behind `cmd/latproxy` (20 ms per GET, 30 ms per
LIST, 50 ms per PUT), measured on builds with each change unless a section
says it's an estimate. Request costs use Cloud Storage's regional
Standard list prices: $0.005 per 1,000 Class A operations (LIST and PUT) and
$0.0004 per 1,000 Class B operations (GET). Check the
[Cloud Storage pricing page](https://cloud.google.com/storage/pricing) for
current prices.

## Summary

| Change | Speed | Cost | Correctness work | Status |
|---|---|---|---|---|
| [Skip the conflict-check LIST](#skip-the-conflict-check-list) | Durable writes 37% faster; 60% more uploads per second | Half the Class A requests per batch | Two guards and tests; a patch in the fork | Done |
| [Keep written pages cached](#keep-written-pages-cached) | No storage reads for pages this instance wrote recently | One fewer GET per such page | An exact TXID check; a patch in the fork | Done |
| [List S3 from the seek position](#list-s3-from-the-seek-position) | About twice the upload rate on S3 under sustained writes (estimate) | About 2.5 times fewer Class A requests per batch on S3 (estimate) | Small; S3 only | Not done; do it before running on S3 |
| [Snapshot less often under steady writes](#snapshot-less-often-under-steady-writes) | Frees about 2% of a vCPU per GiB of database; cold starts about 60 ms slower | Fewer upload requests | None | Done |
| [Hold commits open briefly](#hold-commits-open-briefly) | Adds the wait to every write | About 20% fewer batches at 5 writes per second (estimate) | None | Not done; make it an opt-in setting, off by default |
| [Use more read connections](#use-more-read-connections) | Parallel storage reads | Memory for each connection | Large | Not done; enlarge the cache or hydrate instead |

## Skip the conflict-check LIST

Before each upload, the VFS lists the L0 files after the writer's base TXID
(`checkForConflict` in `litestream/vfs.go`) to check whether another
instance published first. The upload is already a conditional create, which
fails if another instance published the same TXID. The LIST adds protection in
one case only: another instance published TXIDs after this writer's base, and
the file for the next TXID has since been deleted, so the conditional create
would succeed and fork the history.

The fork adds `VFS.ConflictCheckInterval`, zero by default, and the store
sets it to half of `L0Retention`.

### Expected benefit

Measured on a build without the LIST:

| | With the LIST | Without it |
|---|---:|---:|
| Upload p50 | 87 ms | 54 ms |
| Uploads per second, at most | 11.3 | 18.0 |
| Write p50, 1 writer | 89 ms | 56 ms |
| Write p50, 64 writers | 178 ms | 112 ms |
| Writes per second, 256 writers | 1,755 | 2,613 |
| Class A requests per batch | 2 | 1 |

A batch costs about $6.20 per million instead of $11.20: Class A drops from
$10 to $5 per million batches, and the 2.9 Class B requests per batch don't
change. Writing at the maximum rate costs about $290 a month at 18 uploads per
second instead of about $330 at 11.3.

With the patch in place, the steady-state runs in the README took 56 ms per
write at the median with one writer, down from 93 ms, and 8 writers made 71
writes per second instead of 42.

### Reasons not to

- It's a patch to carry in the fork until upstream takes it, and upstream
  would also need conditional L0 uploads.
- Its safety depends on retention rules in two places, the VFS and the store.
  A later change to either can break it without failing any existing test.

### What keeps it correct

1. Nothing deletes an L0 file younger than `L0Retention` (5 minutes). The
   VFS's L0 retention checks the age. The store's snapshot retention used to
   delete any file a snapshot covered, so two snapshots in quick succession,
   from two instances during a deploy or two `POST /admin/snapshot` calls,
   could delete recent L0 files. It now keeps L0 files younger than
   `L0Retention`, which `TestRetentionKeepsRecentL0Files` checks.
2. The writer skips the LIST only when it confirmed the replica's position
   within half of `L0Retention`, by its last listing or by its own last
   upload, timed from when each started. Otherwise it lists first. After a
   long idle period, for example with CPU frozen between requests, the first
   write lists. Elapsed time is the larger of the monotonic and wall-clock
   differences, so neither a paused host nor a clock step shortens it.
3. If a poll has already installed a TXID beyond the writer's base, the
   writer lists, which reports the conflict without uploading.

With these rules, any file the writer could collide with is younger than the
retention age, so it still exists and the conditional create fails.
`TestVFSFile_ConflictCheckInterval` in the fork covers each case, and the
store's tests of overlapping writers pass with the interval on.

## Keep written pages cached

After an upload, the VFS keeps the uploaded pages in a `synced` overlay until
a poll installs index entries for them, and then drops them. The next read of
such a page downloads it again, unless SQLite's own page cache (2 MB by
default) still holds it. The change moves the page into the LRU page cache
when the installed index entry has the same TXID as the overlay page, which
means the bytes are identical.

### Expected benefit

A scan of 2,000 rows (about 500 pages) written 3 seconds earlier, after a
poll, took 2.06 s and 89 GETs. With the change it took less than 1 ms and no
GETs. Each avoided GET is about 20 ms during which the single SQLite
connection holds up every other read, so the change matters most for reads of
recent writes and after bulk writes. The request savings are small: $0.40 per
million pages.

### Reasons not to

- It's another patch to carry in the fork until upstream takes it.
- Written pages take room in the 64 MiB cache, though their next read would
  have put them there anyway.

### What keeps it correct

Cache the page only when the installed entry's MaxTXID equals the overlay
page's TXID. A newer entry, from another instance or from compaction past a
later write, means the overlay page is out of date; drop it as the code does
now. Pages that the index now covers leave the overlay in one function,
`clearSyncedPageWithIndexElemWithLock`, which every caller runs after
invalidating the cache entry; the other code that clears the overlay drops
pages past the end of the database, which must not be cached.
`TestVFSFile_PollCachesSyncedPages` in the fork checks both cases, and the
interleaving tests and the store's read-visibility tests pass with it.

## List S3 from the seek position

Litestream's S3 client ignores the seek in `LTXFiles`: it lists every object
in the level and filters by TXID in the client. Each conflict check therefore
costs one LIST per 1,000 retained L0 files. With 5-minute L0 retention at 11
uploads per second, about 3,300 files are retained, so a check takes about 4
LIST requests. The Cloud Storage client passes the seek as `StartOffset` and
isn't affected. The fix passes the seek as `StartAfter`. It belongs in
Litestream, and can be a patch in the fork until then.

### Expected benefit

In a 1-minute run, conflict checks cost 1.0 LIST per batch at 10.7 uploads
per second. In 6-minute runs, which shared MinIO with other workloads, L0 grew
to 2,550 files, checks averaged 1.88 LISTs, and the rate fell to 7.1 uploads
per second. At steady state with full writes, the estimate is 4 LISTs and
about 5.5 uploads per second, which the fix brings back to 1 LIST and about
11. If the conflict-check LIST is skipped, the fix still shortens polls and
compaction.

### Reasons not to

It only matters on S3; the Terraform deploys to Cloud Storage.

### What keeps it correct

LTX file names are fixed-width hexadecimal, so lexical order is TXID order.
`StartAfter` set to the level prefix plus the seek TXID returns exactly the
files whose MinTXID is at least the seek, because those names continue past
that string. Add a test that compares the result with the client-side filter.

## Snapshot less often under steady writes

The store snapshots when a cold start would read more than 16 files at L1 or
above (`SNAPSHOT_PLAN_LEN`), checking every 15 seconds. L0 files are not
counted. Compaction folds them into L1 within 30 seconds, and a snapshot of
them reads every file back. Under steady writes the higher levels pass 16
files about once an hour.

### Expected benefit

A snapshot of a 978 MiB database took 11.7 s and 7.0 CPU-seconds, and made
198 PUT requests (multipart parts on S3; the Cloud Storage client uploads in
16 MiB chunks, about 60 requests). One every 5 minutes is about 84
CPU-seconds an hour, or about 2% of the instance's one vCPU, and about 12 GiB
uploaded and read back an hour. Both grow with database size: about 9% of
the vCPU at 3.8 GiB. Snapshotting about once an hour cuts both twelvefold.

### Reasons not to

Cold starts read more files: up to about 30 L0, 10 L1, and 12 L2 files on top
of the snapshot. The open prefetches headers and page indexes 32 at a time, so
50 more files add about three rounds of GETs, an estimated 60 ms. Retention
also keeps more small files.

### What keeps it correct

Nothing changes for correctness: a restore plan is valid at any length.

## Hold commits open briefly

The committer would wait a few milliseconds after the first write of a batch
for more writes to join it, like Kafka's `linger.ms`.

### Expected benefit

Concurrent writes already share batches whenever the committer is busy, so a
wait only helps writes that arrive while it's idle, roughly below 10 writes
per second. At 5 writes per second, a 50 ms wait would add about 0.25 writes
to each batch and remove about 20% of the batches, about $29 a month at the
current cost per batch. This is an estimate.

### Reasons not to

Every write pays the wait, including writes that end up alone in a batch. Above
about 10 writes per second the saving disappears.

### What keeps it correct

Nothing changes for correctness.

## Use more read connections

The store uses one SQLite connection, so reads that miss the cache wait for
each other's GETs: random reads over a 979 MiB database reached 21 to 40 per
second whatever the number of readers. Several connections would fetch pages
in parallel.

### Reasons not to

Each connection opens its own VFS file, with its own page cache, page index
(about 75 MiB per GiB of database), and write buffer, so memory grows with
every connection. The rule that a read waits for the batch in progress would
also have to cover every connection. A bigger `CACHE_SIZE`, or `HYDRATE=true`
for a database that fits in memory, removes the misses instead.

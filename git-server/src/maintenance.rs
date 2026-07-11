//! Scheduled maintenance: incremental pack consolidation ("repack").
//!
//! Every push adds one pack, so a busy repo accumulates many small packs.
//! That's correct but degrades everything else: each pack costs one index
//! load per request, object lookup fans out across indexes, and file-log
//! reads parse one segment per push. Repack folds packs together — **without
//! inflating or recompressing anything**:
//!
//! * full entries are copied verbatim (ranged read → multipart write);
//! * delta entries are copied verbatim too, with `OFS_DELTA` rewritten to
//!   `REF_DELTA` headers using the base oid recorded in the `GSIX` index
//!   (payload bytes untouched — a base living outside the selection keeps
//!   working, because reads resolve `REF_DELTA` bases by oid across packs);
//! * duplicate oids (an object pushed twice) keep the newest copy;
//! * the selected packs' file-log segments are merged into one.
//!
//! **Each run is bounded** (see [`RepackBudget`]): it selects the longest
//! contiguous run of packs in manifest order that fits the byte / object /
//! pack-count budgets, consolidates only those, and leaves the rest for the
//! next run. Contiguity is what makes the dedupe safe: shadowing order
//! relative to unselected packs is preserved when the consolidated pack
//! takes the selection's position. Repeated runs converge geometrically —
//! small packs fold into a tier, tiers fold forward when the budget allows,
//! and a pack too big to fold becomes the immutable "base" that maintenance
//! never rewrites (see `docs/large-repo-repacking.md`).
//!
//! The swap is atomic and **commutes with pushes**: the new pack + merged
//! file-log are written first, then the manifest swap replaces exactly the
//! consumed ids in the repo's Durable Object ([`StateStore::apply_repack`]).
//! A racing push only *appends* packs, so it can never invalidate the swap —
//! crucial now that merge-apply lets pushes land at high rate; a
//! whole-document CAS here would lose to every busy repo. The swap fails
//! only if another repack consumed one of the same ids first, in which case
//! all staged output is discarded.
//!
//! Repack runs from three triggers, all safe to overlap: the nightly cron,
//! the on-demand API, and — the one that matters under load — a **per-push
//! self-trigger** (an accepted push that leaves the repo with many packs
//! schedules a bounded run in its invocation's background via `wait_until`).
//! A per-repo **maintenance lease** in the Durable Object collapses
//! concurrent triggers to one holder: losers return [`RepackOutcome::Busy`]
//! after a single cheap DO call instead of consolidating in parallel and
//! losing the swap race.
//!
//! Superseded packs/indexes/segments are **not deleted immediately**: a
//! request that loaded the pre-swap manifest may still be reading them
//! (under sustained load this is the common case, not a corner — swaps land
//! *while* pushes and clones are in flight). The swap moves the consumed ids
//! to the state's `retired` list with a timestamp; a later run deletes the
//! storage of entries older than the grace period and sweeps them from the
//! list. Only a `LostRace` discards its own staged output immediately (it
//! was never referenced by any manifest).

use crate::odb::{index_key, pack_key};
use crate::pack::index::{EntryRecord, PackIndex};
use crate::pack::write::PackWriter;
use crate::pack::TYPE_REF_DELTA;
use crate::refs::{PackMeta, RepackSwap, RepoState};
use crate::repo::{delete_filelog, load_filelog, write_sharded_filelog, FileLogSegment, Repo};

/// Per-run consolidation budgets, sized so one run always fits a single
/// Workers invocation regardless of repo size.
#[derive(Debug, Clone, Copy)]
pub struct RepackBudget {
    /// Max cumulative bytes of selected packs. Reads (÷4 MiB block) plus
    /// multipart part-writes (÷5 MiB) cost ~0.45 subrequests/MiB, so 512 MiB
    /// stays well under the ~1000-subrequest invocation cap with room for
    /// index/file-log traffic.
    pub max_bytes: u64,
    /// Max cumulative objects: bounds resident index metadata (selected
    /// `GSIX` indexes + the new pack's records) under the 128 MiB isolate.
    pub max_objects: u64,
    /// Max packs per run: bounds per-pack overhead (index load + first
    /// ranged read each).
    pub max_packs: usize,
    /// Deferred-deletion grace period: a superseded pack's storage is
    /// deleted only this long after the swap retired it, so any request
    /// that loaded the pre-swap manifest has finished reading. Must exceed
    /// the longest plausible request (a near-cap push/clone runs minutes).
    pub grace_ms: i64,
}

impl Default for RepackBudget {
    fn default() -> Self {
        RepackBudget {
            max_bytes: 512 * 1024 * 1024,
            max_objects: 200_000,
            max_packs: 200,
            grace_ms: 15 * 60 * 1000,
        }
    }
}

/// What a repack run did.
#[derive(Debug, PartialEq, Eq)]
pub enum RepackOutcome {
    /// Nothing to consolidate within budget (0 or 1 selectable packs).
    NoOp,
    /// Consolidated `packs` packs / `objects` objects into one, leaving
    /// `remaining` packs untouched (0 = the repo is now a single pack).
    Repacked {
        packs: usize,
        objects: usize,
        remaining: usize,
    },
    /// Another repack consumed one of our selected packs first; all staged
    /// output was discarded. (Pushes never cause this — their appends
    /// commute with the swap.)
    LostRace,
    /// Another repack holds the maintenance lease; skipped without doing
    /// any work. The common way concurrent triggers (per-push self-trigger,
    /// cron, on-demand API) collapse to one run.
    Busy,
}

/// Maintenance lease TTL: must exceed the longest plausible bounded run
/// (tens of seconds) but bound how long a crashed holder blocks maintenance.
const LEASE_TTL_MS: i64 = 120_000;

/// Select the longest contiguous run of packs fitting the budget (ties go to
/// the newer window). Returns the index range into `state.packs`.
fn select_packs(state: &RepoState, budget: &RepackBudget) -> std::ops::Range<usize> {
    let packs = &state.packs;
    let (mut best_start, mut best_len) = (0, 0);
    let (mut start, mut bytes, mut objects) = (0usize, 0u64, 0u64);
    for end in 0..packs.len() {
        bytes += packs[end].bytes;
        objects += packs[end].objects;
        // Shrink until the window fits; it may become empty (start = end+1)
        // when packs[end] alone exceeds a budget — that pack is never
        // selected (it's a "base" from this run's point of view).
        while start <= end
            && (bytes > budget.max_bytes
                || objects > budget.max_objects
                || end + 1 - start > budget.max_packs)
        {
            bytes -= packs[start].bytes;
            objects -= packs[start].objects;
            start += 1;
        }
        // `>=`: prefer the newest window of equal length.
        if start <= end && end + 1 - start >= best_len {
            best_len = end + 1 - start;
            best_start = start;
        }
    }
    best_start..best_start + best_len
}

/// Consolidate a budget-bounded selection of the repo's packs into one.
/// `nonce` provides the new pack's unique storage id. One run does bounded
/// work; call repeatedly (e.g. nightly cron, or the on-demand API) to
/// converge a backlog.
pub async fn repack(repo: &Repo<'_>, nonce: &str) -> Result<RepackOutcome, String> {
    repack_with_budget(repo, nonce, &RepackBudget::default()).await
}

pub async fn repack_with_budget(
    repo: &Repo<'_>,
    nonce: &str,
    budget: &RepackBudget,
) -> Result<RepackOutcome, String> {
    let now_ms = crate::metrics::now_ms() as i64;
    // One maintainer per repo at a time: concurrent triggers skip cheaply
    // instead of consolidating in parallel and losing the swap race.
    if !repo
        .states
        .repack_lease(repo.name, now_ms, LEASE_TTL_MS)
        .await
        .map_err(|e| e.to_string())?
    {
        return Ok(RepackOutcome::Busy);
    }
    let outcome = repack_leased(repo, nonce, budget, now_ms).await;
    let _ = repo.states.repack_unlease(repo.name).await;
    outcome
}

async fn repack_leased(
    repo: &Repo<'_>,
    nonce: &str,
    budget: &RepackBudget,
    now_ms: i64,
) -> Result<RepackOutcome, String> {
    let state = repo.load_state().await?.state;

    // Deferred deletion: retired ids past their grace period can no longer
    // be referenced by any in-flight request. Delete their storage now (all
    // three keys — a segment shares its pack's id; deletes are idempotent)
    // and drop them from `retired` in this run's swap.
    let sweep: Vec<String> = state
        .retired
        .iter()
        .filter(|r| now_ms - r.ms >= budget.grace_ms)
        .map(|r| r.id.clone())
        .collect();
    for id in &sweep {
        let _ = repo.store.delete(&pack_key(repo.name, id)).await;
        let _ = repo.store.delete(&index_key(repo.name, id)).await;
        let _ = delete_filelog(repo.store, repo.name, id).await;
    }

    let range = select_packs(&state, budget);
    let selected: Vec<PackMeta> = state.packs[range.clone()].to_vec();
    let selected_ids: Vec<String> = selected.iter().map(|p| p.id.clone()).collect();
    let selected_filelog: Vec<String> = state
        .filelog
        .iter()
        .filter(|f| selected_ids.iter().any(|id| id == *f))
        .cloned()
        .collect();
    // Nothing to fold: one pack holding one merged segment is steady state.
    // Still record the sweep, if any.
    if selected.len() < 2 && selected_filelog.len() < 2 {
        if !sweep.is_empty() {
            let _ = repo
                .states
                .apply_repack(
                    repo.name,
                    &RepackSwap {
                        remove_packs: Vec::new(),
                        new_pack: None,
                        remove_filelog: Vec::new(),
                        new_filelog: None,
                        now_ms,
                        sweep,
                    },
                )
                .await;
        }
        return Ok(RepackOutcome::NoOp);
    }

    // Open only the selected packs: memory scales with the budget, not the
    // repo. Objects are deduped newest-first within the selection.
    let odb = crate::odb::Odb::open(repo.store, repo.name, &selected_ids).await?;
    let oids = odb.all_oids();

    // Copy in (source pack, offset) order so reads walk each source pack
    // sequentially through the block cache — O(bytes / block size) backend
    // requests instead of one per object.
    let mut sources: Vec<(String, EntryRecord)> = Vec::with_capacity(oids.len());
    for &oid in &oids {
        let (pack_id, rec) = odb.locate(oid).ok_or("object vanished during repack")?;
        sources.push((pack_id.to_string(), rec.clone()));
    }
    sources.sort_by(|a, b| (&a.0, a.1.data_start).cmp(&(&b.0, b.1.data_start)));

    let new_id = format!("m-{nonce}");
    let new_key = pack_key(repo.name, &new_id);
    let mut uploader = repo
        .store
        .start_upload(&new_key)
        .await
        .map_err(|e| e.to_string())?;

    let mut w = PackWriter::new(oids.len() as u32);
    let mut records: Vec<EntryRecord> = Vec::with_capacity(oids.len());
    for (pack_id, rec) in &sources {
        let (pack_id, rec) = (pack_id.clone(), rec.clone());
        let oid = rec.oid;
        let header_start = w.emitted();
        // Copy the payload in ≤1 MiB pieces so a huge object is never
        // resident (Workers isolate memory limit).
        let stored_type = match rec.base_oid {
            None => {
                w.begin_full_precompressed(rec.stored_type, rec.size);
                rec.stored_type
            }
            Some(base) => {
                w.begin_ref_delta_precompressed(base, rec.payload_size);
                TYPE_REF_DELTA
            }
        };
        let data_start = w.emitted();
        let total = rec.data_end - rec.data_start;
        let mut pos = 0u64;
        while pos < total {
            let piece = (total - pos).min(1024 * 1024);
            let bytes = odb
                .read_compressed_range(&pack_id, &rec, pos, piece)
                .await?;
            w.append_payload(&bytes);
            pos += piece;
            // Keep the writer's buffer bounded: stream out as we go.
            if w.buffered() >= 4 * 1024 * 1024 {
                let chunk = w.take_chunk();
                uploader.write(&chunk).await.map_err(|e| e.to_string())?;
            }
        }
        w.end_entry();
        let data_end = w.emitted();
        records.push(EntryRecord {
            oid,
            header_start,
            data_start,
            data_end,
            stored_type,
            final_type: rec.final_type,
            size: rec.size,
            payload_size: rec.payload_size,
            base_oid: rec.base_oid,
        });
        let chunk = w.take_chunk();
        uploader.write(&chunk).await.map_err(|e| e.to_string())?;
    }
    let (tail, _sum) = w.finish();
    uploader.write(&tail).await.map_err(|e| e.to_string())?;
    let total_bytes = uploader.complete().await.map_err(|e| e.to_string())?;

    repo.store
        .put(
            &index_key(repo.name, &new_id),
            PackIndex::new(records).to_bytes(),
        )
        .await
        .map_err(|e| e.to_string())?;

    // Merge the selected packs' file-log segments (loaded newest-first;
    // merged output must be oldest-first to preserve within-segment append
    // order), then write the result *sharded by path range* so read APIs can
    // load only the shard(s) covering their path (see
    // `write_sharded_filelog`). Segments outside the selection are left
    // untouched.
    let scoped = RepoState {
        filelog: selected_filelog.clone(),
        ..state.clone()
    };
    let mut merged = FileLogSegment::default();
    let segments = load_filelog(repo.store, repo.name, &scoped).await?;
    for seg in segments.into_iter().rev() {
        merged.records.extend(seg.records);
    }
    let has_filelog =
        write_sharded_filelog(repo.store, repo.name, &new_id, merged.records).await? > 0;

    let swap = RepackSwap {
        remove_packs: selected_ids.clone(),
        new_pack: Some(PackMeta {
            id: new_id.clone(),
            bytes: total_bytes,
            objects: oids.len() as u64,
        }),
        remove_filelog: selected_filelog.clone(),
        new_filelog: has_filelog.then(|| new_id.clone()),
        now_ms,
        sweep,
    };
    match repo.states.apply_repack(repo.name, &swap).await {
        Ok(true) => {
            // Swap landed. The consumed packs/segments are now `retired`,
            // not deleted: a request that loaded the pre-swap manifest may
            // still be reading them. A later run sweeps them after the
            // grace period.
            Ok(RepackOutcome::Repacked {
                packs: selected.len(),
                objects: oids.len(),
                remaining: state.packs.len() - selected.len(),
            })
        }
        Ok(false) => {
            // Another repack consumed one of our packs. Discard staged
            // output (never referenced, so immediate deletion is safe).
            let _ = repo.store.delete(&new_key).await;
            let _ = repo.store.delete(&index_key(repo.name, &new_id)).await;
            if has_filelog {
                let _ = delete_filelog(repo.store, repo.name, &new_id).await;
            }
            Ok(RepackOutcome::LostRace)
        }
        Err(e) => Err(e.to_string()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn state_with_packs(sizes: &[(u64, u64)]) -> RepoState {
        let mut s = RepoState::empty();
        for (i, (bytes, objects)) in sizes.iter().enumerate() {
            s.packs.push(PackMeta {
                id: format!("p{i}"),
                bytes: *bytes,
                objects: *objects,
            });
        }
        s
    }

    #[test]
    fn selects_everything_when_it_fits() {
        let s = state_with_packs(&[(100, 10), (100, 10), (100, 10)]);
        assert_eq!(select_packs(&s, &RepackBudget::default()), 0..3);
    }

    #[test]
    fn skips_oversized_base_and_takes_the_tail() {
        // A big base pack the budget can't fold: consolidate the small tail.
        let s = state_with_packs(&[(1 << 30, 10), (100, 10), (100, 10), (100, 10)]);
        let b = RepackBudget {
            max_bytes: 10_000,
            ..Default::default()
        };
        assert_eq!(select_packs(&s, &b), 1..4);
    }

    #[test]
    fn pack_count_budget_prefers_newest_window() {
        let s = state_with_packs(&[(1, 1); 10]);
        let b = RepackBudget {
            max_packs: 4,
            ..Default::default()
        };
        assert_eq!(select_packs(&s, &b), 6..10);
    }

    #[test]
    fn object_budget_bounds_selection() {
        let s = state_with_packs(&[(1, 100), (1, 100), (1, 100), (1, 100)]);
        let b = RepackBudget {
            max_objects: 250,
            ..Default::default()
        };
        assert_eq!(select_packs(&s, &b), 2..4);
    }
}

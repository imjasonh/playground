//! Scheduled maintenance: pack consolidation ("repack").
//!
//! Every push adds one pack, so a busy repo accumulates many small packs.
//! That's correct but degrades two things: each pack costs one index load
//! per request (Class B read), and object lookup fans out across indexes.
//! Repack rewrites all packs into one — **without inflating or recompressing
//! anything**:
//!
//! * full entries are copied verbatim (ranged read → multipart write);
//! * delta entries are copied verbatim too, with `OFS_DELTA` rewritten to
//!   `REF_DELTA` headers using the base oid recorded in the `GSIX` index
//!   (payload bytes untouched);
//! * duplicate oids (an object pushed twice) keep the newest copy;
//! * file-log segments are merged into one.
//!
//! CPU cost is therefore ~zero per byte (SHA-1 over the output is the only
//! per-byte work) and memory stays flat, which is what makes this viable in a
//! scheduled Worker. The swap is atomic: the new pack + merged file-log are
//! written first, then the state document flips in one CAS; old objects are
//! deleted only after the flip. A racing push simply makes the CAS fail and
//! the repack aborts cleanly (it retries on the next schedule).

use crate::odb::{index_key, pack_key};
use crate::pack::index::{EntryRecord, PackIndex};
use crate::pack::write::PackWriter;
use crate::pack::TYPE_REF_DELTA;
use crate::refs::{PackMeta, StateError};
use crate::repo::{delete_filelog, load_filelog, write_sharded_filelog, FileLogSegment, Repo};

/// What a repack run did.
#[derive(Debug, PartialEq, Eq)]
pub enum RepackOutcome {
    /// Nothing to do (0 or 1 pack).
    NoOp,
    /// Consolidated `packs` packs / `objects` objects into one.
    Repacked { packs: usize, objects: usize },
    /// A concurrent push won the CAS; all staged output was discarded.
    LostRace,
}

/// Consolidate all of a repo's packs into one. `nonce` provides the new
/// pack's unique storage id.
pub async fn repack(repo: &Repo<'_>, nonce: &str) -> Result<RepackOutcome, String> {
    let (state, version) = repo.load_state().await?;
    if state.packs.len() <= 1 && state.filelog.len() <= 1 {
        return Ok(RepackOutcome::NoOp);
    }
    let odb = repo.odb(&state).await?;
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
        let z = odb.read_compressed(&pack_id, &rec).await?;
        let header_start = w.emitted();
        let stored_type = match rec.base_oid {
            None => {
                w.add_full_precompressed(rec.stored_type, rec.size, &z);
                rec.stored_type
            }
            Some(base) => {
                w.add_ref_delta_precompressed(base, rec.payload_size, &z);
                TYPE_REF_DELTA
            }
        };
        let data_end = w.emitted();
        records.push(EntryRecord {
            oid,
            header_start,
            data_start: data_end - z.len() as u64,
            data_end,
            stored_type,
            final_type: rec.final_type,
            size: rec.size,
            payload_size: rec.payload_size,
            base_oid: rec.base_oid,
        });
        // Keep the writer's buffer bounded: stream out per entry.
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

    // Merge file-log segments (they're loaded newest-first; merged output
    // must be oldest-first to preserve within-segment append order), then
    // write the result *sharded by path range* so read APIs can load only
    // the shard(s) covering their path or directory instead of the whole
    // history (see `write_sharded_filelog`).
    let mut merged = FileLogSegment::default();
    let segments = load_filelog(repo.store, repo.name, &state).await?;
    for seg in segments.into_iter().rev() {
        merged.records.extend(seg.records);
    }
    let has_filelog =
        write_sharded_filelog(repo.store, repo.name, &new_id, merged.records).await? > 0;

    let mut next = state.clone();
    next.packs = vec![PackMeta {
        id: new_id.clone(),
        bytes: total_bytes,
        objects: oids.len() as u64,
    }];
    next.filelog = if has_filelog {
        vec![new_id.clone()]
    } else {
        Vec::new()
    };

    match repo.states.commit(repo.name, version, &next).await {
        Ok(_) => {
            // Flip succeeded: delete the superseded objects.
            for p in &state.packs {
                let _ = repo.store.delete(&pack_key(repo.name, &p.id)).await;
                let _ = repo.store.delete(&index_key(repo.name, &p.id)).await;
            }
            for f in &state.filelog {
                let _ = delete_filelog(repo.store, repo.name, f).await;
            }
            Ok(RepackOutcome::Repacked {
                packs: state.packs.len(),
                objects: oids.len(),
            })
        }
        Err(StateError::Conflict) => {
            // A push landed mid-repack. Discard our staged output.
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

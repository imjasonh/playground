//! Repository orchestration: push ingestion, fetch object selection, and the
//! push-time file-log index.
//!
//! The push pipeline (all before report-status is returned, so every derived
//! view is consistent the moment the client sees "ok"):
//!
//! 1. stream the raw pack into R2 (multipart) while scanning it;
//! 2. resolve deltas with ranged reads and write the `GSIX` index;
//! 3. verify ref-target connectivity (cheap: targets + tree roots exist);
//! 4. build the file-log segment for the new commits (first-parent tree
//!    diffs), giving the read APIs their "which commit last touched this
//!    path" chain without history walks;
//! 5. CAS the repo state document: refs, pack manifest, file-log manifest
//!    flip together, atomically.

use crate::object::{ObjType, Oid, TreeEntry};
use crate::odb::{index_key, pack_key, Odb};
use crate::pack::index::{resolve_pack, ExternalBases, PackIndex};
use crate::pack::scan::ScannedPack;
use crate::pack::{EntryRecord, PackScanner};
use crate::refs::{PackMeta, RepoState, StateError, StateStore};
use crate::storage::{Store, Uploader};
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, HashMap, HashSet, VecDeque};
use std::rc::Rc;

/// Handle for one repository: byte store + state store + name.
pub struct Repo<'a> {
    pub store: &'a dyn Store,
    pub states: &'a dyn StateStore,
    pub name: &'a str,
}

// ---------------------------------------------------------------------------
// File-log index
// ---------------------------------------------------------------------------

/// How a commit changed a path.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum Change {
    Add,
    Modify,
    Delete,
}

/// One file-log record: commit C touched `path`.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FileLogRecord {
    pub path: String,
    /// Hex commit oid.
    pub commit: String,
    /// Commit time (epoch seconds) for ordering/display.
    pub time: i64,
    pub change: Change,
    /// Blob oid after the change (empty for deletes).
    pub blob: String,
    /// The previous (commit, blob) that touched this path, forming a chain
    /// the blame engine hops without walking history. Computed at push time
    /// along the first-parent line.
    pub prev_commit: Option<String>,
    pub prev_blob: Option<String>,
}

/// A file-log segment: the records produced by one push (or one maintenance
/// merge). Stored at `<repo>/filelog/<segment-id>` in the binary `GSFL`
/// format below (a compact record stream — parsing it is ~10× faster than
/// JSON and it's less than half the size, which matters because read APIs
/// load segments per request).
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct FileLogSegment {
    pub records: Vec<FileLogRecord>,
}

const GSFL_MAGIC: &[u8; 4] = b"GSFL";
const GSFL_VERSION: u32 = 1;

impl FileLogSegment {
    /// Serialize: header, then per record `path_len(u16) path commit(20)
    /// time(i64) change(u8) blob(20) prev_commit(20) prev_blob(20)` with
    /// zero-oids encoding "absent".
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(16 + self.records.len() * 128);
        out.extend_from_slice(GSFL_MAGIC);
        out.extend_from_slice(&GSFL_VERSION.to_be_bytes());
        out.extend_from_slice(&(self.records.len() as u32).to_be_bytes());
        let oid_or_zero = |s: &Option<String>| -> [u8; 20] {
            s.as_deref().and_then(Oid::from_hex).unwrap_or(Oid::ZERO).0
        };
        for r in &self.records {
            let path = r.path.as_bytes();
            out.extend_from_slice(&(path.len() as u16).to_be_bytes());
            out.extend_from_slice(path);
            out.extend_from_slice(&Oid::from_hex(&r.commit).unwrap_or(Oid::ZERO).0);
            out.extend_from_slice(&r.time.to_be_bytes());
            out.push(match r.change {
                Change::Add => 0,
                Change::Modify => 1,
                Change::Delete => 2,
            });
            out.extend_from_slice(&Oid::from_hex(&r.blob).unwrap_or(Oid::ZERO).0);
            out.extend_from_slice(&oid_or_zero(&r.prev_commit));
            out.extend_from_slice(&oid_or_zero(&r.prev_blob));
        }
        out
    }

    pub fn from_bytes(data: &[u8]) -> Result<FileLogSegment, String> {
        if data.len() < 12 || &data[..4] != GSFL_MAGIC {
            return Err("bad GSFL magic".into());
        }
        let version = u32::from_be_bytes(data[4..8].try_into().unwrap());
        if version != GSFL_VERSION {
            return Err(format!("unsupported GSFL version {version}"));
        }
        let count = u32::from_be_bytes(data[8..12].try_into().unwrap()) as usize;
        let mut records = Vec::with_capacity(count);
        let mut p = 12usize;
        let take = |p: &mut usize, n: usize| -> Result<&[u8], String> {
            let s = data.get(*p..*p + n).ok_or("GSFL truncated")?;
            *p += n;
            Ok(s)
        };
        for _ in 0..count {
            let path_len = u16::from_be_bytes(take(&mut p, 2)?.try_into().unwrap()) as usize;
            let path = String::from_utf8_lossy(take(&mut p, path_len)?).into_owned();
            let commit = Oid::from_bytes(take(&mut p, 20)?).unwrap();
            let time = i64::from_be_bytes(take(&mut p, 8)?.try_into().unwrap());
            let change = match take(&mut p, 1)?[0] {
                0 => Change::Add,
                1 => Change::Modify,
                2 => Change::Delete,
                other => return Err(format!("bad GSFL change {other}")),
            };
            let blob = Oid::from_bytes(take(&mut p, 20)?).unwrap();
            let prev_commit = Oid::from_bytes(take(&mut p, 20)?).unwrap();
            let prev_blob = Oid::from_bytes(take(&mut p, 20)?).unwrap();
            let opt = |o: Oid| (!o.is_zero()).then(|| o.to_hex());
            records.push(FileLogRecord {
                path,
                commit: commit.to_hex(),
                time,
                change,
                blob: if blob.is_zero() {
                    String::new()
                } else {
                    blob.to_hex()
                },
                prev_commit: opt(prev_commit),
                prev_blob: opt(prev_blob),
            });
        }
        if p != data.len() {
            return Err("GSFL trailing bytes".into());
        }
        Ok(FileLogSegment { records })
    }
}

pub fn filelog_key(repo: &str, seg_id: &str) -> String {
    format!("{repo}/filelog/{seg_id}")
}

// ---------------------------------------------------------------------------
// Sharded file-log (path-range shards + GSFI index)
// ---------------------------------------------------------------------------

/// Target shard size. Small enough that a scoped query parses ~1 shard in a
/// fraction of a millisecond; large enough that shard count (and thus Class B
/// reads for whole-log loads) stays low.
pub const FILELOG_SHARD_TARGET_BYTES: usize = 256 * 1024;

const GSFI_MAGIC: &[u8; 4] = b"GSFI";
const GSFI_VERSION: u32 = 1;

/// One shard's entry in a `GSFI` index: records for paths in
/// `[min_path, max_path]` live in `<segment-id>.<k>`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ShardInfo {
    pub min_path: String,
    pub max_path: String,
    pub records: u32,
}

/// Serialize a shard index.
fn shard_index_to_bytes(shards: &[ShardInfo]) -> Vec<u8> {
    let mut out = Vec::new();
    out.extend_from_slice(GSFI_MAGIC);
    out.extend_from_slice(&GSFI_VERSION.to_be_bytes());
    out.extend_from_slice(&(shards.len() as u32).to_be_bytes());
    for s in shards {
        out.extend_from_slice(&(s.min_path.len() as u16).to_be_bytes());
        out.extend_from_slice(s.min_path.as_bytes());
        out.extend_from_slice(&(s.max_path.len() as u16).to_be_bytes());
        out.extend_from_slice(s.max_path.as_bytes());
        out.extend_from_slice(&s.records.to_be_bytes());
    }
    out
}

fn shard_index_from_bytes(data: &[u8]) -> Result<Vec<ShardInfo>, String> {
    if data.len() < 12 || &data[..4] != GSFI_MAGIC {
        return Err("bad GSFI magic".into());
    }
    let version = u32::from_be_bytes(data[4..8].try_into().unwrap());
    if version != GSFI_VERSION {
        return Err(format!("unsupported GSFI version {version}"));
    }
    let count = u32::from_be_bytes(data[8..12].try_into().unwrap()) as usize;
    let mut p = 12usize;
    let take = |p: &mut usize, n: usize| -> Result<&[u8], String> {
        let s = data.get(*p..*p + n).ok_or("GSFI truncated")?;
        *p += n;
        Ok(s)
    };
    let mut shards = Vec::with_capacity(count);
    for _ in 0..count {
        let min_len = u16::from_be_bytes(take(&mut p, 2)?.try_into().unwrap()) as usize;
        let min_path = String::from_utf8_lossy(take(&mut p, min_len)?).into_owned();
        let max_len = u16::from_be_bytes(take(&mut p, 2)?.try_into().unwrap()) as usize;
        let max_path = String::from_utf8_lossy(take(&mut p, max_len)?).into_owned();
        let records = u32::from_be_bytes(take(&mut p, 4)?.try_into().unwrap());
        shards.push(ShardInfo {
            min_path,
            max_path,
            records,
        });
    }
    Ok(shards)
}

fn shard_key(repo: &str, seg_id: &str, k: usize) -> String {
    format!("{repo}/filelog/{seg_id}.{k}")
}

/// Write `records` as a sharded file-log segment: records are stably sorted
/// by path (preserving per-path chronological order), split at path
/// boundaries into ~[`FILELOG_SHARD_TARGET_BYTES`] shards, and described by a
/// `GSFI` index at the segment's own key. A path's records are never split
/// across shards, so any single-path query touches exactly one shard.
///
/// Returns the number of shards written (0 if `records` was empty).
pub async fn write_sharded_filelog(
    store: &dyn Store,
    repo: &str,
    seg_id: &str,
    mut records: Vec<FileLogRecord>,
) -> Result<usize, String> {
    if records.is_empty() {
        return Ok(0);
    }
    records.sort_by(|a, b| a.path.cmp(&b.path)); // stable: keeps time order per path

    let mut shards: Vec<ShardInfo> = Vec::new();
    let mut current: Vec<FileLogRecord> = Vec::new();
    let mut current_bytes = 0usize;

    async fn flush(
        store: &dyn Store,
        repo: &str,
        seg_id: &str,
        shards: &mut Vec<ShardInfo>,
        current: &mut Vec<FileLogRecord>,
    ) -> Result<(), String> {
        if current.is_empty() {
            return Ok(());
        }
        let info = ShardInfo {
            min_path: current.first().unwrap().path.clone(),
            max_path: current.last().unwrap().path.clone(),
            records: current.len() as u32,
        };
        let seg = FileLogSegment {
            records: std::mem::take(current),
        };
        store
            .put(&shard_key(repo, seg_id, shards.len()), seg.to_bytes())
            .await
            .map_err(|e| e.to_string())?;
        shards.push(info);
        Ok(())
    }

    let mut records = records.into_iter().peekable();
    while let Some(r) = records.next() {
        current_bytes += 91 + r.path.len(); // fixed record size + path
        let path_changes = records
            .peek()
            .map(|next| next.path != r.path)
            .unwrap_or(true);
        current.push(r);
        if current_bytes >= FILELOG_SHARD_TARGET_BYTES && path_changes {
            flush(store, repo, seg_id, &mut shards, &mut current).await?;
            current_bytes = 0;
        }
    }
    flush(store, repo, seg_id, &mut shards, &mut current).await?;

    store
        .put(&filelog_key(repo, seg_id), shard_index_to_bytes(&shards))
        .await
        .map_err(|e| e.to_string())?;
    Ok(shards.len())
}

/// Delete a file-log segment, whether plain or sharded.
pub async fn delete_filelog(store: &dyn Store, repo: &str, seg_id: &str) -> Result<(), String> {
    let key = filelog_key(repo, seg_id);
    if let Some(bytes) = store.get(&key).await.map_err(|e| e.to_string())? {
        if bytes.len() >= 4 && &bytes[..4] == GSFI_MAGIC {
            if let Ok(shards) = shard_index_from_bytes(&bytes) {
                for k in 0..shards.len() {
                    let _ = store.delete(&shard_key(repo, seg_id, k)).await;
                }
            }
        }
    }
    store.delete(&key).await.map_err(|e| e.to_string())
}

/// What part of the file-log a request needs. Scoped loads read only the
/// shards whose path range intersects the scope — the difference between
/// parsing a whole repo's history and parsing ~one shard.
pub enum FilelogScope<'a> {
    /// Everything (push prev-pointer indexing over arbitrary paths).
    All,
    /// One exact path (blame).
    Path(&'a str),
    /// All paths under a prefix (directory listings; `""` = whole tree).
    Prefix(&'a str),
    /// A specific set of paths (push prev-pointers when changes are known).
    Paths(&'a std::collections::HashSet<String>),
}

impl FilelogScope<'_> {
    /// Does a shard covering `[min, max]` possibly contain scoped records?
    fn intersects(&self, min: &str, max: &str) -> bool {
        match self {
            FilelogScope::All => true,
            FilelogScope::Path(p) => *p >= min && *p <= max,
            FilelogScope::Prefix(pre) => {
                // Paths with this prefix form the range [pre, successor(pre)).
                // A shard whose min is above the prefix without *carrying* it
                // is entirely past that range (first differing byte is
                // larger); a shard whose max is below `pre` is entirely
                // before it. Everything else may contain prefixed paths.
                max >= *pre && (min.starts_with(*pre) || *pre >= min)
            }
            FilelogScope::Paths(set) => set.iter().any(|p| p.as_str() >= min && p.as_str() <= max),
        }
    }
}

/// Load the file-log segments a request needs, newest first. Plain (per-push)
/// segments are always loaded whole — they are small and recent. Sharded
/// (maintenance-merged) segments contribute only the shards intersecting
/// `scope`, fetched **concurrently** (shards are independent R2 objects, so a
/// wide query pays ~one round trip of latency, not shard-count round trips).
pub async fn load_filelog_scoped(
    store: &dyn Store,
    repo: &str,
    state: &RepoState,
    scope: &FilelogScope<'_>,
) -> Result<Vec<FileLogSegment>, String> {
    let _t = crate::timing::Phase::start("filelog: load+parse");
    let mut segs = Vec::new();
    for id in state.filelog.iter().rev() {
        let bytes = store
            .get(&filelog_key(repo, id))
            .await
            .map_err(|e| e.to_string())?
            .ok_or_else(|| format!("missing filelog segment {id}"))?;
        if bytes.len() >= 4 && &bytes[..4] == GSFI_MAGIC {
            let shards = shard_index_from_bytes(&bytes)?;
            let fetches = shards
                .iter()
                .enumerate()
                .filter(|(_, info)| scope.intersects(&info.min_path, &info.max_path))
                .map(|(k, _)| {
                    let key = shard_key(repo, id, k);
                    async move {
                        store
                            .get(&key)
                            .await
                            .map_err(|e| e.to_string())?
                            .ok_or_else(|| format!("missing filelog shard {key}"))
                    }
                });
            for shard_bytes in futures::future::try_join_all(fetches).await? {
                segs.push(FileLogSegment::from_bytes(&shard_bytes)?);
            }
        } else {
            segs.push(FileLogSegment::from_bytes(&bytes)?);
        }
    }
    Ok(segs)
}

/// Load all of a repo's file-log segments, newest first.
pub async fn load_filelog(
    store: &dyn Store,
    repo: &str,
    state: &RepoState,
) -> Result<Vec<FileLogSegment>, String> {
    load_filelog_scoped(store, repo, state, &FilelogScope::All).await
}

/// Find the newest record for `path` across segments (newest first).
/// One-shot linear scan; request handlers that do many lookups should build a
/// [`FileLogView`] instead.
pub fn latest_for_path<'a>(
    segments: &'a [FileLogSegment],
    path: &str,
) -> Option<&'a FileLogRecord> {
    for seg in segments {
        // Within a segment records are appended oldest→newest; scan backward.
        if let Some(r) = seg.records.iter().rev().find(|r| r.path == path) {
            return Some(r);
        }
    }
    None
}

/// All records for one path, newest first (blame's version chain source).
/// Single pass over the segments, however many versions the chain has.
pub fn records_for_path<'a>(segments: &'a [FileLogSegment], path: &str) -> Vec<&'a FileLogRecord> {
    let mut out = Vec::new();
    for seg in segments {
        for r in seg.records.iter().rev() {
            if r.path == path {
                out.push(r);
            }
        }
    }
    out
}

/// A per-request lookup index over the file-log: newest record per path,
/// built in one pass so N lookups cost N·log(paths) instead of N full scans.
pub struct FileLogView<'a> {
    /// path → newest record. Ordered so prefix queries are range scans.
    newest: BTreeMap<&'a str, &'a FileLogRecord>,
}

impl<'a> FileLogView<'a> {
    /// `segments` newest-first (as [`load_filelog`] returns them).
    pub fn new(segments: &'a [FileLogSegment]) -> Self {
        let mut newest: BTreeMap<&str, &FileLogRecord> = BTreeMap::new();
        // Oldest→newest so later (newer) records overwrite earlier ones.
        for seg in segments.iter().rev() {
            for r in &seg.records {
                newest.insert(r.path.as_str(), r);
            }
        }
        FileLogView { newest }
    }

    /// The newest record that touched `path`.
    pub fn latest_for_path(&self, path: &str) -> Option<&'a FileLogRecord> {
        self.newest.get(path).copied()
    }

    /// The newest record under `prefix` (for directory "last commit" views).
    pub fn latest_for_prefix(&self, prefix: &str) -> Option<&'a FileLogRecord> {
        self.newest
            .range(prefix..)
            .take_while(|(k, _)| k.starts_with(prefix))
            .map(|(_, r)| *r)
            .max_by_key(|r| r.time)
    }
}

// ---------------------------------------------------------------------------
// Push ingestion
// ---------------------------------------------------------------------------

/// Streaming pack ingest: uploads raw pack bytes to R2 while scanning them.
pub struct PackIngest {
    uploader: Box<dyn Uploader>,
    scanner: PackScanner,
    pack_id: String,
}

impl PackIngest {
    /// `nonce` must be unique per push (the caller provides randomness since
    /// this crate stays runtime-agnostic).
    pub async fn start(repo: &Repo<'_>, nonce: &str) -> Result<PackIngest, String> {
        let pack_id = format!("p-{nonce}");
        let uploader = repo
            .store
            .start_upload(&pack_key(repo.name, &pack_id))
            .await
            .map_err(|e| e.to_string())?;
        Ok(PackIngest {
            uploader,
            scanner: PackScanner::new(),
            pack_id,
        })
    }

    pub async fn feed(&mut self, chunk: &[u8]) -> Result<(), String> {
        self.uploader
            .write(chunk)
            .await
            .map_err(|e| e.to_string())?;
        self.scanner.feed(chunk)
    }

    /// Complete the upload and scan. Returns (pack id, scan result).
    pub async fn finish(self) -> Result<(String, ScannedPack), String> {
        let scanned = self.scanner.finish()?;
        self.uploader.complete().await.map_err(|e| e.to_string())?;
        Ok((self.pack_id, scanned))
    }

    /// Abort (push rejected mid-stream).
    pub async fn abort(self) -> Result<(), String> {
        self.uploader.abort().await.map_err(|e| e.to_string())
    }
}

/// An [`ExternalBases`] over an existing odb snapshot, for thin-pack pushes.
pub struct OdbBases<'a>(pub &'a Odb<'a>);

#[async_trait::async_trait(?Send)]
impl ExternalBases for OdbBases<'_> {
    async fn get_object(&self, oid: Oid) -> Result<Option<(ObjType, Rc<Vec<u8>>)>, String> {
        self.0.read(oid).await
    }
}

/// One ref update command from a push.
#[derive(Debug, Clone)]
pub struct RefUpdate {
    pub name: String,
    pub old: Oid,
    pub new: Oid,
}

/// Per-ref result for report-status.
#[derive(Debug, Clone)]
pub struct RefResult {
    pub name: String,
    /// `None` = ok; `Some(reason)` = rejected.
    pub error: Option<String>,
}

/// Outcome of a completed push.
pub struct PushOutcome {
    pub results: Vec<RefResult>,
    /// True if the state document was updated.
    pub applied: bool,
}

impl<'a> Repo<'a> {
    pub async fn load_state(&self) -> Result<(RepoState, u64), String> {
        self.states.load(self.name).await.map_err(|e| e.to_string())
    }

    /// Open an odb over the given state's packs.
    pub async fn odb(&self, state: &RepoState) -> Result<Odb<'a>, String> {
        Odb::open(self.store, self.name, &state.pack_ids()).await
    }

    /// Complete a push: the pack (if any) has been streamed via
    /// [`PackIngest`]; resolve it, index it, build the file-log segment,
    /// verify, and CAS the state.
    pub async fn apply_push(
        &self,
        commands: Vec<RefUpdate>,
        ingested: Option<(String, ScannedPack)>,
        state: RepoState,
        version: u64,
    ) -> Result<PushOutcome, String> {
        let old_odb = self.odb(&state).await?;

        // Resolve + index the new pack (if the push carried one).
        let new_pack: Option<(PackMeta, PackIndex)> = match &ingested {
            Some((pack_id, scanned)) => {
                let _t = crate::timing::Phase::start("push: resolve+index");
                let key = pack_key(self.name, pack_id);
                let records = resolve_pack(self.store, &key, scanned, &OdbBases(&old_odb)).await?;
                let index = PackIndex::new(records);
                self.store
                    .put(&index_key(self.name, pack_id), index.to_bytes())
                    .await
                    .map_err(|e| e.to_string())?;
                let meta = PackMeta {
                    id: pack_id.clone(),
                    bytes: scanned.total_len,
                    objects: scanned.entries.len() as u64,
                };
                Some((meta, index))
            }
            None => None,
        };

        // Odb view including the new pack, for validation + index building.
        let mut pack_ids = state.pack_ids();
        if let Some((meta, _)) = &new_pack {
            pack_ids.push(meta.id.clone());
        }
        let odb = Odb::open(self.store, self.name, &pack_ids).await?;

        // Validate each command against the current state.
        let mut results = Vec::new();
        let mut next = state.clone();
        let mut any_ok = false;
        for cmd in &commands {
            let current = next
                .refs
                .get(&cmd.name)
                .and_then(|h| Oid::from_hex(h))
                .unwrap_or(Oid::ZERO);
            if current != cmd.old {
                results.push(RefResult {
                    name: cmd.name.clone(),
                    error: Some("fetch first".into()),
                });
                continue;
            }
            if cmd.new.is_zero() {
                next.refs.remove(&cmd.name);
                results.push(RefResult {
                    name: cmd.name.clone(),
                    error: None,
                });
                any_ok = true;
                continue;
            }
            // Connectivity (cheap tier): the target must exist, and if it is
            // a commit its root tree must too. Full connectivity is enforced
            // by construction for honest clients (the pack was verified
            // self-contained or thin against our own bases).
            match odb.read(cmd.new).await? {
                None => {
                    results.push(RefResult {
                        name: cmd.name.clone(),
                        error: Some("missing necessary objects".into()),
                    });
                    continue;
                }
                Some((ObjType::Commit, data)) => {
                    let commit = crate::object::parse_commit(&data)?;
                    if odb.read(commit.tree).await?.is_none() {
                        results.push(RefResult {
                            name: cmd.name.clone(),
                            error: Some("missing necessary objects".into()),
                        });
                        continue;
                    }
                }
                Some(_) => {}
            }
            next.refs.insert(cmd.name.clone(), cmd.new.to_hex());
            results.push(RefResult {
                name: cmd.name.clone(),
                error: None,
            });
            any_ok = true;
        }

        if !any_ok {
            return Ok(PushOutcome {
                results,
                applied: false,
            });
        }

        // Keep HEAD pointing at a branch that exists: if its target is gone
        // (or was never created), fall back to `main`, then the first branch.
        if !next.refs.contains_key(&next.head) {
            if next.refs.contains_key("refs/heads/main") {
                next.head = "refs/heads/main".to_string();
            } else if let Some(first) = next.refs.keys().find(|r| r.starts_with("refs/heads/")) {
                next.head = first.clone();
            }
        }

        // Build the file-log segment for the new commits. Typical pushes
        // write one small plain segment; a huge push (e.g. an initial
        // import) is sharded immediately so the read APIs are fast right
        // away rather than only after the next maintenance merge.
        if let Some((meta, index)) = &new_pack {
            let _t = crate::timing::Phase::start("push: filelog build");
            let segment = self
                .build_filelog_segment(&odb, &old_odb, index, &state)
                .await?;
            if !segment.records.is_empty() {
                let bytes = segment.to_bytes();
                if bytes.len() > 2 * FILELOG_SHARD_TARGET_BYTES {
                    write_sharded_filelog(self.store, self.name, &meta.id, segment.records).await?;
                } else {
                    self.store
                        .put(&filelog_key(self.name, &meta.id), bytes)
                        .await
                        .map_err(|e| e.to_string())?;
                }
                next.filelog.push(meta.id.clone());
            }
            next.packs.push(meta.clone());
        }

        match self.states.commit(self.name, version, &next).await {
            Ok(_) => Ok(PushOutcome {
                results,
                applied: true,
            }),
            Err(StateError::Conflict) => {
                // Racing push won. Fail all commands; client retries.
                let results = commands
                    .iter()
                    .map(|c| RefResult {
                        name: c.name.clone(),
                        error: Some("concurrent update, retry".into()),
                    })
                    .collect();
                Ok(PushOutcome {
                    results,
                    applied: false,
                })
            }
            Err(e) => Err(e.to_string()),
        }
    }

    /// Diff each new commit against its first parent, producing file-log
    /// records with prev-pointers.
    async fn build_filelog_segment(
        &self,
        odb: &Odb<'_>,
        old_odb: &Odb<'_>,
        new_index: &PackIndex,
        state: &RepoState,
    ) -> Result<FileLogSegment, String> {
        // New commits: commit-typed entries of this pack not already stored.
        let mut new_commits: Vec<Oid> = Vec::new();
        for rec in &new_index.records {
            if rec.final_type == ObjType::Commit && !old_odb.contains(rec.oid) {
                new_commits.push(rec.oid);
            }
        }
        if new_commits.is_empty() {
            return Ok(FileLogSegment::default());
        }

        // Topologically order (parents before children) within the new set.
        let set: HashSet<Oid> = new_commits.iter().copied().collect();
        let mut parsed: HashMap<Oid, crate::object::Commit> = HashMap::new();
        for &c in &new_commits {
            parsed.insert(c, odb.read_commit(c).await?);
        }
        let mut indegree: HashMap<Oid, usize> = HashMap::new();
        let mut children: HashMap<Oid, Vec<Oid>> = HashMap::new();
        for (&c, commit) in &parsed {
            let mut deg = 0;
            for p in &commit.parents {
                if set.contains(p) {
                    deg += 1;
                    children.entry(*p).or_default().push(c);
                }
            }
            indegree.insert(c, deg);
        }
        let mut queue: VecDeque<Oid> = indegree
            .iter()
            .filter(|(_, &d)| d == 0)
            .map(|(&c, _)| c)
            .collect();
        let mut ordered = Vec::with_capacity(new_commits.len());
        while let Some(c) = queue.pop_front() {
            ordered.push(c);
            for &child in children.get(&c).map(|v| v.as_slice()).unwrap_or(&[]) {
                let d = indegree.get_mut(&child).unwrap();
                *d -= 1;
                if *d == 0 {
                    queue.push_back(child);
                }
            }
        }

        // Pass 1: diff every new commit, collecting records without their
        // prev-pointers (so we know the full changed-path set up front).
        let mut segment = FileLogSegment::default();
        for c in ordered {
            let commit = &parsed[&c];
            let parent_tree = match commit.parents.first() {
                Some(p) => Some(odb.read_commit(*p).await?.tree),
                None => None,
            };
            let mut changes = Vec::new();
            diff_trees(odb, parent_tree, Some(commit.tree), "", &mut changes).await?;
            for (path, change, blob) in changes {
                segment.records.push(FileLogRecord {
                    path,
                    commit: c.to_hex(),
                    time: commit.commit_time,
                    change,
                    blob: blob.map(|b| b.to_hex()).unwrap_or_default(),
                    prev_commit: None,
                    prev_blob: None,
                });
            }
        }

        // Pass 2: fill in prev-pointers. The existing file-log is loaded
        // *scoped to the changed paths*, so a push touching a handful of
        // files reads a handful of shards, not the whole history.
        let changed: HashSet<String> = segment.records.iter().map(|r| r.path.clone()).collect();
        let existing =
            load_filelog_scoped(self.store, self.name, state, &FilelogScope::Paths(&changed))
                .await?;
        let existing_view = FileLogView::new(&existing);
        let mut in_push_latest: HashMap<String, (String, String)> = HashMap::new(); // path → (commit, blob)
        for r in &mut segment.records {
            let (prev_commit, prev_blob) = match in_push_latest.get(&r.path) {
                Some((pc, pb)) => (Some(pc.clone()), Some(pb.clone())),
                None => match existing_view.latest_for_path(&r.path) {
                    Some(prev) => (Some(prev.commit.clone()), Some(prev.blob.clone())),
                    None => (None, None),
                },
            };
            r.prev_commit = prev_commit;
            r.prev_blob = prev_blob;
            in_push_latest.insert(r.path.clone(), (r.commit.clone(), r.blob.clone()));
        }
        Ok(segment)
    }
}

/// Recursive tree diff, emitting `(path, change, new-blob)` tuples for blob
/// entries. `old`/`new` are tree oids (None = absent side).
///
/// Tree objects store entries in git's canonical sort order, so both sides
/// are walked with a two-pointer merge — no maps, no re-sorting. Unchanged
/// subtrees (equal oids) are skipped without being read, which is what keeps
/// a push's file-log cost proportional to its *changes*, not tree size.
async fn diff_trees(
    odb: &Odb<'_>,
    old: Option<Oid>,
    new: Option<Oid>,
    prefix: &str,
    out: &mut Vec<(String, Change, Option<Oid>)>,
) -> Result<(), String> {
    if old == new {
        return Ok(());
    }
    let old_entries = match old {
        Some(t) => odb.read_tree(t).await?,
        None => std::rc::Rc::new(Vec::new()),
    };
    let new_entries = match new {
        Some(t) => odb.read_tree(t).await?,
        None => std::rc::Rc::new(Vec::new()),
    };

    let join = |name: &str| {
        if prefix.is_empty() {
            name.to_string()
        } else {
            format!("{prefix}/{name}")
        }
    };

    // git sorts tree entries by name with directories compared as "name/";
    // emulate that key so the merge walk pairs entries correctly even when a
    // path flips between file and directory.
    let sort_key = |e: &TreeEntry| -> Vec<u8> {
        let mut k = e.name.as_bytes().to_vec();
        if e.is_tree() {
            k.push(b'/');
        }
        k
    };

    let (mut i, mut j) = (0usize, 0usize);
    while i < old_entries.len() || j < new_entries.len() {
        let take = match (old_entries.get(i), new_entries.get(j)) {
            (Some(oe), Some(ne)) => sort_key(oe).cmp(&sort_key(ne)),
            (Some(_), None) => std::cmp::Ordering::Less,
            (None, Some(_)) => std::cmp::Ordering::Greater,
            (None, None) => unreachable!(),
        };
        match take {
            std::cmp::Ordering::Equal => {
                let (oe, ne) = (&old_entries[i], &new_entries[j]);
                i += 1;
                j += 1;
                if oe.oid == ne.oid && oe.mode == ne.mode {
                    continue;
                }
                let path = join(&ne.name);
                match (oe.is_tree(), ne.is_tree()) {
                    (true, true) => {
                        Box::pin(diff_trees(odb, Some(oe.oid), Some(ne.oid), &path, out)).await?
                    }
                    (true, false) => {
                        Box::pin(diff_trees(odb, Some(oe.oid), None, &path, out)).await?;
                        out.push((path, Change::Add, Some(ne.oid)));
                    }
                    (false, true) => {
                        out.push((path.clone(), Change::Delete, None));
                        Box::pin(diff_trees(odb, None, Some(ne.oid), &path, out)).await?;
                    }
                    (false, false) => out.push((path, Change::Modify, Some(ne.oid))),
                }
            }
            std::cmp::Ordering::Less => {
                let oe = &old_entries[i];
                i += 1;
                let path = join(&oe.name);
                if oe.is_tree() {
                    Box::pin(diff_trees(odb, Some(oe.oid), None, &path, out)).await?;
                } else {
                    out.push((path, Change::Delete, None));
                }
            }
            std::cmp::Ordering::Greater => {
                let ne = &new_entries[j];
                j += 1;
                let path = join(&ne.name);
                if ne.is_tree() {
                    Box::pin(diff_trees(odb, None, Some(ne.oid), &path, out)).await?;
                } else {
                    out.push((path, Change::Add, Some(ne.oid)));
                }
            }
        }
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Fetch object selection
// ---------------------------------------------------------------------------

/// Objects to send for a fetch, plus the set the client already has (thin
/// bases).
pub struct FetchSet {
    /// Oids to include in the pack, commits first.
    pub include: Vec<Oid>,
    /// Common commits acknowledged during negotiation.
    pub common: Vec<Oid>,
    /// Objects known to exist on the client (usable as thin-pack bases).
    pub client_has: HashSet<Oid>,
}

/// Compute the object set for a fetch: everything reachable from `wants`
/// minus everything reachable from `haves`.
pub async fn collect_fetch_set(
    odb: &Odb<'_>,
    wants: &[Oid],
    haves: &[Oid],
) -> Result<FetchSet, String> {
    // Ancestors of haves (bounded: stop exploring once a commit is known).
    let mut have_commits: HashSet<Oid> = HashSet::new();
    let mut common = Vec::new();
    let mut queue: VecDeque<Oid> = VecDeque::new();
    for &h in haves {
        if odb.contains(h) {
            common.push(h);
            queue.push_back(h);
        }
    }
    while let Some(c) = queue.pop_front() {
        if !have_commits.insert(c) {
            continue;
        }
        if let Ok(commit) = odb.read_commit(c).await {
            for p in commit.parents {
                queue.push_back(p);
            }
        }
    }

    // Commits to send: BFS from wants, stopping at have_commits.
    let mut include_commits: Vec<Oid> = Vec::new();
    let mut seen: HashSet<Oid> = HashSet::new();
    let mut boundary: HashSet<Oid> = HashSet::new();
    let mut tags: Vec<Oid> = Vec::new();
    let mut queue: VecDeque<Oid> = VecDeque::new();
    for &w in wants {
        let (ty, _) = odb
            .read(w)
            .await?
            .ok_or_else(|| format!("want {w} not found"))?;
        match ty {
            ObjType::Tag => {
                tags.push(w);
                let peeled = odb.peel_to_commit(w).await?;
                queue.push_back(peeled);
            }
            ObjType::Commit => queue.push_back(w),
            _ => {
                // Direct tree/blob want (unusual); include as-is.
                include_commits.push(w);
            }
        }
    }
    while let Some(c) = queue.pop_front() {
        if have_commits.contains(&c) {
            boundary.insert(c);
            continue;
        }
        if !seen.insert(c) {
            continue;
        }
        include_commits.push(c);
        let commit = odb.read_commit(c).await?;
        for p in commit.parents {
            queue.push_back(p);
        }
    }

    // Objects the client demonstrably has: full tree closure of boundary
    // commits (their trees/blobs are all reachable from the client's haves).
    let mut client_has: HashSet<Oid> = HashSet::new();
    for &b in &boundary {
        client_has.insert(b);
        if let Ok(commit) = odb.read_commit(b).await {
            collect_tree_closure(odb, commit.tree, &mut client_has).await?;
        }
    }
    for &h in &have_commits {
        client_has.insert(h);
    }

    // Trees/blobs of included commits, minus what the client has.
    let mut include: Vec<Oid> = tags;
    let mut included: HashSet<Oid> = include.iter().copied().collect();
    for &c in &include_commits {
        if included.insert(c) {
            include.push(c);
        }
    }
    for &c in &include_commits {
        // Direct tree/blob wants land here too; read() dispatches on type.
        let (ty, data) = odb.read(c).await?.ok_or("included object vanished")?;
        if ty != ObjType::Commit {
            continue;
        }
        let commit = crate::object::parse_commit(&data)?;
        collect_new_tree_objects(odb, commit.tree, &client_has, &mut included, &mut include)
            .await?;
    }

    Ok(FetchSet {
        include,
        common,
        client_has,
    })
}

/// Add every object in `tree`'s closure to `out`.
async fn collect_tree_closure(
    odb: &Odb<'_>,
    tree: Oid,
    out: &mut HashSet<Oid>,
) -> Result<(), String> {
    if !out.insert(tree) {
        return Ok(());
    }
    let entries = odb.read_tree(tree).await?;
    for e in entries.iter() {
        if e.is_tree() {
            Box::pin(collect_tree_closure(odb, e.oid, out)).await?;
        } else {
            out.insert(e.oid);
        }
    }
    Ok(())
}

/// Add tree-closure objects not already in `skip`/`included`.
async fn collect_new_tree_objects(
    odb: &Odb<'_>,
    tree: Oid,
    skip: &HashSet<Oid>,
    included: &mut HashSet<Oid>,
    out: &mut Vec<Oid>,
) -> Result<(), String> {
    if skip.contains(&tree) || !included.insert(tree) {
        return Ok(());
    }
    out.push(tree);
    let entries = odb.read_tree(tree).await?;
    for e in entries.iter() {
        if e.is_tree() {
            Box::pin(collect_new_tree_objects(odb, e.oid, skip, included, out)).await?;
        } else if !skip.contains(&e.oid) && included.insert(e.oid) {
            out.push(e.oid);
        }
    }
    Ok(())
}

/// How one planned object will be emitted into the response pack.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EmitMode {
    /// Copy the stored compressed payload verbatim (full entry).
    Copy,
    /// Copy the stored compressed delta verbatim as `REF_DELTA` on this base.
    RefDelta(Oid),
    /// Base unavailable to the client: materialize and re-deflate.
    Materialize,
}

/// A fully decided pack emission plan: which entries, from which packs, in
/// which representation. Metadata only (~100 B/object) — payload bytes are
/// read during emission, not planning.
pub struct PackPlan {
    pub entries: Vec<(String, EntryRecord, EmitMode)>,
}

/// Decide the emission plan for a fetch set, reusing compressed bytes
/// wherever the representation allows.
///
/// Objects are emitted in *source pack offset order*, not selection order:
/// reads then walk each pack sequentially, so the odb's block cache turns
/// per-object ranged reads into O(bytes / block size) backend requests.
/// (Entry order within a pack is ours to choose — we only emit full and
/// `REF_DELTA` entries, which `git index-pack` accepts in any order.)
pub fn plan_pack(odb: &Odb<'_>, set: &FetchSet, thin_ok: bool) -> Result<PackPlan, String> {
    let included: HashSet<Oid> = set.include.iter().copied().collect();
    let mut entries: Vec<(String, EntryRecord, EmitMode)> = Vec::with_capacity(set.include.len());
    for &oid in &set.include {
        let (pack_id, rec) = odb.locate(oid).ok_or_else(|| format!("{oid} vanished"))?;
        let mode = match rec.base_oid {
            None => EmitMode::Copy,
            Some(base)
                if included.contains(&base) || (thin_ok && set.client_has.contains(&base)) =>
            {
                EmitMode::RefDelta(base)
            }
            Some(_) => EmitMode::Materialize,
        };
        entries.push((pack_id.to_string(), rec.clone(), mode));
    }
    entries.sort_by(|a, b| (&a.0, a.1.data_start).cmp(&(&b.0, b.1.data_start)));
    Ok(PackPlan { entries })
}

/// Incremental pack emission: yields the pack in bounded chunks so a
/// response can stream a repo of any size without holding it in memory (the
/// Workers isolate limit is a hard 128 MiB — see `tests/memory.rs`).
///
/// Copied payloads are appended in ≤1 MiB pieces via ranged reads (a single
/// huge blob is never resident); only [`EmitMode::Materialize`] entries
/// (deltas whose base the client lacks — rare) materialize a whole object.
pub struct PackEmitter {
    entries: Vec<(String, EntryRecord, EmitMode)>,
    idx: usize,
    /// Payload bytes of the current entry already appended.
    payload_pos: u64,
    header_written: bool,
    writer: Option<crate::pack::write::PackWriter>,
}

/// Target response chunk size, and the piece size for copied payload reads.
const EMIT_CHUNK: usize = 1024 * 1024;

impl PackEmitter {
    pub fn new(plan: PackPlan) -> PackEmitter {
        let writer = crate::pack::write::PackWriter::new(plan.entries.len() as u32);
        PackEmitter {
            entries: plan.entries,
            idx: 0,
            payload_pos: 0,
            header_written: false,
            writer: Some(writer),
        }
    }

    /// Produce the next ~[`EMIT_CHUNK`] of pack bytes, or `None` when done.
    pub async fn next_chunk(&mut self, odb: &Odb<'_>) -> Result<Option<Vec<u8>>, String> {
        let Some(w) = self.writer.as_mut() else {
            return Ok(None);
        };
        while self.idx < self.entries.len() && w.buffered() < EMIT_CHUNK {
            let (pack_id, rec, mode) = &self.entries[self.idx];
            match mode {
                EmitMode::Materialize => {
                    let (ty, content) = odb.read(rec.oid).await?.ok_or("object vanished")?;
                    w.add_full(ty, &content);
                    self.idx += 1;
                }
                EmitMode::Copy | EmitMode::RefDelta(_) => {
                    if !self.header_written {
                        match mode {
                            EmitMode::Copy => w.begin_full_precompressed(rec.stored_type, rec.size),
                            EmitMode::RefDelta(base) => {
                                w.begin_ref_delta_precompressed(*base, rec.payload_size)
                            }
                            EmitMode::Materialize => unreachable!(),
                        }
                        self.header_written = true;
                        self.payload_pos = 0;
                    }
                    let total = rec.data_end - rec.data_start;
                    let piece = (total - self.payload_pos).min(EMIT_CHUNK as u64);
                    let bytes = odb
                        .read_compressed_range(pack_id, rec, self.payload_pos, piece)
                        .await?;
                    w.append_payload(&bytes);
                    self.payload_pos += piece;
                    if self.payload_pos >= total {
                        w.end_entry();
                        self.header_written = false;
                        self.idx += 1;
                    }
                }
            }
        }
        if self.idx < self.entries.len() {
            return Ok(Some(w.take_chunk()));
        }
        // All entries emitted: flush whatever is buffered plus the trailer.
        let mut out = w.take_chunk();
        let (tail, _sum) = self.writer.take().unwrap().finish();
        out.extend_from_slice(&tail);
        Ok(Some(out))
    }
}

/// Build a whole response pack in memory (tests and benchmarks; production
/// streams via [`PackEmitter`]).
pub async fn build_pack(odb: &Odb<'_>, set: &FetchSet, thin_ok: bool) -> Result<Vec<u8>, String> {
    let mut emitter = PackEmitter::new(plan_pack(odb, set, thin_ok)?);
    let mut out = Vec::new();
    while let Some(chunk) = emitter.next_chunk(odb).await? {
        out.extend_from_slice(&chunk);
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::storage::MemStore;
    use futures::executor::block_on;

    fn record(path: &str, n: u64) -> FileLogRecord {
        // Offset by 1: the all-zero oid encodes "absent" in GSFL.
        FileLogRecord {
            path: path.to_string(),
            commit: format!("{:040x}", n + 1),
            time: n as i64,
            change: if n == 0 { Change::Add } else { Change::Modify },
            blob: format!("{:040x}", n + 1_000_000),
            prev_commit: (n > 0).then(|| format!("{n:040x}")),
            prev_blob: (n > 0).then(|| format!("{:040x}", n + 999_999)),
        }
    }

    #[test]
    fn filelog_segment_binary_roundtrip() {
        let seg = FileLogSegment {
            records: vec![record("a/b.txt", 0), record("a/b.txt", 1), record("z", 5)],
        };
        let parsed = FileLogSegment::from_bytes(&seg.to_bytes()).unwrap();
        assert_eq!(parsed.records.len(), 3);
        assert_eq!(parsed.records[0].path, "a/b.txt");
        assert_eq!(parsed.records[0].change, Change::Add);
        assert_eq!(parsed.records[1].prev_commit, seg.records[1].prev_commit);
        assert!(FileLogSegment::from_bytes(b"JUNK").is_err());
    }

    #[test]
    fn sharded_filelog_roundtrip_and_scoped_loads() {
        block_on(async {
            let store = MemStore::new();
            // Enough records across enough paths to force several shards.
            let mut records = Vec::new();
            for p in 0..3_000 {
                let path = format!("dir{:02}/subdir/file{p:05}.txt", p % 20);
                for v in 0..3 {
                    records.push(record(&path, v));
                }
            }
            let shards = write_sharded_filelog(&store, "r", "seg", records.clone())
                .await
                .unwrap();
            assert!(shards >= 3, "expected several shards, got {shards}");

            let state = RepoState {
                filelog: vec!["seg".to_string()],
                ..RepoState::empty()
            };

            // Exact-path scope: exactly one shard is loaded (a path's records
            // are never split), and the chain is complete and in order.
            store.reset_op_counts();
            let target = "dir07/subdir/file00707.txt";
            let segs = load_filelog_scoped(&store, "r", &state, &FilelogScope::Path(target))
                .await
                .unwrap();
            // index + 1 shard = 2 reads
            assert_eq!(store.op_counts().class_b, 2, "one shard per path query");
            let chain = records_for_path(&segs, target);
            assert_eq!(chain.len(), 3);
            assert_eq!(chain[0].time, 2, "newest first");
            assert_eq!(chain[2].change, Change::Add);

            // Prefix scope: sees every path in the directory.
            let segs =
                load_filelog_scoped(&store, "r", &state, &FilelogScope::Prefix("dir07/subdir/"))
                    .await
                    .unwrap();
            let view = FileLogView::new(&segs);
            for p in 0..3_000u32 {
                if p % 20 == 7 {
                    let path = format!("dir07/subdir/file{p:05}.txt");
                    assert!(view.latest_for_path(&path).is_some(), "{path} visible");
                }
            }
            assert!(view.latest_for_prefix("dir07/").is_some());

            // Scoped load must return a strict subset of the whole log.
            store.reset_op_counts();
            let all = load_filelog_scoped(&store, "r", &state, &FilelogScope::All)
                .await
                .unwrap();
            let all_reads = store.op_counts().class_b;
            assert_eq!(all.iter().map(|s| s.records.len()).sum::<usize>(), 9_000);
            assert_eq!(all_reads as usize, 1 + shards);

            // Deleting removes the index and every shard.
            delete_filelog(&store, "r", "seg").await.unwrap();
            assert!(store.keys().iter().all(|k| !k.contains("filelog")));
        });
    }

    #[test]
    fn scope_intersection_rules() {
        let hit = |scope: &FilelogScope<'_>, min: &str, max: &str| scope.intersects(min, max);
        // Path scope.
        assert!(hit(&FilelogScope::Path("m"), "a", "z"));
        assert!(!hit(&FilelogScope::Path("a"), "b", "z"));
        assert!(!hit(&FilelogScope::Path("z"), "a", "y"));
        // Prefix scope: shards strictly before or after the prefix range are
        // excluded…
        assert!(!hit(&FilelogScope::Prefix("src/"), "a", "b"));
        assert!(!hit(&FilelogScope::Prefix("src/"), "srcz", "zzz"));
        // …but shards starting inside or spanning the range are included.
        assert!(hit(&FilelogScope::Prefix("src/"), "src/zz", "zzz"));
        assert!(hit(&FilelogScope::Prefix("src/"), "a", "zzz"));
        assert!(hit(&FilelogScope::Prefix(""), "a", "b")); // root: everything
                                                           // Paths scope.
        let mut set = std::collections::HashSet::new();
        set.insert("m/file".to_string());
        assert!(hit(&FilelogScope::Paths(&set), "a", "z"));
        assert!(!hit(&FilelogScope::Paths(&set), "n", "z"));
    }
}

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

/// Load all of a repo's file-log segments, newest first.
pub async fn load_filelog(
    store: &dyn Store,
    repo: &str,
    state: &RepoState,
) -> Result<Vec<FileLogSegment>, String> {
    let _t = crate::timing::Phase::start("filelog: load+parse");
    let mut segs = Vec::with_capacity(state.filelog.len());
    for id in state.filelog.iter().rev() {
        let bytes = store
            .get(&filelog_key(repo, id))
            .await
            .map_err(|e| e.to_string())?
            .ok_or_else(|| format!("missing filelog segment {id}"))?;
        segs.push(FileLogSegment::from_bytes(&bytes)?);
    }
    Ok(segs)
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

        // Build the file-log segment for the new commits.
        if let Some((meta, index)) = &new_pack {
            let _t = crate::timing::Phase::start("push: filelog build");
            let segment = self
                .build_filelog_segment(&odb, &old_odb, index, &state)
                .await?;
            if !segment.records.is_empty() {
                self.store
                    .put(&filelog_key(self.name, &meta.id), segment.to_bytes())
                    .await
                    .map_err(|e| e.to_string())?;
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

        // Previous-touch lookup: existing segments (loaded once, indexed in
        // one pass) + the records we generate during this push.
        let existing = load_filelog(self.store, self.name, state).await?;
        let existing_view = FileLogView::new(&existing);
        let mut in_push_latest: HashMap<String, (String, String)> = HashMap::new(); // path → (commit, blob)

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
                let (prev_commit, prev_blob) = match in_push_latest.get(&path) {
                    Some((pc, pb)) => (Some(pc.clone()), Some(pb.clone())),
                    None => match existing_view.latest_for_path(&path) {
                        Some(r) => (Some(r.commit.clone()), Some(r.blob.clone())),
                        None => (None, None),
                    },
                };
                let blob_hex = blob.map(|b| b.to_hex()).unwrap_or_default();
                in_push_latest.insert(path.clone(), (c.to_hex(), blob_hex.clone()));
                segment.records.push(FileLogRecord {
                    path,
                    commit: c.to_hex(),
                    time: commit.commit_time,
                    change,
                    blob: blob_hex,
                    prev_commit,
                    prev_blob,
                });
            }
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

/// Build the response pack for a fetch set, reusing compressed bytes wherever
/// the representation allows. Returns raw pack bytes.
///
/// Objects are emitted in *source pack offset order*, not selection order:
/// reads then walk each pack sequentially, so the odb's block cache turns
/// per-object ranged reads into O(bytes / block size) backend requests.
/// (Entry order within a pack is ours to choose — we only emit full and
/// `REF_DELTA` entries, which `git index-pack` accepts in any order.)
pub async fn build_pack(odb: &Odb<'_>, set: &FetchSet, thin_ok: bool) -> Result<Vec<u8>, String> {
    let included: HashSet<Oid> = set.include.iter().copied().collect();
    let mut located: Vec<(String, EntryRecord)> = Vec::with_capacity(set.include.len());
    for &oid in &set.include {
        let (pack_id, rec) = odb.locate(oid).ok_or_else(|| format!("{oid} vanished"))?;
        located.push((pack_id.to_string(), rec.clone()));
    }
    located.sort_by(|a, b| (&a.0, a.1.data_start).cmp(&(&b.0, b.1.data_start)));

    let mut w = crate::pack::write::PackWriter::new(set.include.len() as u32);
    let mut out: Vec<u8> = Vec::new();
    for (pack_id, rec) in located {
        let oid = rec.oid;
        match rec.base_oid {
            None => {
                let z = odb.read_compressed(&pack_id, &rec).await?;
                w.add_full_precompressed(rec.stored_type, delta_payload_size(&rec), &z);
            }
            Some(base)
                if included.contains(&base) || (thin_ok && set.client_has.contains(&base)) =>
            {
                let z = odb.read_compressed(&pack_id, &rec).await?;
                w.add_ref_delta_precompressed(base, rec.payload_size, &z);
            }
            Some(_) => {
                // Base isn't available to the client: materialize fully.
                let (ty, content) = odb.read(oid).await?.ok_or("object vanished")?;
                w.add_full(ty, &content);
            }
        }
        out.extend_from_slice(&w.take_chunk());
    }
    let (tail, _sum) = w.finish();
    out.extend_from_slice(&tail);
    Ok(out)
}

/// For non-delta records the payload's inflated size is the object size.
fn delta_payload_size(rec: &EntryRecord) -> u64 {
    rec.size
}

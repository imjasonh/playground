//! The unified read layer the filesystem talks to.
//!
//! Every query tries the **local cache first** — a `cat-file` miss against
//! the local repo costs microseconds — and falls back to the **remote JSON
//! API** when the object hasn't been fetched yet. That is the startup race:
//! while the background shallow/full fetches are still running, reads are
//! served remotely in one HTTP round-trip; once objects land locally, the
//! same queries short-circuit to the local repo.
//!
//! Immutable git data (commit → tree, tree contents, blob bytes keyed by
//! oid) is memoized in memory. Refs are the only mutable state: a snapshot
//! is refreshed from the remote on a TTL, and when it changes the local
//! cache is told to fetch incrementally so the new objects go local too.

use crate::cache::{parse_tree, LocalCache, RawTreeEntry};
use crate::remote::Remote;
use crate::vlog;
use std::collections::{BTreeMap, HashMap};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

/// git mode bits for entry classification.
const MODE_TYPE_MASK: u32 = 0o170000;
const MODE_TREE: u32 = 0o040000;
const MODE_SYMLINK: u32 = 0o120000;
const MODE_GITLINK: u32 = 0o160000;
const MODE_EXEC_BIT: u32 = 0o111;

/// What a tree entry is, as the filesystem needs to present it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum EntryKind {
    Dir,
    File { exec: bool },
    Symlink,
}

/// One resolved directory entry.
#[derive(Debug, Clone)]
pub(crate) struct Entry {
    pub name: String,
    pub kind: EntryKind,
    pub oid: String,
    /// Blob size when already known (always known for local blobs; the
    /// remote tree API reports it too). `None` only for directories.
    pub size: Option<u64>,
}

fn kind_of_mode(mode: u32) -> Option<EntryKind> {
    match mode & MODE_TYPE_MASK {
        MODE_TREE => Some(EntryKind::Dir),
        MODE_SYMLINK => Some(EntryKind::Symlink),
        // Submodule pointers have no content to serve; hide them.
        MODE_GITLINK => None,
        _ => Some(EntryKind::File {
            exec: mode & MODE_EXEC_BIT != 0,
        }),
    }
}

/// A point-in-time view of the remote's refs.
#[derive(Debug, Clone)]
pub(crate) struct RefsSnapshot {
    /// HEAD's symref target, e.g. `refs/heads/main`.
    pub head: String,
    /// Full ref name → commit oid.
    pub refs: BTreeMap<String, String>,
}

/// Byte-budgeted blob LRU, keyed by oid (immutable values).
struct BlobLru {
    map: HashMap<String, (Arc<Vec<u8>>, u64)>,
    order: BTreeMap<u64, String>,
    seq: u64,
    bytes: usize,
    budget: usize,
}

impl BlobLru {
    fn new(budget: usize) -> BlobLru {
        BlobLru {
            map: HashMap::new(),
            order: BTreeMap::new(),
            seq: 0,
            bytes: 0,
            budget,
        }
    }

    fn get(&mut self, oid: &str) -> Option<Arc<Vec<u8>>> {
        let (data, old_seq) = self.map.get(oid)?.clone();
        self.seq += 1;
        let seq = self.seq;
        self.order.remove(&old_seq);
        self.order.insert(seq, oid.to_string());
        self.map.insert(oid.to_string(), (data.clone(), seq));
        Some(data)
    }

    fn put(&mut self, oid: &str, data: Arc<Vec<u8>>) {
        if data.len() > self.budget {
            return; // never cache something bigger than the whole budget
        }
        if let Some((old, old_seq)) = self.map.remove(oid) {
            self.order.remove(&old_seq);
            self.bytes -= old.len();
        }
        self.seq += 1;
        self.bytes += data.len();
        self.order.insert(self.seq, oid.to_string());
        self.map.insert(oid.to_string(), (data, self.seq));
        while self.bytes > self.budget {
            let (_, victim) = self.order.pop_first().expect("lru bookkeeping");
            let (data, _) = self.map.remove(&victim).expect("lru bookkeeping");
            self.bytes -= data.len();
        }
    }
}

/// Bounded memo map for immutable metadata. When full it clears wholesale —
/// entries are cheap to recompute and hitting the cap at all is rare.
struct MemoMap<V> {
    map: HashMap<String, V>,
    cap: usize,
}

impl<V: Clone> MemoMap<V> {
    fn new(cap: usize) -> MemoMap<V> {
        MemoMap {
            map: HashMap::new(),
            cap,
        }
    }

    fn get(&self, k: &str) -> Option<V> {
        self.map.get(k).cloned()
    }

    fn put(&mut self, k: String, v: V) {
        if self.map.len() >= self.cap {
            self.map.clear();
        }
        self.map.insert(k, v);
    }
}

/// Caps for the metadata memo maps. Directory listings and commit→tree
/// resolutions are tiny; these caps only bound pathological traversals.
const MEMO_CAP: usize = 1 << 16;

pub(crate) struct Source {
    local: LocalCache,
    remote: Remote,
    refs_ttl: Duration,
    refs: Mutex<Option<(Instant, Arc<RefsSnapshot>)>>,
    /// commit oid → root tree oid (local objects only; immutable).
    commit_tree: Mutex<MemoMap<String>>,
    /// tree oid → parsed entries (local objects only; immutable).
    trees: Mutex<MemoMap<Arc<Vec<RawTreeEntry>>>>,
    /// `"<commit>:<dir path>"` → listing fetched from the remote tree API.
    remote_dirs: Mutex<MemoMap<Arc<Vec<Entry>>>>,
    /// blob oid → size (immutable), for entries whose size wasn't in a
    /// remote listing.
    blob_sizes: Mutex<MemoMap<u64>>,
    blobs: Mutex<BlobLru>,
}

impl Source {
    pub(crate) fn new(
        local: LocalCache,
        remote: Remote,
        refs_ttl: Duration,
        blob_cache_bytes: usize,
    ) -> Source {
        Source {
            local,
            remote,
            refs_ttl,
            refs: Mutex::new(None),
            commit_tree: Mutex::new(MemoMap::new(MEMO_CAP)),
            trees: Mutex::new(MemoMap::new(MEMO_CAP)),
            remote_dirs: Mutex::new(MemoMap::new(MEMO_CAP)),
            blob_sizes: Mutex::new(MemoMap::new(MEMO_CAP)),
            blobs: Mutex::new(BlobLru::new(blob_cache_bytes)),
        }
    }

    /// Current refs, refreshed from the remote at most every `refs_ttl`.
    /// Falls back to the local cache's refs when the remote is unreachable.
    /// A changed snapshot triggers one incremental background fetch.
    pub(crate) fn refs(&self) -> Result<Arc<RefsSnapshot>, String> {
        let mut guard = self.refs.lock().unwrap();
        if let Some((at, snap)) = guard.as_ref() {
            if at.elapsed() < self.refs_ttl {
                return Ok(snap.clone());
            }
        }
        let fetched = match self.remote.refs() {
            Ok(r) => RefsSnapshot {
                head: r.head,
                refs: r.refs,
            },
            Err(remote_err) => match self.local.local_refs() {
                Ok((head, refs)) => {
                    vlog!("refs: remote unreachable ({remote_err}); serving local snapshot");
                    RefsSnapshot { head, refs }
                }
                Err(_) => return Err(remote_err),
            },
        };
        let changed = guard
            .as_ref()
            .map(|(_, prev)| prev.refs != fetched.refs)
            .unwrap_or(false);
        let snap = Arc::new(fetched);
        *guard = Some((Instant::now(), snap.clone()));
        drop(guard);
        if changed {
            vlog!("refs changed; scheduling incremental fetch");
            self.local.fetch_async();
        }
        Ok(snap)
    }

    /// A read of `commit` had to fall through to the remote API: pull the
    /// commit into the local cache in the background so later reads go
    /// local. Current ref tips are skipped — the staged warmup or the
    /// incremental ref fetch is already bringing those in; the targeted
    /// fetch is for everything else (other history, dangling shas).
    fn expand_cache_for(&self, commit: &str) {
        let is_ref_tip = self
            .refs()
            .map(|snap| snap.refs.values().any(|oid| oid == commit))
            .unwrap_or(false);
        if !is_ref_tip {
            self.local.fetch_commit_async(commit);
        }
    }

    /// Root tree oid of a commit, local-only. `Ok(None)` = not local yet.
    fn local_commit_tree(&self, commit: &str) -> Result<Option<String>, String> {
        if let Some(t) = self.commit_tree.lock().unwrap().get(commit) {
            return Ok(Some(t));
        }
        match self.local.commit_tree(commit)? {
            Some(t) => {
                self.commit_tree
                    .lock()
                    .unwrap()
                    .put(commit.to_string(), t.clone());
                Ok(Some(t))
            }
            None => Ok(None),
        }
    }

    /// Parsed entries of a local tree object. `Ok(None)` = not local yet.
    fn local_tree(&self, tree_oid: &str) -> Result<Option<Arc<Vec<RawTreeEntry>>>, String> {
        if let Some(t) = self.trees.lock().unwrap().get(tree_oid) {
            return Ok(Some(t));
        }
        let Some((kind, data)) = self.local.contents(tree_oid)? else {
            return Ok(None);
        };
        if kind != "tree" {
            return Err(format!("object {tree_oid} is a {kind}, not a tree"));
        }
        let entries = Arc::new(parse_tree(&data)?);
        self.trees
            .lock()
            .unwrap()
            .put(tree_oid.to_string(), entries.clone());
        Ok(Some(entries))
    }

    /// Walk `path` inside `commit` using only local objects. Returns the
    /// tree oid at that path, or `Ok(None)` when any object on the way (or
    /// the path itself) isn't locally resolvable as a directory.
    fn local_dir_tree(&self, commit: &str, path: &str) -> Result<Option<String>, String> {
        let Some(mut tree) = self.local_commit_tree(commit)? else {
            return Ok(None);
        };
        for comp in path.split('/').filter(|c| !c.is_empty()) {
            let Some(entries) = self.local_tree(&tree)? else {
                return Ok(None);
            };
            match entries.iter().find(|e| e.name == comp) {
                Some(e) if e.is_tree() => tree = e.oid.clone(),
                _ => return Ok(None),
            }
        }
        Ok(Some(tree))
    }

    fn blob_size(&self, oid: &str) -> Result<Option<u64>, String> {
        if let Some(s) = self.blob_sizes.lock().unwrap().get(oid) {
            return Ok(Some(s));
        }
        if let Some(info) = self.local.info(oid)? {
            self.blob_sizes
                .lock()
                .unwrap()
                .put(oid.to_string(), info.size);
            return Ok(Some(info.size));
        }
        Ok(None)
    }

    fn entry_from_raw(&self, raw: &RawTreeEntry) -> Result<Option<Entry>, String> {
        let Some(kind) = kind_of_mode(raw.mode) else {
            return Ok(None);
        };
        let size = if kind == EntryKind::Dir {
            None
        } else {
            self.blob_size(&raw.oid)?
        };
        Ok(Some(Entry {
            name: raw.name.clone(),
            kind,
            oid: raw.oid.clone(),
            size,
        }))
    }

    /// Directory listing fetched (and memoized) from the remote tree API.
    /// `Ok(None)` when the path isn't a directory at that commit.
    fn remote_dir(&self, commit: &str, path: &str) -> Result<Option<Arc<Vec<Entry>>>, String> {
        let key = format!("{commit}:{path}");
        if let Some(list) = self.remote_dirs.lock().unwrap().get(&key) {
            return Ok(Some(list));
        }
        let Some(resp) = self.remote.tree(commit, path)? else {
            return Ok(None);
        };
        self.expand_cache_for(commit);
        let mut entries = Vec::with_capacity(resp.entries.len());
        for e in resp.entries {
            let mode = u32::from_str_radix(&e.mode, 8)
                .map_err(|_| format!("remote tree: bad mode {}", e.mode))?;
            let Some(kind) = kind_of_mode(mode) else {
                continue;
            };
            let kind = if e.kind == "tree" {
                EntryKind::Dir
            } else {
                kind
            };
            if let Some(size) = e.size {
                self.blob_sizes.lock().unwrap().put(e.oid.clone(), size);
            }
            entries.push(Entry {
                name: e.name,
                kind,
                oid: e.oid,
                size: e.size,
            });
        }
        let entries = Arc::new(entries);
        self.remote_dirs.lock().unwrap().put(key, entries.clone());
        Ok(Some(entries))
    }

    /// Does this commit exist (anywhere)? Cheap local check first, then one
    /// remote root-listing probe (which is memoized for the readdir that
    /// almost always follows).
    pub(crate) fn commit_exists(&self, commit: &str) -> Result<bool, String> {
        if self.local_commit_tree(commit)?.is_some() {
            return Ok(true);
        }
        Ok(self.remote_dir(commit, "")?.is_some())
    }

    /// List the directory `path` inside `commit`. `Ok(None)` when it isn't a
    /// directory there.
    pub(crate) fn readdir(&self, commit: &str, path: &str) -> Result<Option<Vec<Entry>>, String> {
        if let Some(tree) = self.local_dir_tree(commit, path)? {
            if let Some(raws) = self.local_tree(&tree)? {
                self.prefetch_blob_sizes(&raws)?;
                let mut out = Vec::with_capacity(raws.len());
                for raw in raws.iter() {
                    if let Some(e) = self.entry_from_raw(raw)? {
                        out.push(e);
                    }
                }
                return Ok(Some(out));
            }
        }
        Ok(self.remote_dir(commit, path)?.map(|l| (*l).clone()))
    }

    /// Warm the size memo for every non-tree entry of a listing in one
    /// batched cat-file exchange (readdirplus asks for all of them anyway).
    fn prefetch_blob_sizes(&self, raws: &[RawTreeEntry]) -> Result<(), String> {
        let missing: Vec<&str> = {
            let sizes = self.blob_sizes.lock().unwrap();
            raws.iter()
                .filter(|r| !r.is_tree() && sizes.get(&r.oid).is_none())
                .map(|r| r.oid.as_str())
                .collect()
        };
        if missing.is_empty() {
            return Ok(());
        }
        let infos = self.local.infos(&missing)?;
        let mut sizes = self.blob_sizes.lock().unwrap();
        for (oid, info) in missing.iter().zip(infos) {
            if let Some(info) = info {
                sizes.put(oid.to_string(), info.size);
            }
        }
        Ok(())
    }

    /// Resolve one child entry: `dir` is the parent directory path, `name`
    /// the child. `Ok(None)` when it doesn't exist.
    pub(crate) fn lookup(
        &self,
        commit: &str,
        dir: &str,
        name: &str,
    ) -> Result<Option<Entry>, String> {
        if let Some(tree) = self.local_dir_tree(commit, dir)? {
            if let Some(raws) = self.local_tree(&tree)? {
                return match raws.iter().find(|e| e.name == name) {
                    Some(raw) => self.entry_from_raw(raw),
                    None => Ok(None),
                };
            }
        }
        match self.remote_dir(commit, dir)? {
            Some(list) => Ok(list.iter().find(|e| e.name == name).cloned()),
            None => Ok(None),
        }
    }

    /// Read a blob's bytes. `path` locates it under `commit` for the remote
    /// fallback; `oid` is its object id (always known from the lookup that
    /// produced the entry).
    pub(crate) fn read_blob(
        &self,
        commit: &str,
        path: &str,
        oid: &str,
    ) -> Result<Arc<Vec<u8>>, String> {
        if let Some(data) = self.blobs.lock().unwrap().get(oid) {
            return Ok(data);
        }
        let data = match self.local.contents(oid)? {
            Some((kind, data)) => {
                if kind != "blob" {
                    return Err(format!("object {oid} is a {kind}, not a blob"));
                }
                vlog!("blob {oid} served from local cache");
                data
            }
            None => {
                vlog!("blob {oid} not local; fetching {commit}:{path} from remote");
                let data = self
                    .remote
                    .file(commit, path)?
                    .ok_or_else(|| format!("object {oid} not found at {commit}:{path}"))?;
                self.expand_cache_for(commit);
                data
            }
        };
        let data = Arc::new(data);
        self.blob_sizes
            .lock()
            .unwrap()
            .put(oid.to_string(), data.len() as u64);
        self.blobs.lock().unwrap().put(oid, data.clone());
        Ok(data)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn mode_classification() {
        assert_eq!(
            kind_of_mode(0o100644),
            Some(EntryKind::File { exec: false })
        );
        assert_eq!(kind_of_mode(0o100755), Some(EntryKind::File { exec: true }));
        assert_eq!(kind_of_mode(0o040000), Some(EntryKind::Dir));
        assert_eq!(kind_of_mode(0o120000), Some(EntryKind::Symlink));
        assert_eq!(kind_of_mode(0o160000), None); // submodule: hidden
    }

    #[test]
    fn blob_lru_evicts_by_bytes() {
        let mut lru = BlobLru::new(10);
        lru.put("a", Arc::new(vec![0; 4]));
        lru.put("b", Arc::new(vec![0; 4]));
        assert!(lru.get("a").is_some());
        // "b" is now least-recent; adding 4 more bytes evicts it.
        lru.put("c", Arc::new(vec![0; 4]));
        assert!(lru.get("b").is_none());
        assert!(lru.get("a").is_some());
        assert!(lru.get("c").is_some());
        // Oversized values are refused outright.
        lru.put("huge", Arc::new(vec![0; 11]));
        assert!(lru.get("huge").is_none());
    }
}

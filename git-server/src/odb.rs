//! The object database: oid → object across all of a repo's packs.
//!
//! Reads are index-guided ranged gets against R2: look the oid up in the pack
//! indexes (loaded once per request and cached), fetch exactly the compressed
//! payload bytes, inflate, and — for deltas — recurse to the recorded base
//! oid. A per-instance content cache keeps tree walks (file API, blame,
//! reachability) from re-reading hot objects.

use crate::object::{Commit, ObjType, Oid, TreeEntry};
use crate::pack::write::inflate;
use crate::pack::{delta::apply_delta, EntryRecord, PackIndex};
use crate::storage::Store;
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

/// Where a pack and its index live in the byte store.
pub fn pack_key(repo: &str, pack_id: &str) -> String {
    format!("{repo}/pack/{pack_id}.pack")
}

pub fn index_key(repo: &str, pack_id: &str) -> String {
    format!("{repo}/pack/{pack_id}.idx")
}

/// One pack the odb can read from.
struct PackHandle {
    pack_id: String,
    index: PackIndex,
    /// Block-cached reader over the pack: turns clustered per-object reads
    /// into a handful of 4 MiB ranged gets (see [`crate::storage::BlockReader`]).
    reader: crate::storage::BlockReader,
}

/// A materialized object: type + shared content.
pub type CachedObject = (ObjType, Rc<Vec<u8>>);

/// Object database over a fixed set of packs (the repo state's pack manifest
/// at the time the request began — a consistent snapshot).
pub struct Odb<'a> {
    store: &'a dyn Store,
    packs: Vec<PackHandle>,
    cache: RefCell<HashMap<Oid, CachedObject>>,
    cache_bytes: RefCell<usize>,
    /// Parsed-tree cache: tree walks (filelog build, fetch selection, file
    /// API) revisit the same trees; parsing entries once per oid instead of
    /// per visit is a large win on big pushes.
    tree_cache: RefCell<HashMap<Oid, Rc<Vec<TreeEntry>>>>,
}

/// Cache budget for materialized objects, sized for tree walks / blame /
/// fetch-set collection over big repos. Was briefly halved to 24 MiB while
/// chasing a suspected memory bug; the real large-push failure was CPU
/// (free-tier cap), not memory, so this is restored to 48 MiB — a smaller
/// cache just meant more R2 re-reads on the read paths for no safety gain.
/// Bounded well under the 128 MiB isolate (see `tests/memory.rs`).
const CONTENT_CACHE_BUDGET: usize = 48 * 1024 * 1024;

impl<'a> Odb<'a> {
    /// Load the indexes for `pack_ids` (one Class B read per pack).
    pub async fn open(
        store: &'a dyn Store,
        repo: &'a str,
        pack_ids: &[String],
    ) -> Result<Odb<'a>, String> {
        let mut packs = Vec::with_capacity(pack_ids.len());
        for id in pack_ids {
            let bytes = store
                .get(&index_key(repo, id))
                .await
                .map_err(|e| e.to_string())?
                .ok_or_else(|| format!("missing pack index for {id}"))?;
            packs.push(PackHandle {
                pack_id: id.clone(),
                index: PackIndex::from_bytes(&bytes)?,
                reader: crate::storage::BlockReader::new(&pack_key(repo, id)),
            });
        }
        Ok(Odb {
            store,
            packs,
            cache: RefCell::new(HashMap::new()),
            cache_bytes: RefCell::new(0),
            tree_cache: RefCell::new(HashMap::new()),
        })
    }

    /// Locate an oid: (pack_id, record).
    pub fn locate(&self, oid: Oid) -> Option<(&str, &EntryRecord)> {
        // Newest pack first: recent pushes shadow older copies of the same oid.
        for p in self.packs.iter().rev() {
            if let Some(rec) = p.index.lookup(oid) {
                return Some((&p.pack_id, rec));
            }
        }
        None
    }

    pub fn contains(&self, oid: Oid) -> bool {
        self.locate(oid).is_some()
    }

    /// Final type and inflated size from the pack index, without reading
    /// content. Used by partial-clone filters (`blob:limit=…`) to decide
    /// omission without materializing the object.
    pub fn meta(&self, oid: Oid) -> Option<(ObjType, u64)> {
        self.locate(oid).map(|(_, rec)| (rec.final_type, rec.size))
    }

    /// All oids across all packs (deduplicated), for clone reachability.
    pub fn all_oids(&self) -> Vec<Oid> {
        let mut seen = std::collections::HashSet::new();
        let mut out = Vec::new();
        for p in self.packs.iter().rev() {
            for r in &p.index.records {
                if seen.insert(r.oid) {
                    out.push(r.oid);
                }
            }
        }
        out
    }

    /// Read an object's compressed payload verbatim (for pack-copy reuse),
    /// through the pack's block cache.
    pub async fn read_compressed(
        &self,
        pack_id: &str,
        rec: &EntryRecord,
    ) -> Result<Vec<u8>, String> {
        self.read_compressed_range(pack_id, rec, 0, rec.data_end - rec.data_start)
            .await
    }

    /// Read `len` bytes of an entry's compressed payload starting at
    /// `offset` (streamed pack emission copies huge payloads in pieces so
    /// they are never fully resident).
    pub async fn read_compressed_range(
        &self,
        pack_id: &str,
        rec: &EntryRecord,
        offset: u64,
        len: u64,
    ) -> Result<Vec<u8>, String> {
        let handle = self
            .packs
            .iter()
            .find(|p| p.pack_id == pack_id)
            .ok_or_else(|| format!("pack {pack_id} not open"))?;
        let start = rec.data_start + offset;
        let end = (start + len).min(rec.data_end);
        handle
            .reader
            .read(self.store, start, end)
            .await
            .map_err(|e| e.to_string())
    }

    /// Read and fully materialize an object.
    pub async fn read(&self, oid: Oid) -> Result<Option<(ObjType, Rc<Vec<u8>>)>, String> {
        if let Some(hit) = self.cache.borrow().get(&oid) {
            return Ok(Some(hit.clone()));
        }
        // Collect the delta chain (root last), then apply downward.
        let mut chain: Vec<(String, EntryRecord)> = Vec::new();
        let mut cursor = oid;
        let (ty, mut content) = loop {
            if let Some(hit) = self.cache.borrow().get(&cursor) {
                break hit.clone();
            }
            let (pack_id, rec) = match self.locate(cursor) {
                Some((p, r)) => (p.to_string(), r.clone()),
                None => {
                    return if chain.is_empty() {
                        Ok(None)
                    } else {
                        Err(format!("dangling delta base {cursor}"))
                    }
                }
            };
            match rec.base_oid {
                None => {
                    let raw = self.read_compressed(&pack_id, &rec).await?;
                    let data = Rc::new(inflate(&raw, rec.size)?);
                    let ty = rec.final_type;
                    self.cache_put(cursor, ty, data.clone());
                    break (ty, data);
                }
                Some(base) => {
                    chain.push((pack_id, rec));
                    cursor = base;
                    if chain.len() > 10_000 {
                        return Err("delta chain too long".into());
                    }
                }
            }
        };
        for (pack_id, rec) in chain.iter().rev() {
            let raw = self.read_compressed(pack_id, rec).await?;
            // rec.size is the *final* object size; the delta payload's own
            // inflated size is unknown here, so inflate without a hard check.
            let delta = inflate_unchecked(&raw)?;
            let applied = apply_delta(&content, &delta)?;
            content = Rc::new(applied);
            let key = rec.oid;
            self.cache_put(key, ty, content.clone());
        }
        Ok(Some((ty, content)))
    }

    /// Read an object, verifying the expected type.
    pub async fn read_typed(&self, oid: Oid, want: ObjType) -> Result<Rc<Vec<u8>>, String> {
        match self.read(oid).await? {
            Some((ty, data)) if ty == want => Ok(data),
            Some((ty, _)) => Err(format!(
                "object {oid} is a {}, expected {}",
                ty.name(),
                want.name()
            )),
            None => Err(format!("object {oid} not found")),
        }
    }

    pub async fn read_commit(&self, oid: Oid) -> Result<Commit, String> {
        let data = self.read_typed(oid, ObjType::Commit).await?;
        crate::object::parse_commit(&data)
    }

    pub async fn read_tree(&self, oid: Oid) -> Result<Rc<Vec<TreeEntry>>, String> {
        if let Some(hit) = self.tree_cache.borrow().get(&oid) {
            return Ok(hit.clone());
        }
        let data = self.read_typed(oid, ObjType::Tree).await?;
        let parsed = Rc::new(crate::object::parse_tree(&data)?);
        // Parsed entries are ~the size of the raw tree; keep the cache in the
        // same ballpark as the content cache by piggybacking on its budget
        // accounting (a tree's raw bytes are already counted there).
        if self.tree_cache.borrow().len() > 100_000 {
            self.tree_cache.borrow_mut().clear();
        }
        self.tree_cache.borrow_mut().insert(oid, parsed.clone());
        Ok(parsed)
    }

    /// Peel an object to a commit: commits pass through, annotated tags are
    /// dereferenced (possibly repeatedly).
    pub async fn peel_to_commit(&self, oid: Oid) -> Result<Oid, String> {
        let mut cursor = oid;
        for _ in 0..16 {
            match self.read(cursor).await? {
                Some((ObjType::Commit, _)) => return Ok(cursor),
                Some((ObjType::Tag, data)) => {
                    let text = String::from_utf8_lossy(&data);
                    let target = text
                        .lines()
                        .find_map(|l| l.strip_prefix("object "))
                        .and_then(Oid::from_hex)
                        .ok_or("tag object missing target")?;
                    cursor = target;
                }
                Some((ty, _)) => return Err(format!("{oid} peels to a {}", ty.name())),
                None => return Err(format!("object {cursor} not found")),
            }
        }
        Err("tag chain too deep".into())
    }

    fn cache_put(&self, oid: Oid, ty: ObjType, content: Rc<Vec<u8>>) {
        let mut bytes = self.cache_bytes.borrow_mut();
        if *bytes + content.len() > CONTENT_CACHE_BUDGET {
            self.cache.borrow_mut().clear();
            *bytes = 0;
        }
        *bytes += content.len();
        self.cache.borrow_mut().insert(oid, (ty, content));
    }
}

/// Inflate a zlib stream whose inflated size we don't know in advance.
fn inflate_unchecked(data: &[u8]) -> Result<Vec<u8>, String> {
    let mut out = Vec::new();
    let mut dec = flate2::Decompress::new(true);
    let mut scratch = vec![0u8; 64 * 1024];
    let mut pos = 0usize;
    loop {
        let before_in = dec.total_in();
        let before_out = dec.total_out();
        let status = dec
            .decompress(&data[pos..], &mut scratch, flate2::FlushDecompress::None)
            .map_err(|e| format!("zlib: {e}"))?;
        pos += (dec.total_in() - before_in) as usize;
        let produced = (dec.total_out() - before_out) as usize;
        out.extend_from_slice(&scratch[..produced]);
        match status {
            flate2::Status::StreamEnd => return Ok(out),
            _ if produced == 0 && pos >= data.len() => return Err("zlib: truncated stream".into()),
            _ => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::object::hash_object;
    use crate::pack::index::{resolve_pack, NoExternalBases, PackIndex};
    use crate::pack::write::test_support::build_pack;
    use crate::pack::PackScanner;
    use crate::storage::MemStore;
    use futures::executor::block_on;

    /// Store a pack + index under `repo` and return its pack id.
    pub async fn install_pack(store: &MemStore, repo: &str, pack: &[u8]) -> String {
        let mut s = PackScanner::new();
        s.feed(pack).unwrap();
        let scanned = s.finish().unwrap();
        let id = hex::encode(scanned.checksum);
        store
            .put(&pack_key(repo, &id), pack.to_vec())
            .await
            .unwrap();
        let recs = resolve_pack(store, &pack_key(repo, &id), &scanned, &NoExternalBases)
            .await
            .unwrap();
        store
            .put(&index_key(repo, &id), PackIndex::new(recs).to_bytes())
            .await
            .unwrap();
        id
    }

    #[test]
    fn reads_across_multiple_packs() {
        block_on(async {
            let store = MemStore::new();
            let a = build_pack(&[(ObjType::Blob, b"alpha".to_vec())]);
            let b = build_pack(&[(ObjType::Blob, b"beta".to_vec())]);
            let ida = install_pack(&store, "r", &a).await;
            let idb = install_pack(&store, "r", &b).await;
            let odb = Odb::open(&store, "r", &[ida, idb]).await.unwrap();

            let alpha = hash_object(ObjType::Blob, b"alpha");
            let beta = hash_object(ObjType::Blob, b"beta");
            assert_eq!(*odb.read(alpha).await.unwrap().unwrap().1, b"alpha");
            assert_eq!(*odb.read(beta).await.unwrap().unwrap().1, b"beta");
            assert!(odb.read(Oid::ZERO).await.unwrap().is_none());
            assert_eq!(odb.all_oids().len(), 2);
        });
    }
}

//! Delta resolution and the `GSIX` pack index.
//!
//! After a pushed pack has been streamed to R2 and scanned
//! ([`super::scan`]), every delta entry still needs its final object id and
//! type. [`resolve_pack`] does that with *ranged reads* against the stored
//! pack: it walks delta chains, reading each compressed payload only when
//! needed and keeping a byte-budgeted content cache, so memory stays bounded
//! no matter how large the pack is.
//!
//! The result is serialized as a `GSIX` index object next to the pack in R2.
//! Per entry it records the compressed byte range (so reads are exact ranged
//! gets), the *final* type/size, and — for deltas — the resolved base oid.
//! Storing the base oid is what lets the read path hop delta chains with pure
//! oid lookups, and lets repacking rewrite `OFS_DELTA` entries as `REF_DELTA`
//! without touching payload bytes.

use crate::object::{hash_object, ObjType, Oid};
use crate::pack::scan::{BaseRef, ScannedPack};
use crate::pack::write::inflate;
use crate::storage::{StorageError, Store};
use std::collections::HashMap;
use std::rc::Rc;

/// One indexed entry.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EntryRecord {
    pub oid: Oid,
    /// Offset of the entry header in the pack.
    pub header_start: u64,
    /// Compressed payload byte range.
    pub data_start: u64,
    pub data_end: u64,
    /// On-disk type (1-4 full, 6/7 delta).
    pub stored_type: u8,
    /// Final object type after delta resolution.
    pub final_type: ObjType,
    /// Final (fully inflated, delta-applied) object size.
    pub size: u64,
    /// Inflated size of the stored payload itself (== `size` for full
    /// entries; the delta blob's size for delta entries). Recorded so pack
    /// copy paths can re-emit entry headers without inflating the payload.
    pub payload_size: u64,
    /// For delta entries: the resolved base object id.
    pub base_oid: Option<Oid>,
}

/// Provider of base objects that live *outside* the pack being resolved
/// (thin-pack bases). Returns (type, content).
#[async_trait::async_trait(?Send)]
pub trait ExternalBases {
    async fn get_object(&self, oid: Oid) -> Result<Option<(ObjType, Rc<Vec<u8>>)>, String>;
}

/// An [`ExternalBases`] that has nothing — for self-contained packs.
pub struct NoExternalBases;

#[async_trait::async_trait(?Send)]
impl ExternalBases for NoExternalBases {
    async fn get_object(&self, _oid: Oid) -> Result<Option<(ObjType, Rc<Vec<u8>>)>, String> {
        Ok(None)
    }
}

/// Byte budget for the delta-resolution content cache. Bases are usually
/// clustered (git orders packs so deltas sit near their bases), so this
/// cache eliminates nearly all repeat reads while resolving a pushed pack.
/// Restored to 32 MiB (from a brief 24 MiB dip taken while chasing a
/// phantom memory bug — the real large-push limit was CPU, not memory);
/// still comfortably within the 128 MiB isolate.
const RESOLVE_CACHE_BUDGET: usize = 32 * 1024 * 1024;

/// Resolve all entries of a scanned pack stored at `pack_key` in `store`,
/// producing index records sorted by oid.
pub async fn resolve_pack(
    store: &dyn Store,
    pack_key: &str,
    scanned: &ScannedPack,
    external: &dyn ExternalBases,
) -> Result<Vec<EntryRecord>, String> {
    let entries = &scanned.entries;
    let by_offset: HashMap<u64, usize> = entries
        .iter()
        .enumerate()
        .map(|(i, e)| (e.header_start, i))
        .collect();
    // Non-delta entries already have oids from the scan; they can be REF_DELTA
    // bases for later entries in the same pack.
    let mut oid_to_idx: HashMap<Oid, usize> = entries
        .iter()
        .enumerate()
        .filter_map(|(i, e)| e.oid.map(|o| (o, i)))
        .collect();

    let mut resolver = Resolver {
        store,
        reader: crate::storage::BlockReader::new(pack_key),
        entries,
        by_offset,
        cache: HashMap::new(),
        cache_bytes: 0,
        external,
    };

    let mut records: Vec<EntryRecord> = Vec::with_capacity(entries.len());
    #[allow(clippy::needless_range_loop)] // `records` is also indexed below
    for i in 0..entries.len() {
        let e = &entries[i];
        // Non-delta entries were fully identified during the streaming scan
        // (oid hashed, size known): no need to touch their payloads again.
        // Only delta entries require materialization.
        let (ty, oid, size) = match (e.oid, e.base) {
            (Some(oid), BaseRef::None) => {
                let ty = ObjType::from_pack_type(e.stored_type)
                    .ok_or_else(|| format!("bad stored type {}", e.stored_type))?;
                (ty, oid, e.inflated_size)
            }
            _ => {
                let (ty, content) = resolver.content_of(i, &oid_to_idx).await?;
                let oid = hash_object(ty, &content);
                oid_to_idx.insert(oid, i);
                (ty, oid, content.len() as u64)
            }
        };
        let base_oid = match e.base {
            BaseRef::None => None,
            BaseRef::Id(o) => Some(o),
            BaseRef::Offset(off) => {
                let bi = *resolver.by_offset.get(&off).ok_or_else(|| {
                    format!("ofs-delta base offset {off} does not match an entry")
                })?;
                // Base precedes its delta, so it is already resolved.
                Some(records[bi].oid)
            }
        };
        records.push(EntryRecord {
            oid,
            header_start: e.header_start,
            data_start: e.data_start,
            data_end: e.data_end,
            stored_type: e.stored_type,
            final_type: ty,
            size,
            payload_size: e.inflated_size,
            base_oid,
        });
    }
    records.sort_by(|a, b| a.oid.cmp(&b.oid));
    Ok(records)
}

struct Resolver<'a> {
    store: &'a dyn Store,
    /// Block-cached reads over the stored pack: entries are processed in
    /// offset order and delta bases cluster near their deltas, so this turns
    /// per-entry ranged reads into O(pack bytes / block size) requests.
    reader: crate::storage::BlockReader,
    entries: &'a [crate::pack::scan::ScanEntry],
    by_offset: HashMap<u64, usize>,
    cache: HashMap<usize, (ObjType, Rc<Vec<u8>>)>,
    cache_bytes: usize,
    external: &'a dyn ExternalBases,
}

impl Resolver<'_> {
    async fn read_payload(&self, i: usize) -> Result<Vec<u8>, String> {
        let e = &self.entries[i];
        let raw = self
            .reader
            .read(self.store, e.data_start, e.data_end)
            .await
            .map_err(|se: StorageError| se.to_string())?;
        inflate(&raw, e.inflated_size)
    }

    /// Materialize entry `i`'s full content, resolving delta chains
    /// iteratively (a chain is found root-first, then applied downward).
    async fn content_of(
        &mut self,
        i: usize,
        oid_to_idx: &HashMap<Oid, usize>,
    ) -> Result<(ObjType, Rc<Vec<u8>>), String> {
        if let Some(hit) = self.cache.get(&i) {
            return Ok(hit.clone());
        }
        // Walk up the chain until a cached / non-delta / external root.
        let mut chain: Vec<usize> = Vec::new(); // deltas to apply, deepest last
        let mut cursor = i;
        // Delta application never changes the object type, so `ty` is fixed
        // once the chain root is found.
        let (ty, mut content): (ObjType, Rc<Vec<u8>>) = loop {
            if let Some(hit) = self.cache.get(&cursor) {
                break hit.clone();
            }
            let e = &self.entries[cursor];
            match e.base {
                BaseRef::None => {
                    let ty = ObjType::from_pack_type(e.stored_type)
                        .ok_or_else(|| format!("bad stored type {}", e.stored_type))?;
                    let content = Rc::new(self.read_payload(cursor).await?);
                    self.cache_put(cursor, ty, content.clone());
                    break (ty, content);
                }
                BaseRef::Offset(off) => {
                    chain.push(cursor);
                    cursor = *self
                        .by_offset
                        .get(&off)
                        .ok_or_else(|| format!("ofs-delta base offset {off} not found"))?;
                }
                BaseRef::Id(oid) => {
                    chain.push(cursor);
                    if let Some(&bi) = oid_to_idx.get(&oid) {
                        cursor = bi;
                    } else {
                        // Thin-pack base: outside this pack.
                        let (ty, content) = self
                            .external
                            .get_object(oid)
                            .await?
                            .ok_or_else(|| format!("thin-pack base {oid} not found"))?;
                        break (ty, content);
                    }
                }
            }
            if chain.len() > 10_000 {
                return Err("delta chain too long".into());
            }
        };
        // Apply the chain downward (deepest chain element is the last pushed).
        for &di in chain.iter().rev() {
            let delta = self.read_payload(di).await?;
            let applied = crate::pack::delta::apply_delta(&content, &delta)?;
            content = Rc::new(applied);
            self.cache_put(di, ty, content.clone());
        }
        Ok((ty, content))
    }

    fn cache_put(&mut self, i: usize, ty: ObjType, content: Rc<Vec<u8>>) {
        if self.cache_bytes + content.len() > RESOLVE_CACHE_BUDGET {
            // Crude but bounded: drop everything. Bases cluster near their
            // deltas, so the working set rebuilds quickly.
            self.cache.clear();
            self.cache_bytes = 0;
        }
        self.cache_bytes += content.len();
        self.cache.insert(i, (ty, content));
    }
}

// ---------------------------------------------------------------------------
// GSIX serialization
// ---------------------------------------------------------------------------

const GSIX_MAGIC: &[u8; 4] = b"GSIX";
const GSIX_VERSION: u32 = 1;
/// oid(20) + header_start(8) + data_start(8) + data_end(8) + stored_type(1) +
/// final_type(1) + size(8) + payload_size(8) + base_oid(20)
const RECORD_LEN: usize = 82;

/// A parsed pack index: records sorted by oid.
#[derive(Debug, Clone, Default)]
pub struct PackIndex {
    pub records: Vec<EntryRecord>,
}

impl PackIndex {
    pub fn new(mut records: Vec<EntryRecord>) -> Self {
        records.sort_by(|a, b| a.oid.cmp(&b.oid));
        PackIndex { records }
    }

    pub fn lookup(&self, oid: Oid) -> Option<&EntryRecord> {
        self.records
            .binary_search_by(|r| r.oid.cmp(&oid))
            .ok()
            .map(|i| &self.records[i])
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(12 + self.records.len() * RECORD_LEN);
        out.extend_from_slice(GSIX_MAGIC);
        out.extend_from_slice(&GSIX_VERSION.to_be_bytes());
        out.extend_from_slice(&(self.records.len() as u32).to_be_bytes());
        for r in &self.records {
            out.extend_from_slice(&r.oid.0);
            out.extend_from_slice(&r.header_start.to_be_bytes());
            out.extend_from_slice(&r.data_start.to_be_bytes());
            out.extend_from_slice(&r.data_end.to_be_bytes());
            out.push(r.stored_type);
            out.push(r.final_type.pack_type());
            out.extend_from_slice(&r.size.to_be_bytes());
            out.extend_from_slice(&r.payload_size.to_be_bytes());
            out.extend_from_slice(&r.base_oid.unwrap_or(Oid::ZERO).0);
        }
        out
    }

    pub fn from_bytes(data: &[u8]) -> Result<Self, String> {
        if data.len() < 12 || &data[..4] != GSIX_MAGIC {
            return Err("bad GSIX magic".into());
        }
        let version = u32::from_be_bytes(data[4..8].try_into().unwrap());
        if version != GSIX_VERSION {
            return Err(format!("unsupported GSIX version {version}"));
        }
        let count = u32::from_be_bytes(data[8..12].try_into().unwrap()) as usize;
        if data.len() != 12 + count * RECORD_LEN {
            return Err("GSIX length mismatch".into());
        }
        let mut records = Vec::with_capacity(count);
        for i in 0..count {
            let p = 12 + i * RECORD_LEN;
            let r = &data[p..p + RECORD_LEN];
            let base = Oid::from_bytes(&r[62..82]).unwrap();
            records.push(EntryRecord {
                oid: Oid::from_bytes(&r[..20]).unwrap(),
                header_start: u64::from_be_bytes(r[20..28].try_into().unwrap()),
                data_start: u64::from_be_bytes(r[28..36].try_into().unwrap()),
                data_end: u64::from_be_bytes(r[36..44].try_into().unwrap()),
                stored_type: r[44],
                final_type: ObjType::from_pack_type(r[45])
                    .ok_or_else(|| format!("bad final type {}", r[45]))?,
                size: u64::from_be_bytes(r[46..54].try_into().unwrap()),
                payload_size: u64::from_be_bytes(r[54..62].try_into().unwrap()),
                base_oid: if base.is_zero() { None } else { Some(base) },
            });
        }
        Ok(PackIndex { records })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::object::hash_object;
    use crate::pack::delta::literal_delta;
    use crate::pack::write::{deflate, test_support::build_pack, PackWriter};
    use crate::pack::PackScanner;
    use crate::storage::MemStore;
    use futures::executor::block_on;

    fn scan(pack: &[u8]) -> ScannedPack {
        let mut s = PackScanner::new();
        s.feed(pack).unwrap();
        s.finish().unwrap()
    }

    #[test]
    fn resolves_full_objects() {
        block_on(async {
            let objs = vec![
                (ObjType::Blob, b"one".to_vec()),
                (ObjType::Blob, b"two".to_vec()),
            ];
            let pack = build_pack(&objs);
            let store = MemStore::new();
            store.put("p", pack.clone()).await.unwrap();
            let scanned = scan(&pack);
            let recs = resolve_pack(&store, "p", &scanned, &NoExternalBases)
                .await
                .unwrap();
            assert_eq!(recs.len(), 2);
            let idx = PackIndex::new(recs);
            for (ty, data) in &objs {
                let oid = hash_object(*ty, data);
                let r = idx.lookup(oid).expect("entry present");
                assert_eq!(r.final_type, *ty);
                assert_eq!(r.size, data.len() as u64);
                assert!(r.base_oid.is_none());
            }
        });
    }

    #[test]
    fn resolves_ref_delta_chain() {
        block_on(async {
            let base = b"the quick brown fox jumps over the lazy dog".to_vec();
            let mid = b"the quick brown fox".to_vec();
            let tip = b"lazy dog".to_vec();
            let base_oid = hash_object(ObjType::Blob, &base);
            let mid_oid = hash_object(ObjType::Blob, &mid);
            let tip_oid = hash_object(ObjType::Blob, &tip);

            let mut w = PackWriter::new(3);
            w.add_full(ObjType::Blob, &base);
            let d1 = literal_delta(base.len(), &mid);
            w.add_ref_delta_precompressed(base_oid, d1.len() as u64, &deflate(&d1));
            let d2 = literal_delta(mid.len(), &tip);
            w.add_ref_delta_precompressed(mid_oid, d2.len() as u64, &deflate(&d2));
            let (pack, _) = w.finish();

            let store = MemStore::new();
            store.put("p", pack.clone()).await.unwrap();
            let scanned = scan(&pack);
            let idx = PackIndex::new(
                resolve_pack(&store, "p", &scanned, &NoExternalBases)
                    .await
                    .unwrap(),
            );
            let tip_rec = idx.lookup(tip_oid).expect("tip resolved");
            assert_eq!(tip_rec.final_type, ObjType::Blob);
            assert_eq!(tip_rec.base_oid, Some(mid_oid));
            assert_eq!(idx.lookup(mid_oid).unwrap().base_oid, Some(base_oid));
        });
    }

    #[test]
    fn resolves_thin_pack_via_external_bases() {
        block_on(async {
            struct OneBase(Oid, Vec<u8>);
            #[async_trait::async_trait(?Send)]
            impl ExternalBases for OneBase {
                async fn get_object(
                    &self,
                    oid: Oid,
                ) -> Result<Option<(ObjType, Rc<Vec<u8>>)>, String> {
                    Ok((oid == self.0).then(|| (ObjType::Blob, Rc::new(self.1.clone()))))
                }
            }
            let base = b"external base content".to_vec();
            let base_oid = hash_object(ObjType::Blob, &base);
            let target = b"target".to_vec();
            let target_oid = hash_object(ObjType::Blob, &target);

            let mut w = PackWriter::new(1);
            let d = literal_delta(base.len(), &target);
            w.add_ref_delta_precompressed(base_oid, d.len() as u64, &deflate(&d));
            let (pack, _) = w.finish();

            let store = MemStore::new();
            store.put("p", pack.clone()).await.unwrap();
            let scanned = scan(&pack);
            let idx = PackIndex::new(
                resolve_pack(&store, "p", &scanned, &OneBase(base_oid, base))
                    .await
                    .unwrap(),
            );
            let rec = idx.lookup(target_oid).expect("thin delta resolved");
            assert_eq!(rec.base_oid, Some(base_oid));
            assert_eq!(rec.size, target.len() as u64);
        });
    }

    #[test]
    fn gsix_roundtrip() {
        block_on(async {
            let pack = build_pack(&[(ObjType::Blob, b"data".to_vec())]);
            let store = MemStore::new();
            store.put("p", pack.clone()).await.unwrap();
            let scanned = scan(&pack);
            let idx = PackIndex::new(
                resolve_pack(&store, "p", &scanned, &NoExternalBases)
                    .await
                    .unwrap(),
            );
            let bytes = idx.to_bytes();
            let parsed = PackIndex::from_bytes(&bytes).unwrap();
            assert_eq!(parsed.records, idx.records);
            assert!(PackIndex::from_bytes(b"JUNK").is_err());
        });
    }
}

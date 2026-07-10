//! The byte-store abstraction over R2.
//!
//! Everything the server persists that is *bulk data* (packs, pack indexes,
//! file-log segments) goes through this trait. In production it is backed by
//! an R2 bucket; tests and benchmarks use [`MemStore`]. The API is shaped by
//! what R2 actually offers — and, just as importantly, by what it charges for:
//!
//! * **No appends.** R2 objects are immutable once written; "append" is
//!   modelled as multipart upload (stream parts, then complete). Every writer
//!   in this crate is designed around write-once objects.
//! * **Ranged reads.** `get_range` maps to a single Class B operation
//!   regardless of range size, so reading a 300-byte pack entry from a 10 GiB
//!   pack costs the same as reading a 1 KiB object. The object database leans
//!   on this heavily.
//! * **List is Class A** (expensive tier); the design avoids `list` on hot
//!   paths entirely by keeping an explicit pack manifest in the repo state.
//!
//! Futures here are non-`Send` (`async_trait(?Send)`) because the Workers
//! runtime is single-threaded wasm; native tests run them with a local
//! executor.

use async_trait::async_trait;
use std::collections::BTreeMap;
use std::sync::{Arc, Mutex};

/// Errors from the byte store. Kept stringly-typed: the callers can't do
/// anything smarter than report/retry anyway.
#[derive(Debug, Clone)]
pub struct StorageError(pub String);

impl std::fmt::Display for StorageError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "storage error: {}", self.0)
    }
}

impl std::error::Error for StorageError {}

pub type Result<T> = std::result::Result<T, StorageError>;

/// A streaming, write-once upload (R2 multipart upload in production).
///
/// Parts may be buffered internally until they reach the backend's minimum
/// part size; `complete` flushes and atomically publishes the object.
#[async_trait(?Send)]
pub trait Uploader {
    /// Append a chunk to the object being uploaded.
    async fn write(&mut self, chunk: &[u8]) -> Result<()>;
    /// Finish and publish the object. Returns total bytes written.
    async fn complete(self: Box<Self>) -> Result<u64>;
    /// Abort the upload, releasing any stored parts.
    async fn abort(self: Box<Self>) -> Result<()>;
}

/// The byte store. Keys are flat strings; this crate namespaces them as
/// `<repo>/pack/<id>.pack`, `<repo>/pack/<id>.idx`, `<repo>/filelog/<id>`.
#[async_trait(?Send)]
pub trait Store {
    /// Write a whole object at once (small objects: indexes, manifests).
    async fn put(&self, key: &str, data: Vec<u8>) -> Result<()>;

    /// Read a whole object. `None` if absent.
    async fn get(&self, key: &str) -> Result<Option<Vec<u8>>>;

    /// Read `len` bytes starting at `offset`. Short reads happen at EOF.
    /// `None` if the object is absent.
    async fn get_range(&self, key: &str, offset: u64, len: u64) -> Result<Option<Vec<u8>>>;

    /// Object size in bytes, `None` if absent.
    async fn size(&self, key: &str) -> Result<Option<u64>>;

    async fn delete(&self, key: &str) -> Result<()>;

    /// Begin a streaming upload to `key`.
    async fn start_upload(&self, key: &str) -> Result<Box<dyn Uploader>>;
}

// ---------------------------------------------------------------------------
// Block-cached reads
// ---------------------------------------------------------------------------

/// Read granularity for [`BlockReader`]. R2 charges per request, not per
/// byte, and Worker→R2 bandwidth is free, so reading 4 MiB to serve a
/// 300-byte pack entry costs the same as reading 300 bytes — while turning
/// thousands of per-object reads into a handful when access has locality
/// (git packs cluster commits/trees/blobs together, and this crate sorts its
/// bulk operations by pack offset).
pub const BLOCK_SIZE: u64 = 4 * 1024 * 1024;

/// Cached blocks per reader (LRU). 8 × 4 MiB = 32 MiB ceiling per instance.
const BLOCK_CACHE_SLOTS: usize = 8;

/// A block-aligned, LRU-cached ranged reader over one stored object.
///
/// Every bulk read path in this crate (delta resolution, fetch pack copy,
/// repack, odb object reads) goes through one of these instead of issuing raw
/// `get_range` calls: sequential or clustered access patterns then cost
/// O(bytes / 4 MiB) backend requests instead of O(objects).
pub struct BlockReader {
    key: String,
    /// (block index, bytes) in LRU order — most recently used last.
    blocks: std::cell::RefCell<Vec<(u64, std::rc::Rc<Vec<u8>>)>>,
}

impl BlockReader {
    pub fn new(key: &str) -> Self {
        BlockReader {
            key: key.to_string(),
            blocks: std::cell::RefCell::new(Vec::new()),
        }
    }

    async fn block(&self, store: &dyn Store, idx: u64) -> Result<std::rc::Rc<Vec<u8>>> {
        {
            let mut blocks = self.blocks.borrow_mut();
            if let Some(pos) = blocks.iter().position(|(i, _)| *i == idx) {
                let hit = blocks.remove(pos);
                let data = hit.1.clone();
                blocks.push(hit);
                return Ok(data);
            }
        }
        let data = store
            .get_range(&self.key, idx * BLOCK_SIZE, BLOCK_SIZE)
            .await?
            .ok_or_else(|| StorageError(format!("{} vanished", self.key)))?;
        let data = std::rc::Rc::new(data);
        let mut blocks = self.blocks.borrow_mut();
        if blocks.len() >= BLOCK_CACHE_SLOTS {
            blocks.remove(0);
        }
        blocks.push((idx, data.clone()));
        Ok(data)
    }

    /// Read `[start, end)`, served from cached blocks where possible.
    pub async fn read(&self, store: &dyn Store, start: u64, end: u64) -> Result<Vec<u8>> {
        let mut out = Vec::with_capacity((end - start) as usize);
        let mut pos = start;
        while pos < end {
            let idx = pos / BLOCK_SIZE;
            let block = self.block(store, idx).await?;
            let block_start = idx * BLOCK_SIZE;
            let from = (pos - block_start) as usize;
            let to = ((end - block_start) as usize).min(block.len());
            if from >= block.len() {
                return Err(StorageError(format!(
                    "{}: read past end of object ({} of {} block bytes)",
                    self.key,
                    from,
                    block.len()
                )));
            }
            out.extend_from_slice(&block[from..to]);
            pos = block_start + to as u64;
        }
        Ok(out)
    }
}

// ---------------------------------------------------------------------------
// In-memory implementation (tests, benchmarks, native integration server).
// ---------------------------------------------------------------------------

/// In-memory [`Store`]. Cheap to clone (shared interior); thread-safe so the
/// native integration tests can serve requests on one thread while asserting
/// from another.
#[derive(Default, Clone)]
pub struct MemStore {
    objects: Arc<Mutex<BTreeMap<String, Vec<u8>>>>,
    /// Counts of operations, for the cost-model assertions in tests: how many
    /// backend calls would each git operation make in production?
    pub ops: Arc<Mutex<OpCounts>>,
}

/// Operation counters mirroring R2's billing classes.
#[derive(Default, Debug, Clone)]
pub struct OpCounts {
    /// Class A (puts, multipart operations, lists).
    pub class_a: u64,
    /// Class B (gets, ranged gets, head).
    pub class_b: u64,
}

impl MemStore {
    pub fn new() -> Self {
        Self::default()
    }

    /// Snapshot of the op counters.
    pub fn op_counts(&self) -> OpCounts {
        self.ops.lock().unwrap().clone()
    }

    pub fn reset_op_counts(&self) {
        *self.ops.lock().unwrap() = OpCounts::default();
    }

    /// All keys currently stored (test helper; `list` is deliberately not on
    /// the [`Store`] trait so production code can't depend on it).
    pub fn keys(&self) -> Vec<String> {
        self.objects.lock().unwrap().keys().cloned().collect()
    }
}

#[async_trait(?Send)]
impl Store for MemStore {
    async fn put(&self, key: &str, data: Vec<u8>) -> Result<()> {
        let _t = crate::metrics::BackendTimer::start(crate::metrics::Op::R2ClassA);
        self.ops.lock().unwrap().class_a += 1;
        self.objects.lock().unwrap().insert(key.to_string(), data);
        Ok(())
    }

    async fn get(&self, key: &str) -> Result<Option<Vec<u8>>> {
        let _t = crate::metrics::BackendTimer::start(crate::metrics::Op::R2ClassB);
        self.ops.lock().unwrap().class_b += 1;
        Ok(self.objects.lock().unwrap().get(key).cloned())
    }

    async fn get_range(&self, key: &str, offset: u64, len: u64) -> Result<Option<Vec<u8>>> {
        let _t = crate::metrics::BackendTimer::start(crate::metrics::Op::R2ClassB);
        self.ops.lock().unwrap().class_b += 1;
        Ok(self.objects.lock().unwrap().get(key).map(|data| {
            let start = (offset as usize).min(data.len());
            let end = (offset.saturating_add(len) as usize).min(data.len());
            data[start..end].to_vec()
        }))
    }

    async fn size(&self, key: &str) -> Result<Option<u64>> {
        let _t = crate::metrics::BackendTimer::start(crate::metrics::Op::R2ClassB);
        self.ops.lock().unwrap().class_b += 1;
        Ok(self
            .objects
            .lock()
            .unwrap()
            .get(key)
            .map(|d| d.len() as u64))
    }

    async fn delete(&self, key: &str) -> Result<()> {
        let _t = crate::metrics::BackendTimer::start(crate::metrics::Op::R2ClassA);
        self.ops.lock().unwrap().class_a += 1;
        self.objects.lock().unwrap().remove(key);
        Ok(())
    }

    async fn start_upload(&self, key: &str) -> Result<Box<dyn Uploader>> {
        // R2 CreateMultipartUpload is Class A.
        crate::metrics::backend(crate::metrics::Op::R2ClassA, 0.0);
        self.ops.lock().unwrap().class_a += 1;
        Ok(Box::new(MemUploader {
            store: self.clone(),
            key: key.to_string(),
            buf: Vec::new(),
            unparted: 0,
        }))
    }
}

struct MemUploader {
    store: MemStore,
    key: String,
    buf: Vec<u8>,
    /// Bytes not yet attributed to a modelled UploadPart call.
    unparted: usize,
}

#[async_trait(?Send)]
impl Uploader for MemUploader {
    async fn write(&mut self, chunk: &[u8]) -> Result<()> {
        self.buf.extend_from_slice(chunk);
        // Model R2 UploadPart (Class A) per 5 MiB of data, matching the part
        // buffering the production R2 uploader does.
        self.unparted += chunk.len();
        while self.unparted >= 5 * 1024 * 1024 {
            crate::metrics::backend(crate::metrics::Op::R2ClassA, 0.0);
            self.store.ops.lock().unwrap().class_a += 1;
            self.unparted -= 5 * 1024 * 1024;
        }
        Ok(())
    }

    async fn complete(self: Box<Self>) -> Result<u64> {
        crate::metrics::backend(crate::metrics::Op::R2ClassA, 0.0); // CompleteMultipartUpload
        self.store.ops.lock().unwrap().class_a += 1;
        let len = self.buf.len() as u64;
        self.store
            .objects
            .lock()
            .unwrap()
            .insert(self.key.clone(), self.buf);
        Ok(len)
    }

    async fn abort(self: Box<Self>) -> Result<()> {
        crate::metrics::backend(crate::metrics::Op::R2ClassA, 0.0);
        self.store.ops.lock().unwrap().class_a += 1;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use futures::executor::block_on;

    #[test]
    fn mem_store_roundtrip() {
        block_on(async {
            let s = MemStore::new();
            s.put("k", b"hello world".to_vec()).await.unwrap();
            assert_eq!(s.get("k").await.unwrap().unwrap(), b"hello world");
            assert_eq!(s.get_range("k", 6, 5).await.unwrap().unwrap(), b"world");
            assert_eq!(s.get_range("k", 6, 100).await.unwrap().unwrap(), b"world");
            assert_eq!(s.size("k").await.unwrap(), Some(11));
            assert_eq!(s.get("missing").await.unwrap(), None);
            s.delete("k").await.unwrap();
            assert_eq!(s.get("k").await.unwrap(), None);
        });
    }

    #[test]
    fn uploader_streams() {
        block_on(async {
            let s = MemStore::new();
            let mut up = s.start_upload("p").await.unwrap();
            up.write(b"abc").await.unwrap();
            up.write(b"def").await.unwrap();
            let n = up.complete().await.unwrap();
            assert_eq!(n, 6);
            assert_eq!(s.get("p").await.unwrap().unwrap(), b"abcdef");
        });
    }
}

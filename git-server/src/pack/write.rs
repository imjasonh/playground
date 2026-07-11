//! Pack generation.
//!
//! Used by the fetch path (building the response pack) and by repacking. The
//! central trick for both: entries whose payload we already hold compressed in
//! R2 are copied **verbatim** (a ranged read, no inflate/deflate), so serving
//! a clone is mostly `memcpy` from R2 to the socket. Only objects that must
//! change representation (a delta whose base isn't being sent) are
//! re-compressed.
//!
//! The writer accumulates into an internal buffer that the caller drains
//! periodically (`take_chunk`), so a multi-gigabyte pack can be streamed to an
//! R2 multipart upload or an HTTP response without ever being resident.

use crate::object::{ObjType, Oid};
use crate::pack::delta::encode_entry_header;
use crate::pack::TYPE_REF_DELTA;
use flate2::write::ZlibEncoder;
use flate2::Compression;
use sha1::{Digest, Sha1};
use std::io::Write;

/// Streaming pack writer.
pub struct PackWriter {
    buf: Vec<u8>,
    sha: Sha1,
    declared: u32,
    written: u32,
    emitted: u64,
}

impl PackWriter {
    /// Start a pack that will contain exactly `count` entries.
    pub fn new(count: u32) -> Self {
        let mut w = PackWriter {
            buf: Vec::new(),
            sha: Sha1::new(),
            declared: count,
            written: 0,
            emitted: 0,
        };
        let mut header = Vec::with_capacity(12);
        header.extend_from_slice(b"PACK");
        header.extend_from_slice(&2u32.to_be_bytes());
        header.extend_from_slice(&count.to_be_bytes());
        w.emit(&header);
        w
    }

    fn emit(&mut self, bytes: &[u8]) {
        self.sha.update(bytes);
        self.emitted += bytes.len() as u64;
        self.buf.extend_from_slice(bytes);
    }

    /// Total bytes emitted so far (header included, trailer not yet). Used by
    /// repacking to record entry offsets for the new index.
    pub fn emitted(&self) -> u64 {
        self.emitted
    }

    /// Append a full (non-delta) object, compressing `content`.
    pub fn add_full(&mut self, ty: ObjType, content: &[u8]) {
        let header = encode_entry_header(ty.pack_type(), content.len() as u64);
        self.emit(&header);
        let mut enc = ZlibEncoder::new(Vec::new(), Compression::default());
        enc.write_all(content).expect("in-memory deflate");
        let compressed = enc.finish().expect("in-memory deflate");
        self.emit(&compressed);
        self.written += 1;
    }

    /// Append a full object whose zlib stream we already have (verbatim copy
    /// from an existing pack).
    pub fn add_full_precompressed(&mut self, ty: u8, inflated_size: u64, zlib_data: &[u8]) {
        debug_assert!((1..=4).contains(&ty));
        let header = encode_entry_header(ty, inflated_size);
        self.emit(&header);
        self.emit(zlib_data);
        self.written += 1;
    }

    /// Append a REF_DELTA entry with an already-compressed delta payload.
    /// (`OFS_DELTA` entries from source packs are rewritten to `REF_DELTA` so
    /// the copied bytes stay position-independent.)
    pub fn add_ref_delta_precompressed(
        &mut self,
        base: Oid,
        delta_inflated_size: u64,
        zlib_delta: &[u8],
    ) {
        let header = encode_entry_header(TYPE_REF_DELTA, delta_inflated_size);
        self.emit(&header);
        self.emit(&base.0);
        self.emit(zlib_delta);
        self.written += 1;
    }

    // -- Resumable copy API ---------------------------------------------------
    // Copy paths (fetch emission, repack) append an entry's compressed
    // payload in block-sized pieces rather than as one buffer, so a huge
    // object never has to be resident: begin_*, then any number of
    // append_payload calls, then end_entry.

    /// Start a full (non-delta) entry whose payload will follow via
    /// [`Self::append_payload`].
    pub fn begin_full_precompressed(&mut self, ty: u8, inflated_size: u64) {
        debug_assert!((1..=4).contains(&ty));
        let header = encode_entry_header(ty, inflated_size);
        self.emit(&header);
    }

    /// Start a REF_DELTA entry whose compressed delta payload will follow
    /// via [`Self::append_payload`].
    pub fn begin_ref_delta_precompressed(&mut self, base: Oid, delta_inflated_size: u64) {
        let header = encode_entry_header(TYPE_REF_DELTA, delta_inflated_size);
        self.emit(&header);
        self.emit(&base.0);
    }

    /// Append part of the current entry's already-compressed payload.
    pub fn append_payload(&mut self, bytes: &[u8]) {
        self.emit(bytes);
    }

    /// Finish the entry started by a `begin_*` call.
    pub fn end_entry(&mut self) {
        self.written += 1;
    }

    /// Take whatever has accumulated, leaving the writer ready for more. Call
    /// between entries to bound memory when streaming to storage/response.
    pub fn take_chunk(&mut self) -> Vec<u8> {
        std::mem::take(&mut self.buf)
    }

    /// Bytes currently buffered.
    pub fn buffered(&self) -> usize {
        self.buf.len()
    }

    /// Finish the pack: appends the SHA-1 trailer and returns the final chunk
    /// (including anything not yet drained) plus the pack checksum.
    pub fn finish(mut self) -> (Vec<u8>, [u8; 20]) {
        assert_eq!(
            self.written, self.declared,
            "pack declared {} entries but {} were written",
            self.declared, self.written
        );
        let sum: [u8; 20] = self.sha.clone().finalize().into();
        self.buf.extend_from_slice(&sum);
        (std::mem::take(&mut self.buf), sum)
    }
}

/// Deflate `content` (helper for tests and for re-compressed entries).
pub fn deflate(content: &[u8]) -> Vec<u8> {
    let mut enc = ZlibEncoder::new(Vec::new(), Compression::default());
    enc.write_all(content).expect("in-memory deflate");
    enc.finish().expect("in-memory deflate")
}

/// Inflate a complete zlib stream (helper for read paths).
pub fn inflate(data: &[u8], expected_size: u64) -> Result<Vec<u8>, String> {
    let mut out = Vec::with_capacity(expected_size as usize);
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
            flate2::Status::StreamEnd => break,
            _ if produced == 0 && pos >= data.len() => return Err("zlib: truncated stream".into()),
            _ => {}
        }
    }
    if out.len() as u64 != expected_size {
        return Err(format!(
            "inflated size {} != expected {}",
            out.len(),
            expected_size
        ));
    }
    Ok(out)
}

/// Test-support pack builder shared by unit tests and benchmarks across
/// modules. Excluded from the wasm (production Worker) build.
#[cfg(not(target_arch = "wasm32"))]
pub mod test_support {
    use super::*;

    /// Build a complete in-memory pack of full (non-delta) objects.
    pub fn build_pack(objects: &[(ObjType, Vec<u8>)]) -> Vec<u8> {
        let mut w = PackWriter::new(objects.len() as u32);
        for (ty, data) in objects {
            w.add_full(*ty, data);
        }
        w.finish().0
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::object::hash_object;
    use crate::pack::delta::literal_delta;

    #[test]
    fn inflate_roundtrip() {
        let data = vec![3u8; 200_000];
        let z = deflate(&data);
        assert_eq!(inflate(&z, data.len() as u64).unwrap(), data);
    }

    #[test]
    fn writer_produces_scannable_pack_with_ref_delta() {
        let base = b"base content base content".to_vec();
        let target = b"target!".to_vec();
        let base_oid = hash_object(ObjType::Blob, &base);

        let mut w = PackWriter::new(2);
        w.add_full(ObjType::Blob, &base);
        let delta = literal_delta(base.len(), &target);
        w.add_ref_delta_precompressed(base_oid, delta.len() as u64, &deflate(&delta));
        let (pack, _sum) = w.finish();

        let mut scanner = crate::pack::PackScanner::new();
        scanner.feed(&pack).unwrap();
        let scanned = scanner.finish().unwrap();
        assert_eq!(scanned.entries.len(), 2);
        assert_eq!(scanned.entries[0].oid, Some(base_oid));
        assert_eq!(
            scanned.entries[1].base,
            crate::pack::scan::BaseRef::Id(base_oid)
        );
    }

    #[test]
    #[should_panic(expected = "declared 2 entries")]
    fn writer_enforces_count() {
        let w = PackWriter::new(2);
        let _ = w.finish();
    }
}

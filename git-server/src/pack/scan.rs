//! Incremental pack scanner.
//!
//! [`PackScanner`] consumes the raw pack byte stream *as it arrives from the
//! network* (in whatever chunk sizes the transport delivers) and produces, in
//! bounded memory:
//!
//! * the boundaries of every entry (header start, compressed data range);
//! * each entry's stored type, uncompressed size, and delta base reference;
//! * the final object id of every **non-delta** entry (hashed while
//!   inflating — the bytes are never retained);
//! * verification of the pack's trailing SHA-1 checksum.
//!
//! It deliberately does **not** resolve deltas: that needs random access to
//! base objects, which is done after the raw pack has landed in R2 (see
//! [`super::index`]), using ranged reads. This split is what keeps ingest
//! memory ~O(entries), independent of pack size: the scanner holds only a
//! partial-chunk carry buffer and a 32 KiB inflate scratch buffer.

use crate::object::{ObjType, ObjectHasher, Oid};
use crate::pack::delta::{parse_entry_header, parse_ofs_delta_offset};
use crate::pack::{TYPE_OFS_DELTA, TYPE_REF_DELTA};
use flate2::{Decompress, FlushDecompress, Status};
use sha1::{Digest, Sha1};

/// Where a delta entry's base lives.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BaseRef {
    /// Not a delta.
    None,
    /// OFS_DELTA: absolute offset of the base entry earlier in this pack.
    Offset(u64),
    /// REF_DELTA: base identified by oid (may be outside this pack — a
    /// "thin" pack, which pushes commonly use).
    Id(Oid),
}

/// One scanned entry.
#[derive(Debug, Clone)]
pub struct ScanEntry {
    /// Offset of the entry header within the pack.
    pub header_start: u64,
    /// Offset where the zlib-compressed payload begins.
    pub data_start: u64,
    /// Offset one past the end of the compressed payload.
    pub data_end: u64,
    /// Stored (on-disk) type: 1-4 for full objects, 6 OFS_DELTA, 7 REF_DELTA.
    pub stored_type: u8,
    /// Uncompressed payload size (of the delta itself, for delta entries).
    pub inflated_size: u64,
    pub base: BaseRef,
    /// Final object id — known during the scan only for non-delta entries.
    pub oid: Option<Oid>,
}

/// Scan result for a complete, checksum-verified pack.
#[derive(Debug)]
pub struct ScannedPack {
    pub entries: Vec<ScanEntry>,
    /// The pack's trailing SHA-1 (also its identity: packs are content-addressed).
    pub checksum: [u8; 20],
    /// Total pack size in bytes, trailer included.
    pub total_len: u64,
}

enum State {
    Header,
    /// Waiting for the next entry's header (and delta-base preamble).
    EntryHeader,
    /// Inflating the current entry's payload.
    EntryData {
        raw: Decompress,
        hasher: Option<ObjectHasher>,
    },
    Trailer,
    Done,
}

/// Incremental scanner. `feed` chunks, then `finish`.
pub struct PackScanner {
    state: State,
    /// Carry buffer: bytes received but not yet consumed by the state machine.
    carry: Vec<u8>,
    /// Absolute offset of `carry[0]` within the pack stream.
    carry_offset: u64,
    /// Running SHA-1 of consumed bytes (everything before the trailer).
    sha: Sha1,
    declared_count: u32,
    entries: Vec<ScanEntry>,
    /// Scratch space for inflate output.
    scratch: Box<[u8; 32 * 1024]>,
    checksum: Option<[u8; 20]>,
    total_len: u64,
}

impl Default for PackScanner {
    fn default() -> Self {
        Self::new()
    }
}

impl PackScanner {
    pub fn new() -> Self {
        PackScanner {
            state: State::Header,
            carry: Vec::new(),
            carry_offset: 0,
            sha: Sha1::new(),
            declared_count: 0,
            entries: Vec::new(),
            scratch: Box::new([0u8; 32 * 1024]),
            checksum: None,
            total_len: 0,
        }
    }

    /// Number of entries the pack header declared.
    pub fn declared_count(&self) -> u32 {
        self.declared_count
    }

    /// Feed the next chunk of raw pack bytes.
    pub fn feed(&mut self, chunk: &[u8]) -> Result<(), String> {
        self.carry.extend_from_slice(chunk);
        self.total_len += chunk.len() as u64;
        self.process()
    }

    /// Signal end of stream and take the result.
    pub fn finish(mut self) -> Result<ScannedPack, String> {
        self.process()?;
        match self.state {
            State::Done => Ok(ScannedPack {
                entries: self.entries,
                checksum: self.checksum.unwrap(),
                total_len: self.total_len,
            }),
            _ => Err(format!(
                "pack stream truncated (state {:?}, {} of {} entries)",
                match self.state {
                    State::Header => "header",
                    State::EntryHeader => "entry-header",
                    State::EntryData { .. } => "entry-data",
                    State::Trailer => "trailer",
                    State::Done => "done",
                },
                self.entries.len(),
                self.declared_count
            )),
        }
    }

    /// Drive the state machine over whatever is buffered.
    fn process(&mut self) -> Result<(), String> {
        loop {
            match &mut self.state {
                State::Header => {
                    if self.carry.len() < 12 {
                        return Ok(());
                    }
                    if &self.carry[..4] != b"PACK" {
                        return Err("bad pack signature".into());
                    }
                    let version = u32::from_be_bytes(self.carry[4..8].try_into().unwrap());
                    if version != 2 {
                        return Err(format!("unsupported pack version {version}"));
                    }
                    self.declared_count = u32::from_be_bytes(self.carry[8..12].try_into().unwrap());
                    self.consume(12);
                    self.state = if self.declared_count == 0 {
                        State::Trailer
                    } else {
                        State::EntryHeader
                    };
                }
                State::EntryHeader => {
                    // Entry header + worst-case base preamble is < 64 bytes;
                    // wait for enough unless the stream is short.
                    let (ty, size, mut used) = match parse_entry_header(&self.carry) {
                        Some(v) => v,
                        None => return Ok(()), // need more bytes
                    };
                    let header_start = self.carry_offset;
                    let base = match ty {
                        TYPE_OFS_DELTA => match parse_ofs_delta_offset(&self.carry[used..]) {
                            Some((rel, n)) => {
                                used += n;
                                let abs = header_start
                                    .checked_sub(rel)
                                    .ok_or("ofs-delta base before pack start")?;
                                BaseRef::Offset(abs)
                            }
                            None => return Ok(()),
                        },
                        TYPE_REF_DELTA => {
                            if self.carry.len() < used + 20 {
                                return Ok(());
                            }
                            let oid = Oid::from_bytes(&self.carry[used..used + 20]).unwrap();
                            used += 20;
                            BaseRef::Id(oid)
                        }
                        1..=4 => BaseRef::None,
                        _ => return Err(format!("bad pack entry type {ty}")),
                    };
                    self.consume(used);
                    let hasher = ObjType::from_pack_type(ty).map(|t| ObjectHasher::new(t, size));
                    self.entries.push(ScanEntry {
                        header_start,
                        data_start: self.carry_offset,
                        data_end: 0, // filled when inflation completes
                        stored_type: ty,
                        inflated_size: size,
                        base,
                        oid: None,
                    });
                    self.state = State::EntryData {
                        raw: Decompress::new(true),
                        hasher,
                    };
                }
                State::EntryData { .. } => {
                    // Take ownership of the inflater/hasher so we can call
                    // `self.consume` (which needs `&mut self`) mid-entry.
                    let (mut raw, mut hasher) =
                        match std::mem::replace(&mut self.state, State::Done) {
                            State::EntryData { raw, hasher } => (raw, hasher),
                            _ => unreachable!(),
                        };
                    let before_in = raw.total_in();
                    let before_out = raw.total_out();
                    let status = raw
                        .decompress(&self.carry, &mut self.scratch[..], FlushDecompress::None)
                        .map_err(|e| format!("zlib: {e}"))?;
                    let consumed = (raw.total_in() - before_in) as usize;
                    let produced = (raw.total_out() - before_out) as usize;
                    if let Some(h) = hasher.as_mut() {
                        h.update(&self.scratch[..produced]);
                    }
                    let total_out = raw.total_out();
                    let stream_end = status == Status::StreamEnd;
                    self.consume(consumed);
                    if stream_end {
                        let entry = self.entries.last_mut().unwrap();
                        if total_out != entry.inflated_size {
                            return Err(format!(
                                "entry at {} inflated to {} bytes, header said {}",
                                entry.header_start, total_out, entry.inflated_size
                            ));
                        }
                        entry.data_end = self.carry_offset;
                        if let Some(h) = hasher {
                            entry.oid = Some(h.finish());
                        }
                        self.state = if self.entries.len() as u32 == self.declared_count {
                            State::Trailer
                        } else {
                            State::EntryHeader
                        };
                    } else if consumed == 0 && produced == 0 {
                        // Inflater made no progress: it needs more input.
                        self.state = State::EntryData { raw, hasher };
                        return Ok(());
                    } else {
                        // Loop: more buffered input, or the scratch buffer was
                        // full and inflation must continue.
                        self.state = State::EntryData { raw, hasher };
                    }
                }
                State::Trailer => {
                    if self.carry.len() < 20 {
                        return Ok(());
                    }
                    let mut sum = [0u8; 20];
                    sum.copy_from_slice(&self.carry[..20]);
                    let computed: [u8; 20] = self.sha.clone().finalize().into();
                    if sum != computed {
                        return Err("pack checksum mismatch".into());
                    }
                    // Consume without hashing (the trailer isn't covered).
                    self.carry.drain(..20);
                    self.carry_offset += 20;
                    if !self.carry.is_empty() {
                        return Err("trailing garbage after pack".into());
                    }
                    self.checksum = Some(sum);
                    self.state = State::Done;
                }
                State::Done => {
                    if !self.carry.is_empty() {
                        return Err("data after pack end".into());
                    }
                    return Ok(());
                }
            }
        }
    }

    /// Consume `n` bytes from the carry buffer, hashing them.
    fn consume(&mut self, n: usize) {
        self.sha.update(&self.carry[..n]);
        self.carry.drain(..n);
        self.carry_offset += n as u64;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::object::hash_object;
    use crate::pack::write::test_support::build_pack;

    #[test]
    fn scans_simple_pack() {
        // A pack with two full blobs, built by our writer (itself verified
        // against a real `git index-pack` in the integration tests).
        let objs: Vec<(ObjType, Vec<u8>)> = vec![
            (ObjType::Blob, b"hello\n".to_vec()),
            (ObjType::Blob, vec![9u8; 100_000]), // forces multi-chunk inflate
        ];
        let pack = build_pack(&objs);

        // Feed in awkward chunk sizes to exercise the incremental paths.
        let mut scanner = PackScanner::new();
        for chunk in pack.chunks(1023) {
            scanner.feed(chunk).unwrap();
        }
        let scanned = scanner.finish().unwrap();
        assert_eq!(scanned.entries.len(), 2);
        assert_eq!(scanned.total_len, pack.len() as u64);
        for (entry, (ty, data)) in scanned.entries.iter().zip(&objs) {
            assert_eq!(entry.oid, Some(hash_object(*ty, data)));
            assert_eq!(entry.inflated_size, data.len() as u64);
            assert_eq!(entry.base, BaseRef::None);
            assert!(entry.data_end > entry.data_start);
        }
    }

    #[test]
    fn rejects_corrupt_checksum() {
        let mut pack = build_pack(&[(ObjType::Blob, b"x".to_vec())]);
        let n = pack.len();
        pack[n - 1] ^= 0xff;
        let mut scanner = PackScanner::new();
        let err = pack
            .chunks(7)
            .try_for_each(|c| scanner.feed(c))
            .and_then(|_| scanner.finish().map(|_| ()));
        assert!(err.is_err());
    }

    #[test]
    fn rejects_truncation() {
        let pack = build_pack(&[(ObjType::Blob, b"hello".to_vec())]);
        let mut scanner = PackScanner::new();
        scanner.feed(&pack[..pack.len() - 5]).unwrap();
        assert!(scanner.finish().is_err());
    }

    #[test]
    fn rejects_bad_signature() {
        let mut scanner = PackScanner::new();
        assert!(scanner.feed(b"JUNKJUNKJUNKJUNK").is_err());
    }
}

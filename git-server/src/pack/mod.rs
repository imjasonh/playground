//! Packfile machinery (gitformat-pack(5)).
//!
//! Packs are the only object storage this server uses — there are no loose
//! objects. Every push streams its pack into R2 *unmodified* (so the client's
//! compression work is reused, and ingest is O(1) memory), and an index is
//! built alongside it. Reads use ranged R2 reads guided by the index; clones
//! reuse the compressed bytes verbatim wherever possible.
//!
//! * [`scan`] — incremental, chunk-at-a-time scanner that finds entry
//!   boundaries and hashes non-delta objects while the push is still
//!   streaming in.
//! * [`delta`] — the delta encoding: varints, apply, and header parsing
//!   shared by scan/read paths.
//! * [`index`] — resolves delta chains to assign every entry its final object
//!   id and type, and serializes the result as our `GSIX` index format.
//! * [`write`] — pack generation for fetch responses and repacking, with
//!   verbatim reuse of already-compressed entries.

pub mod delta;
pub mod index;
pub mod scan;
pub mod write;

pub use index::{EntryRecord, PackIndex};
pub use scan::{PackScanner, ScanEntry, ScannedPack};

/// Pack entry storage types (the on-disk header values).
pub const TYPE_OFS_DELTA: u8 = 6;
pub const TYPE_REF_DELTA: u8 = 7;

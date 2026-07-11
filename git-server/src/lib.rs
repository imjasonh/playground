//! A git smart-HTTP server for Cloudflare Workers, in Rust.
//!
//! The interesting constraint set: Workers gives us ~128 MiB of memory, small
//! CPU budgets, and no filesystem — but free egress, R2 (object storage with
//! ranged reads and multipart uploads), Durable Objects (single-writer
//! transactional storage), and KV. This crate implements the git smart-HTTP
//! protocol (`info/refs`, `git-upload-pack`, `git-receive-pack`) plus
//! file-content / tree / blame read APIs on top of those primitives, streaming
//! pack data to and from R2 so no operation ever needs to hold a whole pack in
//! memory.
//!
//! Everything except the thin Workers glue is transport- and storage-agnostic:
//!
//! * [`pktline`] — the pkt-line framing used by every git transport.
//! * [`object`] — object ids, types, header encoding, loose-object hashing.
//! * [`pack`] — streaming pack parsing, delta resolution, our pack index
//!   format, and pack generation.
//! * [`odb`] — the object database: oid → object lookup across all packs via
//!   their indexes, with bounded-memory delta-chain resolution.
//! * [`storage`] — the byte-store trait implemented by R2 in production and by
//!   an in-memory store in tests/benchmarks.
//! * [`refs`] — the ref-store trait implemented by a Durable Object in
//!   production (the per-repo linearization point) and in-memory in tests.
//! * [`protocol`] — protocol v2 `ls-refs`/`fetch` (upload-pack) and the v0
//!   receive-pack flow, as pure functions over the traits above.
//! * [`repo`] — ties storage + refs together; owns the pack manifest and the
//!   push-time derived indexes (file-log) that make the read APIs fast.
//! * [`fileapi`] — file content / directory listing at a ref or commit.
//! * [`blame`] — line-level blame built on the push-time file-log index.
//! * [`maintenance`] — budgeted, resumable repacking for scheduled Workers.
//! * [`http`] — the transport-agnostic HTTP request router shared by the
//!   Workers entry point, the native test server, and the benchmarks.
//!
//! See `docs/design.md` for the full architecture, streaming strategy, cost
//! model, and repacking design.

pub mod blame;
pub(crate) mod cache;
pub mod diff;
pub mod fileapi;
pub mod filter;
pub mod http;
pub mod maintenance;
#[cfg(not(target_arch = "wasm32"))]
pub mod memtrack;
pub mod metrics;
pub mod object;
pub mod odb;
pub mod pack;
pub mod pktline;
pub mod protocol;
pub mod refs;
pub mod repo;
pub mod storage;
#[cfg(not(target_arch = "wasm32"))]
pub mod testutil;
pub mod timefmt;
pub mod timing;

#[cfg(target_arch = "wasm32")]
mod worker_entry;

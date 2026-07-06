//! A self-hostable, SSRF-hardened CORS proxy for Cloudflare Workers, in Rust.
//!
//! A CORS proxy fetches a user-supplied URL server-side and returns the
//! response with permissive `Access-Control-*` headers, so browser code can
//! read APIs that don't send CORS headers of their own. The catch is that
//! "fetch any URL the caller names" is textbook Server-Side Request Forgery, so
//! the interesting part of this crate is the hardening, not the proxying.
//!
//! The security-critical logic lives in transport-agnostic modules that are
//! fully unit-tested on the host:
//!
//! * [`url_guard`] — scheme allow-listing and private/loopback/metadata IP and
//!   hostname blocking (the SSRF defense).
//! * [`proxy`] — target extraction, request/response header sanitization, CORS
//!   allow-list decisions, and size limits.
//!
//! The Cloudflare Workers entry point (`fetch`-based delivery with manual,
//! re-validated redirects) is compiled only for `wasm32`.

pub mod error;
pub mod proxy;
pub mod url_guard;

pub use error::GuardError;

#[cfg(target_arch = "wasm32")]
mod worker_entry;

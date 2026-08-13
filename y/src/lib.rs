//! One-user microblog for Cloudflare Workers, in Rust.
//!
//! Auth, HTML rendering, and WebAuthn (ES256) verification are transport-agnostic
//! and unit-tested on the host. The Cloudflare Workers entry point (D1 + R2 +
//! `fetch`) is compiled only for `wasm32`.

pub mod auth;
pub mod html;
pub mod route;
pub mod webauthn;

pub use auth::hash_password;

#[cfg(target_arch = "wasm32")]
mod worker_entry;

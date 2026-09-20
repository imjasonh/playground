//! App Attest handshake and JWT issuer for Cloudflare Workers, in Rust.
//!
//! The iOS Playground app attests a Secure Enclave key once, binding `userId`
//! and `deviceId` to that hardware key. This crate verifies Apple's attestation
//! object, stores the public key, and mints a short-lived HS256 JWT. Later API
//! calls present that JWT; `/v1/whoami` returns the attested identifiers.
//!
//! Verification, JWT minting, and routing live in transport-agnostic modules
//! that native `cargo test` exercises. The Cloudflare Workers entry point
//! (KV + `fetch`) is compiled only for `wasm32`.

pub mod api;
pub mod attest;
pub mod b64;
pub mod certs;
pub mod challenge;
pub mod client_data;
pub mod error;
pub mod jwt;
pub mod store;

pub use api::{handle, ApiConfig, ApiRequest, ApiResponse};
pub use error::Error;

#[cfg(target_arch = "wasm32")]
mod worker_entry;

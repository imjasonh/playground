//! App Attest handshake and assertion verifier for Cloudflare Workers, in Rust.
//!
//! The iOS Playground app attests a Secure Enclave key once, binding `userId`
//! and `deviceId` to that hardware key. Later sensitive calls (`/v1/whoami`)
//! send a fresh `generateAssertion` object. The Worker checks the signature
//! against the stored public key and requires a strictly increasing counter.
//!
//! Verification and routing live in transport-agnostic modules that native
//! `cargo test` exercises. The Cloudflare Workers entry point (KV + `fetch`)
//! is compiled only for `wasm32`.

pub mod api;
pub mod assert;
pub mod attest;
pub mod b64;
pub mod certs;
pub mod challenge;
pub mod client_data;
pub mod error;
pub mod fraud;
pub mod receipt;
pub mod store;

pub use api::{handle, ApiConfig, ApiRequest, ApiResponse};
pub use error::Error;

#[cfg(target_arch = "wasm32")]
mod worker_entry;

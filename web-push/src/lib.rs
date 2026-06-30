//! A Web Push application-server backend for Cloudflare Workers, in Rust.
//!
//! The crate implements the application-server half of the Web Push stack:
//!
//! * **RFC 8030** — the HTTP push request (TTL/Urgency/Topic headers).
//! * **RFC 8188** — `aes128gcm` Encrypted Content-Encoding.
//! * **RFC 8291** — Message Encryption for Web Push (ECDH + HKDF key schedule).
//! * **RFC 8292** — VAPID (a signed ES256 JWT identifying the app server).
//!
//! All cryptography is pure Rust (RustCrypto), so the exact code that runs in
//! the wasm Worker is also exercised by native `cargo test`. The HTTP API
//! ([`api`]) is written against the [`store::SubscriptionStore`] and
//! [`sender::PushSender`] traits, allowing full integration tests with an
//! in-memory store and a recording sender — no deployment required.
//!
//! The Cloudflare Workers entry point (KV-backed storage and `fetch`-based
//! delivery) is compiled only for `wasm32`.

pub mod api;
pub mod b64;
pub mod ece;
pub mod error;
pub mod push;
pub mod sender;
pub mod store;
pub mod subscription;
pub mod vapid;

pub use api::{handle, ApiConfig, ApiRequest, ApiResponse};
pub use error::Error;
pub use push::{endpoint_origin, Urgency, WebPushClient, WebPushMessage, WebPushRequest};
pub use sender::{PushResponse, PushSender, SenderError};
pub use store::{InMemoryStore, StoreError, StoredSubscription, SubscriptionStore};
pub use subscription::{id_for_endpoint, Subscription, SubscriptionKeys};
pub use vapid::VapidKey;

#[cfg(target_arch = "wasm32")]
mod worker_entry;

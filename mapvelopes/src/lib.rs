//! Mapvelopes: envelope PDFs with the sender-to-recipient route as the background.
//!
//! Transport-agnostic modules, unit-tested on the host:
//!
//! * [`address`] — print lines for return and delivery addresses
//! * [`geo`] — encoded polylines
//! * [`maps`] — Google Maps URLs and JSON, plus [`maps::EnvelopeSpec`]
//! * [`render`] — PDF drawing
//! * [`api`] — HTTP classification (form, health, envelope, suggest)
//!
//! The Cloudflare Workers entry point is compiled only for `wasm32`. The
//! native CLI is `cargo run --example envelope`.

pub mod address;
pub mod api;
pub mod error;
pub mod geo;
pub mod maps;
pub mod render;

pub use address::Address;
pub use api::{classify, form_html, health_json, ApiRequest, Classified};
pub use error::Error;
pub use maps::{
    api_key_usable, directions_url, geocode_url, spec_from_google, static_map_url, EnvelopeSize,
    EnvelopeSpec, MapStyle,
};
pub use render::render;

#[cfg(target_arch = "wasm32")]
mod worker_entry;

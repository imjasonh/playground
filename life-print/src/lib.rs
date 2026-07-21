//! Quote life-lab STLs through the Slant 3D print API.
//!
//! The browser already builds binary STL bytes via the `life-stl` wasm module.
//! This Worker:
//!
//! 1. Accepts those bytes on `POST /quote`
//! 2. Parks them briefly in R2 under a random id
//! 3. Asks Slant to slice `https://<this-worker>/files/<id>`
//! 4. Returns the print price and cleans up the blob
//!
//! Business logic lives in transport-agnostic modules so native `cargo test`
//! exercises the same paths the Worker runs. The Cloudflare entry point
//! (`worker_entry`) is compiled only for `wasm32`.

pub mod api;
pub mod slant;
pub mod stl;
pub mod store;

pub use api::{handle, ApiConfig, ApiRequest, ApiResponse};
pub use slant::{MockSlant, SlantClient, SlantError, SliceQuote};
pub use stl::{validate_binary_stl, StlError};
pub use store::{InMemoryStore, StlStore, StoreError};

#[cfg(target_arch = "wasm32")]
mod worker_entry;

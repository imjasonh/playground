//! inkbot — e-ink frame image host + Slack app for Cloudflare Workers.
//!
//! Transport-agnostic modules (tested on the host):
//!
//! * [`panel`] — 800×480 black-and-white PNG validate / transform / encode
//! * [`auth`] — Bearer upload-secret checks + Slack request signatures
//! * [`slack`] — Events API parsing for `@inkbot` image mentions
//! * [`api`] — HTTP routing decisions independent of the Workers runtime
//!
//! The Cloudflare Workers entry point is compiled only for `wasm32`.

pub mod api;
pub mod auth;
pub mod panel;
pub mod slack;

#[cfg(target_arch = "wasm32")]
mod worker_entry;

pub use api::{
    begin_slack_event, finish_app_mention, handle, name_from_filename, parse_slack_command,
    validate_name, ApiRequest, ApiResponse, Catalog, HandlerConfig, ImageStore, SlackBegin,
    SlackCommand, StoredFrame,
};
pub use panel::{PanelError, PanelSpec, DEFAULT_HEIGHT, DEFAULT_WIDTH};

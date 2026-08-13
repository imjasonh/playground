//! One-user microblog for Cloudflare Workers, in Rust.
//!
//! Auth, HTML rendering, and WebAuthn (ES256) verification are transport-agnostic
//! and unit-tested on the host. The Cloudflare Workers entry point (D1 + R2 +
//! `fetch`) is compiled only for `wasm32`.

pub mod auth;
pub mod html;
pub mod route;
pub mod webauthn;

pub use auth::{
    hash_password, make_challenge_cookie, make_session_cookie, verify_challenge_cookie,
    verify_password, verify_session_cookie, CHALLENGE_COOKIE, CHALLENGE_TTL, SESSION_COOKIE,
    SESSION_MAX_AGE,
};
pub use html::{
    extract_youtube_ref, image_ext_for, is_allowed_image_type, is_valid_email, linkify_body,
    utf16_len, Post, PostImage, POST_MAX_CHARS,
};
pub use route::Route;
pub use webauthn::{
    authentication_options, registration_options, verify_authentication, verify_registration,
    AuthenticationResponse, Credential, RegistrationResponse, RpContext,
};

#[cfg(target_arch = "wasm32")]
mod worker_entry;

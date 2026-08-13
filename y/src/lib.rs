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
    challenge_cookie_header, clear_cookie_header, hash_password, make_challenge_cookie,
    make_session_cookie, session_cookie_header, verify_challenge_cookie, verify_password,
    verify_session_cookie, CHALLENGE_COOKIE, CHALLENGE_TTL, SESSION_COOKIE, SESSION_MAX_AGE,
};
pub use html::{
    clip_utf16, extract_youtube_ref, grouped_has_images, image_ext_for, is_allowed_image_type,
    is_valid_email, linkify_body, passkey_label, truncate, utf16_len, validate_post_body, Post,
    PostImage, POST_MAX_CHARS,
};
pub use route::Route;
pub use webauthn::{
    authentication_options, registration_options, verify_authentication, verify_registration,
    AuthenticationResponse, Credential, RegistrationResponse, RpContext,
};

#[cfg(target_arch = "wasm32")]
mod worker_entry;

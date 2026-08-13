//! Request-policy helpers shared by the wasm Worker and host tests.
//!
//! Limits, origin checks, image-key allowlists, and secret validation live
//! here so `cargo test` exercises the same decisions `worker_entry` applies.

use crate::html::PAPERCLIP_KEY;

/// JavaScript `Number.MAX_SAFE_INTEGER` (2^53 − 1). D1 binds integers as
/// IEEE-754, so IDs above this lose precision.
pub const JS_SAFE_INTEGER_MAX: i64 = (1 << 53) - 1;

pub const MIN_SESSION_SECRET_LEN: usize = 16;
pub const MAX_JSON_BODY_BYTES: usize = 16 * 1024;
pub const MAX_IMAGES_PER_POST: usize = 4;
pub const MAX_IMAGE_BYTES: u64 = 5 * 1024 * 1024;
pub const MAX_IMAGE_TOTAL_BYTES: u64 = 12 * 1024 * 1024;

pub const LOGIN_RATE_MAX: i64 = 5;
pub const LOGIN_RATE_WINDOW_SECS: u64 = 15 * 60;
pub const SUBSCRIBE_RATE_MAX: i64 = 20;
pub const SUBSCRIBE_RATE_WINDOW_SECS: u64 = 60 * 60;
pub const OPTIONS_RATE_MAX: i64 = 30;
pub const OPTIONS_RATE_WINDOW_SECS: u64 = 60 * 60;

const CSP: &str = "default-src 'self'; \
base-uri 'none'; \
object-src 'none'; \
frame-ancestors 'none'; \
form-action 'self'; \
script-src 'self' 'unsafe-inline'; \
style-src 'self' 'unsafe-inline' https://fonts.googleapis.com; \
font-src https://fonts.gstatic.com; \
img-src 'self'; \
frame-src https://www.youtube-nocookie.com; \
connect-src 'self'";

/// Headers applied to every response.
pub fn security_headers() -> &'static [(&'static str, &'static str)] {
    &[
        ("X-Content-Type-Options", "nosniff"),
        ("Referrer-Policy", "strict-origin-when-cross-origin"),
        ("X-Frame-Options", "DENY"),
        ("Content-Security-Policy", CSP),
    ]
}

/// Reject missing, empty, or short session HMAC keys (empty keys are forgeable).
pub fn require_session_secret(value: &str) -> Result<(), String> {
    if value.len() < MIN_SESSION_SECRET_LEN {
        return Err("SESSION_SECRET missing or too short".into());
    }
    Ok(())
}

/// Reject missing or malformed `pbkdf2$iters$salt$hash` bootstrap hashes.
pub fn require_password_hash(value: &str) -> Result<(), String> {
    let mut parts = value.split('$');
    if parts.next() != Some("pbkdf2") {
        return Err("ADMIN_PASSWORD_HASH missing or malformed".into());
    }
    let Some(iter_s) = parts.next() else {
        return Err("ADMIN_PASSWORD_HASH missing or malformed".into());
    };
    let Some(salt_hex) = parts.next() else {
        return Err("ADMIN_PASSWORD_HASH missing or malformed".into());
    };
    let Some(hash_hex) = parts.next() else {
        return Err("ADMIN_PASSWORD_HASH missing or malformed".into());
    };
    if parts.next().is_some() {
        return Err("ADMIN_PASSWORD_HASH missing or malformed".into());
    }
    let Ok(iter) = iter_s.parse::<u32>() else {
        return Err("ADMIN_PASSWORD_HASH missing or malformed".into());
    };
    if iter == 0 || salt_hex.is_empty() || hash_hex.is_empty() {
        return Err("ADMIN_PASSWORD_HASH missing or malformed".into());
    }
    if hex::decode(salt_hex).is_err() || hex::decode(hash_hex).is_err() {
        return Err("ADMIN_PASSWORD_HASH missing or malformed".into());
    }
    Ok(())
}

/// Exact `Origin` match, or `Referer` that is the origin or a path under it.
pub fn origin_allowed(expected: &str, origin: Option<&str>, referer: Option<&str>) -> bool {
    if let Some(o) = origin {
        return o == expected;
    }
    if let Some(r) = referer {
        if r == expected {
            return true;
        }
        let prefix = format!("{expected}/");
        return r.starts_with(&prefix);
    }
    false
}

/// Accept the configured site origin or the request's own origin (wrangler dev).
pub fn origin_allowed_any(expected: &[&str], origin: Option<&str>, referer: Option<&str>) -> bool {
    expected.iter().any(|e| origin_allowed(e, origin, referer))
}

/// Paperclip asset, or `{postId}/{ordinal}.{jpg|png|gif|webp|avif}`.
pub fn is_allowed_image_key(key: &str) -> bool {
    if key == PAPERCLIP_KEY {
        return true;
    }
    if key.contains("..") || key.contains('\\') || key.starts_with('/') {
        return false;
    }
    let Some((post, rest)) = key.split_once('/') else {
        return false;
    };
    if parse_js_safe_id(post).is_none() {
        return false;
    }
    let Some((idx, ext)) = rest.split_once('.') else {
        return false;
    };
    if rest.contains('/') {
        return false;
    }
    if idx.is_empty() || !idx.bytes().all(|b| b.is_ascii_digit()) {
        return false;
    }
    matches!(ext, "jpg" | "png" | "gif" | "webp" | "avif")
}

/// `None` when `n` is negative or not a JS-safe integer.
pub fn js_safe_id(n: i64) -> Option<i64> {
    (0..=JS_SAFE_INTEGER_MAX).contains(&n).then_some(n)
}

/// Parse a decimal id that will round-trip through JS/D1 numbers.
pub fn parse_js_safe_id(s: &str) -> Option<i64> {
    if s.is_empty() || !s.bytes().all(|b| b.is_ascii_digit()) {
        return None;
    }
    s.parse().ok().and_then(js_safe_id)
}

pub fn rate_limit_exceeded(recent_count: i64, max: i64) -> bool {
    recent_count >= max
}

pub fn can_delete_passkey(credential_count: i64) -> bool {
    credential_count > 1
}

pub fn challenge_consumed(rows_deleted: i64) -> bool {
    rows_deleted > 0
}

pub fn counter_from_i64(n: i64) -> Result<u32, String> {
    u32::try_from(n).map_err(|_| "credential counter out of range".into())
}

/// Reject a file that would exceed per-file, per-post count, or total bytes.
pub fn check_image_upload(count_so_far: usize, size: u64, total_so_far: u64) -> Result<(), String> {
    if size == 0 {
        return Ok(());
    }
    if count_so_far >= MAX_IMAGES_PER_POST {
        return Err(format!("too many images (max {MAX_IMAGES_PER_POST})"));
    }
    if size > MAX_IMAGE_BYTES {
        return Err("image too large".into());
    }
    if total_so_far.saturating_add(size) > MAX_IMAGE_TOTAL_BYTES {
        return Err("images exceed total size limit".into());
    }
    Ok(())
}

pub fn json_body_too_large(len: usize) -> bool {
    len > MAX_JSON_BODY_BYTES
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn secrets_fail_closed() {
        assert!(require_session_secret("").is_err());
        assert!(require_session_secret("short").is_err());
        assert!(require_session_secret("0123456789abcdef").is_ok());
        assert!(require_password_hash("").is_err());
        assert!(require_password_hash("not-pbkdf2").is_err());
        assert!(require_password_hash("pbkdf2$0$aa$bb").is_err());
        assert!(require_password_hash("pbkdf2$1$zz$00").is_err());
        assert!(require_password_hash("pbkdf2$1$00$00").is_ok());
    }

    #[test]
    fn origin_matches_exact_or_referer_path() {
        let exp = "https://y.imjasonh.workers.dev";
        assert!(origin_allowed(exp, Some(exp), None));
        assert!(!origin_allowed(exp, Some("https://evil.example"), None));
        assert!(!origin_allowed(exp, Some("null"), None));
        assert!(!origin_allowed(exp, None, None));
        assert!(origin_allowed(exp, None, Some(exp)));
        assert!(origin_allowed(
            exp,
            None,
            Some("https://y.imjasonh.workers.dev/admin")
        ));
        assert!(!origin_allowed(
            exp,
            None,
            Some("https://y.imjasonh.workers.dev.evil/")
        ));
        assert!(origin_allowed_any(
            &[exp, "http://127.0.0.1:8787"],
            Some("http://127.0.0.1:8787"),
            None
        ));
        assert!(!origin_allowed_any(
            &[exp],
            Some("http://127.0.0.1:8787"),
            None
        ));
    }

    #[test]
    fn image_keys_are_allowlisted() {
        assert!(is_allowed_image_key(PAPERCLIP_KEY));
        assert!(is_allowed_image_key("9/0.jpg"));
        assert!(is_allowed_image_key("1/3.webp"));
        assert!(!is_allowed_image_key("9/0.svg"));
        assert!(!is_allowed_image_key("../etc/passwd"));
        assert!(!is_allowed_image_key("assets/other.png"));
        assert!(!is_allowed_image_key("9/0.jpg/extra"));
        assert!(!is_allowed_image_key("/9/0.jpg"));
        assert!(!is_allowed_image_key("9/0.JPG"));
    }

    #[test]
    fn js_safe_ids_reject_oversize() {
        assert_eq!(parse_js_safe_id("0"), Some(0));
        assert_eq!(parse_js_safe_id("42"), Some(42));
        assert_eq!(parse_js_safe_id(""), None);
        assert_eq!(parse_js_safe_id("-1"), None);
        assert_eq!(parse_js_safe_id("abc"), None);
        let too_big = format!("{}", JS_SAFE_INTEGER_MAX.saturating_add(1));
        assert_eq!(parse_js_safe_id(&too_big), None);
        assert_eq!(js_safe_id(JS_SAFE_INTEGER_MAX), Some(JS_SAFE_INTEGER_MAX));
        assert_eq!(js_safe_id(-1), None);
    }

    #[test]
    fn upload_limits() {
        assert!(check_image_upload(0, 1, 0).is_ok());
        assert!(check_image_upload(0, 0, 0).is_ok());
        assert!(check_image_upload(MAX_IMAGES_PER_POST, 1, 0).is_err());
        assert!(check_image_upload(0, MAX_IMAGE_BYTES + 1, 0).is_err());
        assert!(check_image_upload(0, 1, MAX_IMAGE_TOTAL_BYTES).is_err());
    }

    #[test]
    fn passkey_and_challenge_helpers() {
        assert!(!can_delete_passkey(0));
        assert!(!can_delete_passkey(1));
        assert!(can_delete_passkey(2));
        assert!(!challenge_consumed(0));
        assert!(challenge_consumed(1));
        assert_eq!(counter_from_i64(0).unwrap(), 0);
        assert_eq!(counter_from_i64(u32::MAX as i64).unwrap(), u32::MAX);
        assert!(counter_from_i64(-1).is_err());
        assert!(counter_from_i64(i64::from(u32::MAX) + 1).is_err());
    }

    #[test]
    fn rate_limit_and_json_size() {
        assert!(!rate_limit_exceeded(4, 5));
        assert!(rate_limit_exceeded(5, 5));
        assert!(!json_body_too_large(MAX_JSON_BODY_BYTES));
        assert!(json_body_too_large(MAX_JSON_BODY_BYTES + 1));
    }

    #[test]
    fn security_headers_include_nosniff_and_csp() {
        let names: Vec<_> = security_headers().iter().map(|(n, _)| *n).collect();
        assert!(names.contains(&"X-Content-Type-Options"));
        assert!(names.contains(&"Content-Security-Policy"));
        let csp = security_headers()
            .iter()
            .find(|(n, _)| *n == "Content-Security-Policy")
            .map(|(_, v)| *v)
            .unwrap();
        assert!(csp.contains("frame-src https://www.youtube-nocookie.com"));
        assert!(csp.contains("object-src 'none'"));
    }
}

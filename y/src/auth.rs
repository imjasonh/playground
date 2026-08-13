//! Password hashing and signed session / WebAuthn-challenge cookies.
//!
//! Password hashes are stored as `pbkdf2$<iterations>$<saltHex>$<hashHex>`
//! (PBKDF2-HMAC-SHA256, 32-byte output) so existing `ADMIN_PASSWORD_HASH`
//! secrets keep working.
//!
//! Sessions are a signed cookie `<expiresUnix>.<hmacHex>` — no DB row. Change
//! `SESSION_SECRET` to revoke every session. Challenges are
//! `<expires>.<challenge>.<hmac>` and last [`CHALLENGE_TTL`] seconds.

use hmac::{Hmac, Mac};
use pbkdf2::pbkdf2_hmac_array;
use rand_core::{OsRng, RngCore};
use sha2::Sha256;

type HmacSha256 = Hmac<Sha256>;

pub const SESSION_COOKIE: &str = "y_session";
pub const CHALLENGE_COOKIE: &str = "y_challenge";
pub const SESSION_TTL_SECONDS: u64 = 60 * 60 * 24 * 30;
pub const CHALLENGE_TTL: u64 = 5 * 60;
const PBKDF2_ITER: u32 = 100_000;

/// Constant-time equality; length mismatch is false.
fn bytes_equal(a: &[u8], b: &[u8]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut diff = 0u8;
    for (x, y) in a.iter().zip(b.iter()) {
        diff |= x ^ y;
    }
    diff == 0
}

fn pbkdf2(password: &str, salt: &[u8], iterations: u32) -> [u8; 32] {
    pbkdf2_hmac_array::<Sha256, 32>(password.as_bytes(), salt, iterations)
}

/// Hash a password into the stored `pbkdf2$…` form (100k iterations, 16-byte salt).
pub fn hash_password(password: &str) -> String {
    let mut salt = [0u8; 16];
    OsRng.fill_bytes(&mut salt);
    let hash = pbkdf2(password, &salt, PBKDF2_ITER);
    format!(
        "pbkdf2${}${}${}",
        PBKDF2_ITER,
        hex::encode(salt),
        hex::encode(hash)
    )
}

/// Verify `password` against a `pbkdf2$iters$salt$hash` string.
pub fn verify_password(password: &str, stored: &str) -> bool {
    let mut parts = stored.split('$');
    let Some("pbkdf2") = parts.next() else {
        return false;
    };
    let Some(iter_s) = parts.next() else {
        return false;
    };
    let Some(salt_hex) = parts.next() else {
        return false;
    };
    let Some(hash_hex) = parts.next() else {
        return false;
    };
    if parts.next().is_some() {
        return false;
    }
    let Ok(iter) = iter_s.parse::<u32>() else {
        return false;
    };
    if iter == 0 {
        return false;
    }
    let Ok(salt) = hex::decode(salt_hex) else {
        return false;
    };
    let Ok(expected) = hex::decode(hash_hex) else {
        return false;
    };
    let got = pbkdf2(password, &salt, iter);
    bytes_equal(&got, &expected)
}

fn hmac_hex(secret: &str, message: &str) -> String {
    let mut mac =
        HmacSha256::new_from_slice(secret.as_bytes()).expect("HMAC-SHA256 accepts any key length");
    mac.update(message.as_bytes());
    hex::encode(mac.finalize().into_bytes())
}

/// Build a session cookie value valid for [`SESSION_TTL_SECONDS`] from `now`.
pub fn make_session_cookie(secret: &str, now_seconds: u64) -> String {
    let expires = now_seconds + SESSION_TTL_SECONDS;
    let payload = expires.to_string();
    let sig = hmac_hex(secret, &payload);
    format!("{payload}.{sig}")
}

/// True when `raw` is a session cookie that has not expired at `now_seconds`.
pub fn verify_session_cookie(secret: &str, raw: Option<&str>, now_seconds: u64) -> bool {
    let Some(raw) = raw else {
        return false;
    };
    let Some((payload, sig)) = raw.split_once('.') else {
        return false;
    };
    if payload.contains('.') {
        return false;
    }
    let expected = hmac_hex(secret, payload);
    let Ok(got) = hex::decode(sig) else {
        return false;
    };
    let Ok(want) = hex::decode(&expected) else {
        return false;
    };
    if !bytes_equal(&got, &want) {
        return false;
    }
    let Ok(expires) = payload.parse::<u64>() else {
        return false;
    };
    now_seconds < expires
}

/// Signed cookie carrying a WebAuthn challenge across the options/verify roundtrip.
pub fn make_challenge_cookie(secret: &str, challenge: &str, now_seconds: u64) -> String {
    let expires = now_seconds + CHALLENGE_TTL;
    let payload = format!("{expires}.{challenge}");
    let sig = hmac_hex(secret, &payload);
    format!("{payload}.{sig}")
}

/// Return the challenge string if the cookie is valid and unexpired.
pub fn verify_challenge_cookie(
    secret: &str,
    raw: Option<&str>,
    now_seconds: u64,
) -> Option<String> {
    let raw = raw?;
    let last_dot = raw.rfind('.')?;
    let payload = &raw[..last_dot];
    let sig = &raw[last_dot + 1..];
    let expected = hmac_hex(secret, payload);
    let got = hex::decode(sig).ok()?;
    let want = hex::decode(&expected).ok()?;
    if !bytes_equal(&got, &want) {
        return None;
    }
    let first_dot = payload.find('.')?;
    let expires: u64 = payload[..first_dot].parse().ok()?;
    if now_seconds >= expires {
        return None;
    }
    Some(payload[first_dot + 1..].to_string())
}

/// 32 random bytes as unpadded base64url — a WebAuthn challenge.
pub fn random_challenge() -> String {
    let mut bytes = [0u8; 32];
    OsRng.fill_bytes(&mut bytes);
    crate::webauthn::b64url_encode(&bytes)
}

/// `Set-Cookie` value for a new session (Path=/, 30-day Max-Age).
pub fn session_cookie_header(value: &str) -> String {
    format!(
        "{SESSION_COOKIE}={value}; Path=/; HttpOnly; Secure; SameSite=Strict; Max-Age={SESSION_TTL_SECONDS}"
    )
}

/// `Set-Cookie` value for a WebAuthn challenge (Path=/admin, 5-minute Max-Age).
pub fn challenge_cookie_header(value: &str) -> String {
    format!(
        "{CHALLENGE_COOKIE}={value}; Path=/admin; HttpOnly; Secure; SameSite=Strict; Max-Age={CHALLENGE_TTL}"
    )
}

/// `Set-Cookie` value that expires a cookie immediately.
pub fn clear_cookie_header(name: &str, path: &str) -> String {
    format!("{name}=; Path={path}; HttpOnly; Secure; SameSite=Strict; Max-Age=0")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn password_roundtrip() {
        let stored = hash_password("hunter2");
        assert!(verify_password("hunter2", &stored));
        assert!(!verify_password("hunter3", &stored));
        assert!(!verify_password("hunter2", "not-a-hash"));
    }

    #[test]
    fn password_parses_known_vector() {
        // 1 iteration, salt = 00..0f, password = "pw" — checks the wire format.
        let salt: [u8; 16] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15];
        let hash = pbkdf2("pw", &salt, 1);
        let stored = format!("pbkdf2$1${}${}", hex::encode(salt), hex::encode(hash));
        assert!(verify_password("pw", &stored));
        assert!(!verify_password("pw", &stored.replace("$1$", "$2$")));
    }

    #[test]
    fn session_cookie_roundtrip() {
        let secret = "s3cret";
        let cookie = make_session_cookie(secret, 1_000);
        assert!(verify_session_cookie(secret, Some(&cookie), 1_000));
        assert!(verify_session_cookie(
            secret,
            Some(&cookie),
            1_000 + SESSION_TTL_SECONDS - 1
        ));
        assert!(!verify_session_cookie(
            secret,
            Some(&cookie),
            1_000 + SESSION_TTL_SECONDS
        ));
        assert!(!verify_session_cookie("other", Some(&cookie), 1_000));
        assert!(!verify_session_cookie(secret, None, 1_000));
        assert!(!verify_session_cookie(secret, Some("nope"), 1_000));
    }

    #[test]
    fn challenge_cookie_roundtrip() {
        let secret = "s3cret";
        let cookie = make_challenge_cookie(secret, "abc.def", 50);
        assert_eq!(
            verify_challenge_cookie(secret, Some(&cookie), 50).as_deref(),
            Some("abc.def")
        );
        assert_eq!(
            verify_challenge_cookie(secret, Some(&cookie), 50 + CHALLENGE_TTL),
            None
        );
        assert_eq!(verify_challenge_cookie("nope", Some(&cookie), 50), None);
    }

    #[test]
    fn cookie_header_flags() {
        let session = session_cookie_header("abc");
        assert_eq!(
            session,
            "y_session=abc; Path=/; HttpOnly; Secure; SameSite=Strict; Max-Age=2592000"
        );
        let challenge = challenge_cookie_header("ch");
        assert_eq!(
            challenge,
            "y_challenge=ch; Path=/admin; HttpOnly; Secure; SameSite=Strict; Max-Age=300"
        );
        assert_eq!(
            clear_cookie_header(SESSION_COOKIE, "/"),
            "y_session=; Path=/; HttpOnly; Secure; SameSite=Strict; Max-Age=0"
        );
        assert_eq!(
            clear_cookie_header(CHALLENGE_COOKIE, "/admin"),
            "y_challenge=; Path=/admin; HttpOnly; Secure; SameSite=Strict; Max-Age=0"
        );
    }
}

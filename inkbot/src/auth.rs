//! Shared-secret Bearer auth and Slack request signing.

use hmac::{Hmac, Mac};
use sha2::Sha256;
use std::time::{SystemTime, UNIX_EPOCH};

type HmacSha256 = Hmac<Sha256>;

/// Maximum age of a Slack signing timestamp we will accept (5 minutes).
pub const SLACK_MAX_SKEW_SECS: i64 = 60 * 5;

/// Extract the token from an `Authorization: Bearer <token>` header value.
pub fn bearer_token(authorization: Option<&str>) -> Option<&str> {
    let value = authorization?.trim();
    let rest = value
        .strip_prefix("Bearer ")
        .or_else(|| value.strip_prefix("bearer "))?;
    let token = rest.trim();
    if token.is_empty() {
        None
    } else {
        Some(token)
    }
}

/// Constant-time equality for secrets of equal length; length mismatch → false.
pub fn secrets_equal(a: &str, b: &str) -> bool {
    let a = a.as_bytes();
    let b = b.as_bytes();
    if a.len() != b.len() {
        return false;
    }
    let mut diff = 0u8;
    for (x, y) in a.iter().zip(b.iter()) {
        diff |= x ^ y;
    }
    diff == 0
}

/// True when the Authorization header carries the expected upload secret.
pub fn authorize_upload(authorization: Option<&str>, expected: &str) -> bool {
    match bearer_token(authorization) {
        Some(token) => secrets_equal(token, expected),
        None => false,
    }
}

/// Verify a Slack Events API request signature.
///
/// Slack signs `v0:{timestamp}:{body}` with HMAC-SHA256 using the signing
/// secret and sends `X-Slack-Signature: v0=<hex>`.
pub fn verify_slack_signature(
    signing_secret: &str,
    timestamp: &str,
    body: &[u8],
    signature: &str,
    now_unix: i64,
) -> bool {
    let Ok(ts) = timestamp.parse::<i64>() else {
        return false;
    };
    if (now_unix - ts).abs() > SLACK_MAX_SKEW_SECS {
        return false;
    }

    let Some(sig_hex) = signature.strip_prefix("v0=") else {
        return false;
    };
    let Ok(expected_bytes) = hex::decode(sig_hex) else {
        return false;
    };

    let mut mac = match HmacSha256::new_from_slice(signing_secret.as_bytes()) {
        Ok(m) => m,
        Err(_) => return false,
    };
    mac.update(b"v0:");
    mac.update(timestamp.as_bytes());
    mac.update(b":");
    mac.update(body);
    let computed = mac.finalize().into_bytes();

    if computed.len() != expected_bytes.len() {
        return false;
    }
    let mut diff = 0u8;
    for (x, y) in computed.iter().zip(expected_bytes.iter()) {
        diff |= x ^ y;
    }
    diff == 0
}

/// Current unix time; falls back to 0 only if the system clock is before epoch.
pub fn now_unix() -> i64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_secs() as i64)
        .unwrap_or(0)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bearer_parsing() {
        assert_eq!(bearer_token(Some("Bearer abc")), Some("abc"));
        assert_eq!(bearer_token(Some("bearer  xyz  ")), Some("xyz"));
        assert_eq!(bearer_token(Some("Basic abc")), None);
        assert_eq!(bearer_token(None), None);
    }

    #[test]
    fn authorize_upload_matches() {
        assert!(authorize_upload(Some("Bearer s3cret"), "s3cret"));
        assert!(!authorize_upload(Some("Bearer nope"), "s3cret"));
        assert!(!authorize_upload(None, "s3cret"));
    }

    #[test]
    fn slack_signature_round_trip() {
        let secret = "8f742231b10e8888abcd852abaddeadbeef";
        let ts = "1531420618";
        let body = b"token=xyzz&team_id=T1DC2JH3J&team_domain=testteamnow&channel_id=C1DC2JH3J&channel_name=testchannel&user_id=U1DC2JH3J&user_name=testuser&command=%2Fweather&text=94070&response_url=https%3A%2F%2Fhooks.slack.com%2Fcommands%2FT1DC2JH3J%2F1234567890%2Fsecret&trigger_id=13345224609.738474920.8088930838d88f008e0";
        // Signature from Slack's documenting example for this body+secret+ts.
        let mut mac = HmacSha256::new_from_slice(secret.as_bytes()).unwrap();
        mac.update(b"v0:");
        mac.update(ts.as_bytes());
        mac.update(b":");
        mac.update(body);
        let sig = format!("v0={}", hex::encode(mac.finalize().into_bytes()));

        assert!(verify_slack_signature(secret, ts, body, &sig, 1531420618));
        assert!(!verify_slack_signature(
            secret,
            ts,
            body,
            &sig,
            1531420618 + SLACK_MAX_SKEW_SECS + 1
        ));
        assert!(!verify_slack_signature(
            secret, ts, body, "v0=00", 1531420618
        ));
    }
}

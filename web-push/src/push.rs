//! Assembling an HTTP push request (RFC 8030) with an aes128gcm-encrypted body
//! (RFC 8291) and a VAPID `Authorization` header (RFC 8292).

use p256::SecretKey;
use rand_core::{OsRng, RngCore};

use crate::ece::{self, DEFAULT_RECORD_SIZE};
use crate::error::Error;
use crate::subscription::Subscription;
use crate::vapid::VapidKey;

/// VAPID JWTs must expire within 24h of issuance (RFC 8292 §2); cap to that.
const MAX_JWT_TTL_SECS: u64 = 24 * 60 * 60;

/// Message urgency (RFC 8030 §5.3).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Urgency {
    VeryLow,
    Low,
    Normal,
    High,
}

impl Urgency {
    /// The header token for this urgency.
    pub fn as_str(self) -> &'static str {
        match self {
            Urgency::VeryLow => "very-low",
            Urgency::Low => "low",
            Urgency::Normal => "normal",
            Urgency::High => "high",
        }
    }

    /// Parse an urgency token, returning `None` for unknown values.
    pub fn parse(s: &str) -> Option<Self> {
        match s {
            "very-low" => Some(Urgency::VeryLow),
            "low" => Some(Urgency::Low),
            "normal" => Some(Urgency::Normal),
            "high" => Some(Urgency::High),
            _ => None,
        }
    }
}

/// A message to deliver to a single subscription.
#[derive(Clone, Debug)]
pub struct WebPushMessage {
    /// The plaintext payload (typically JSON the service worker will read).
    pub payload: Vec<u8>,
    /// How long (seconds) the push service should retain the message.
    pub ttl: u32,
    /// Optional delivery urgency.
    pub urgency: Option<Urgency>,
    /// Optional topic; a newer message with the same topic replaces an older
    /// undelivered one.
    pub topic: Option<String>,
}

impl WebPushMessage {
    /// A message with the given payload and TTL and no urgency/topic.
    pub fn new(payload: impl Into<Vec<u8>>, ttl: u32) -> Self {
        Self {
            payload: payload.into(),
            ttl,
            urgency: None,
            topic: None,
        }
    }
}

/// A fully assembled HTTP request, ready for a transport to send.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WebPushRequest {
    /// The push service endpoint (request URL).
    pub endpoint: String,
    /// HTTP request headers.
    pub headers: Vec<(String, String)>,
    /// The encrypted request body.
    pub body: Vec<u8>,
}

impl WebPushRequest {
    /// Look up a header value (case-insensitive).
    pub fn header(&self, name: &str) -> Option<&str> {
        self.headers
            .iter()
            .find(|(k, _)| k.eq_ignore_ascii_case(name))
            .map(|(_, v)| v.as_str())
    }
}

/// Builds encrypted, VAPID-authenticated push requests for one application
/// server identity (one VAPID key + contact subject).
#[derive(Clone)]
pub struct WebPushClient {
    vapid: VapidKey,
    subject: String,
    jwt_ttl_secs: u64,
    record_size: u32,
}

impl WebPushClient {
    /// Create a client. `subject` is the VAPID contact (a `mailto:` or `https:`
    /// URI). `jwt_ttl_secs` is clamped to the 24h VAPID maximum.
    pub fn new(vapid: VapidKey, subject: impl Into<String>, jwt_ttl_secs: u64) -> Self {
        Self {
            vapid,
            subject: subject.into(),
            jwt_ttl_secs: jwt_ttl_secs.clamp(1, MAX_JWT_TTL_SECS),
            record_size: DEFAULT_RECORD_SIZE,
        }
    }

    /// The VAPID public key (base64url) browsers subscribe with.
    pub fn vapid_public_key(&self) -> String {
        self.vapid.public_key_base64url()
    }

    /// Build a request, generating a random ephemeral key and salt.
    pub fn build_request(
        &self,
        subscription: &Subscription,
        message: &WebPushMessage,
        now_unix: u64,
    ) -> Result<WebPushRequest, Error> {
        let as_secret = SecretKey::random(&mut OsRng);
        let mut salt = [0u8; 16];
        OsRng.fill_bytes(&mut salt);
        self.build_request_with(subscription, message, now_unix, &as_secret, &salt)
    }

    /// Build a request with caller-supplied ephemeral key and salt (used by
    /// deterministic tests).
    pub fn build_request_with(
        &self,
        subscription: &Subscription,
        message: &WebPushMessage,
        now_unix: u64,
        as_secret: &SecretKey,
        salt: &[u8; 16],
    ) -> Result<WebPushRequest, Error> {
        let receiver = subscription.receiver_keys()?;
        let body = ece::encrypt(
            &receiver,
            as_secret,
            salt,
            &message.payload,
            self.record_size,
        )?;

        let audience = endpoint_origin(&subscription.endpoint)?;
        let exp = now_unix + self.jwt_ttl_secs;
        let authorization = self
            .vapid
            .authorization_header(&audience, &self.subject, exp);

        let mut headers = vec![
            ("TTL".to_string(), message.ttl.to_string()),
            ("Content-Encoding".to_string(), "aes128gcm".to_string()),
            (
                "Content-Type".to_string(),
                "application/octet-stream".to_string(),
            ),
            ("Authorization".to_string(), authorization),
        ];
        if let Some(urgency) = message.urgency {
            headers.push(("Urgency".to_string(), urgency.as_str().to_string()));
        }
        if let Some(topic) = &message.topic {
            headers.push(("Topic".to_string(), topic.clone()));
        }

        Ok(WebPushRequest {
            endpoint: subscription.endpoint.clone(),
            headers,
            body,
        })
    }
}

/// Extract the origin (`scheme://authority`) of an endpoint URL for use as the
/// VAPID JWT audience.
pub fn endpoint_origin(endpoint: &str) -> Result<String, Error> {
    let scheme_end = endpoint
        .find("://")
        .ok_or_else(|| Error::BadRequest("endpoint missing scheme".into()))?;
    let scheme = &endpoint[..scheme_end];
    let rest = &endpoint[scheme_end + 3..];
    let authority_end = rest.find('/').unwrap_or(rest.len());
    let authority = &rest[..authority_end];
    if scheme.is_empty() || authority.is_empty() {
        return Err(Error::BadRequest("endpoint missing host".into()));
    }
    Ok(format!("{scheme}://{authority}"))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn origin_strips_path_and_query() {
        assert_eq!(
            endpoint_origin("https://fcm.googleapis.com/fcm/send/abc?x=1").unwrap(),
            "https://fcm.googleapis.com"
        );
        assert_eq!(
            endpoint_origin("https://updates.push.services.mozilla.com:443/wpush/v2/xyz").unwrap(),
            "https://updates.push.services.mozilla.com:443"
        );
    }

    #[test]
    fn origin_requires_scheme_and_host() {
        assert!(endpoint_origin("not-a-url").is_err());
        assert!(endpoint_origin("https:///path").is_err());
    }
}

//! Parsing and validation of the W3C `PushSubscription` object that a browser
//! produces from `pushManager.subscribe(...)`.

use p256::PublicKey;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::b64;
use crate::ece::ReceiverKeys;
use crate::error::Error;

/// The subscription keys block: `p256dh` and `auth`, both base64url.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SubscriptionKeys {
    /// The user agent's P-256 public key (uncompressed point), base64url.
    pub p256dh: String,
    /// The 16-byte authentication secret, base64url.
    pub auth: String,
}

/// A `PushSubscription` as serialized by the browser Push API.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Subscription {
    /// The push service endpoint URL the message is delivered to.
    pub endpoint: String,
    /// Optional expiration time; retained for round-tripping, otherwise unused.
    #[serde(default, rename = "expirationTime")]
    pub expiration_time: Option<serde_json::Value>,
    /// The subscription's cryptographic keys.
    pub keys: SubscriptionKeys,
}

impl Subscription {
    /// Parse a subscription from JSON bytes.
    pub fn parse(json: &[u8]) -> Result<Self, Error> {
        serde_json::from_slice(json)
            .map_err(|e| Error::BadRequest(format!("invalid subscription JSON: {e}")))
    }

    /// Decode and validate the receiver keys (`p256dh` + `auth`).
    pub fn receiver_keys(&self) -> Result<ReceiverKeys, Error> {
        let p256dh_bytes = b64::decode(&self.keys.p256dh)?;
        let p256dh =
            PublicKey::from_sec1_bytes(&p256dh_bytes).map_err(|_| Error::InvalidPublicKey)?;
        let auth =
            b64::decode_array::<16>(&self.keys.auth).map_err(|_| Error::InvalidAuthSecret)?;
        Ok(ReceiverKeys { p256dh, auth })
    }

    /// Validate the endpoint and keys without retaining the decoded keys.
    pub fn validate(&self) -> Result<(), Error> {
        if !(self.endpoint.starts_with("https://") || self.endpoint.starts_with("http://")) {
            return Err(Error::BadRequest(
                "subscription endpoint must be an http(s) URL".into(),
            ));
        }
        self.receiver_keys().map(|_| ())
    }

    /// A stable identifier derived from the endpoint (SHA-256, base64url). Using
    /// the endpoint makes re-subscribing with the same endpoint idempotent.
    pub fn id(&self) -> String {
        id_for_endpoint(&self.endpoint)
    }
}

/// Compute the stable subscription id for an endpoint URL.
pub fn id_for_endpoint(endpoint: &str) -> String {
    b64::encode(Sha256::digest(endpoint.as_bytes()))
}

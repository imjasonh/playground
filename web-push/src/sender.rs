//! Transport abstraction for delivering a [`WebPushRequest`] to a push service.
//!
//! Production uses the Workers `fetch` API; tests use a recording sender. The
//! API logic only depends on this trait, so delivery can be exercised without a
//! network.

use async_trait::async_trait;
use std::fmt;

use crate::push::WebPushRequest;

/// The push service's response to a delivery attempt.
#[derive(Debug, Clone)]
pub struct PushResponse {
    /// HTTP status code returned by the push service.
    pub status: u16,
    /// Optional response body (often an error description).
    pub body: Option<String>,
}

impl PushResponse {
    /// Whether the push service accepted the message (2xx).
    pub fn is_success(&self) -> bool {
        (200..300).contains(&self.status)
    }

    /// Whether the subscription is no longer valid and should be pruned
    /// (`404 Not Found` or `410 Gone`, per RFC 8030 §7.3).
    pub fn is_gone(&self) -> bool {
        self.status == 404 || self.status == 410
    }
}

/// A transport error (e.g. the network request itself failed).
#[derive(Debug, Clone)]
pub struct SenderError(pub String);

impl fmt::Display for SenderError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "push send error: {}", self.0)
    }
}

impl std::error::Error for SenderError {}

/// Sends an assembled push request to the push service.
#[async_trait(?Send)]
pub trait PushSender {
    /// Deliver the request and return the push service's response.
    async fn send(&self, request: &WebPushRequest) -> Result<PushResponse, SenderError>;
}

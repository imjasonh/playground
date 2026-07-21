//! Slant 3D API client surface used by the quote flow.
//!
//! Only the slicer endpoint is wired today (`POST /api/slicer`). Ordering /
//! checkout is deliberately out of scope — see the README for why payment
//! cannot be "users pay Slant at cost" through the raw Order API alone.

use std::sync::Mutex;

use async_trait::async_trait;
use serde::Deserialize;

/// A successful slice / print-price quote.
#[derive(Debug, Clone, PartialEq)]
pub struct SliceQuote {
    pub price: f64,
    pub message: Option<String>,
}

/// Why talking to Slant failed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SlantError {
    /// HTTP or transport failure before a JSON body was parsed.
    Transport(String),
    /// Slant returned a non-success status.
    Status { status: u16, body: String },
    /// Response JSON was missing / unusable.
    BadResponse(String),
}

impl std::fmt::Display for SlantError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SlantError::Transport(m) => write!(f, "slant transport: {m}"),
            SlantError::Status { status, body } => {
                write!(f, "slant HTTP {status}: {body}")
            }
            SlantError::BadResponse(m) => write!(f, "slant bad response: {m}"),
        }
    }
}

impl std::error::Error for SlantError {}

/// Slice a publicly reachable STL URL and return Slant's print price.
///
/// Futures are `?Send` because the Workers runtime is single-threaded.
#[async_trait(?Send)]
pub trait SlantClient {
    async fn slice(&self, file_url: &str) -> Result<SliceQuote, SlantError>;
}

/// Parse the JSON body of a successful `/api/slicer` response.
pub fn parse_slice_response(body: &[u8]) -> Result<SliceQuote, SlantError> {
    #[derive(Deserialize)]
    struct Data {
        price: Option<f64>,
    }
    #[derive(Deserialize)]
    struct Envelope {
        message: Option<String>,
        data: Option<Data>,
    }

    let env: Envelope = serde_json::from_slice(body)
        .map_err(|e| SlantError::BadResponse(format!("invalid JSON: {e}")))?;
    let price = env
        .data
        .and_then(|d| d.price)
        .ok_or_else(|| SlantError::BadResponse("missing data.price".into()))?;
    if !price.is_finite() || price < 0.0 {
        return Err(SlantError::BadResponse(format!(
            "nonsensical price {price}"
        )));
    }
    Ok(SliceQuote {
        price,
        message: env.message,
    })
}

/// Build the JSON body Slant expects for a slice request.
///
/// Field name is `fileURL` (camel with capital URL) — that is what their
/// working examples and OpenAPI clients send. The published JSON Schema
/// sometimes spells it `fileUrl`; Slant accepts `fileURL`.
pub fn slice_request_body(file_url: &str) -> Vec<u8> {
    serde_json::to_vec(&serde_json::json!({ "fileURL": file_url })).expect("json")
}

/// Test double that records requested URLs and returns a fixed quote (or error).
pub struct MockSlant {
    pub price: f64,
    pub fail: Mutex<Option<SlantError>>,
    pub seen_urls: Mutex<Vec<String>>,
}

impl MockSlant {
    pub fn with_price(price: f64) -> Self {
        Self {
            price,
            fail: Mutex::new(None),
            seen_urls: Mutex::new(Vec::new()),
        }
    }

    pub fn fail_next(&self, err: SlantError) {
        *self.fail.lock().expect("lock") = Some(err);
    }

    pub fn urls(&self) -> Vec<String> {
        self.seen_urls.lock().expect("lock").clone()
    }
}

#[async_trait(?Send)]
impl SlantClient for MockSlant {
    async fn slice(&self, file_url: &str) -> Result<SliceQuote, SlantError> {
        self.seen_urls
            .lock()
            .expect("lock")
            .push(file_url.to_string());
        if let Some(err) = self.fail.lock().expect("lock").take() {
            return Err(err);
        }
        Ok(SliceQuote {
            price: self.price,
            message: Some("Slicing successful".into()),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_wiki_sample() {
        let body = br#"{"message":"Slicing successful","data":{"price":5.2}}"#;
        let q = parse_slice_response(body).unwrap();
        assert!((q.price - 5.2).abs() < f64::EPSILON);
        assert_eq!(q.message.as_deref(), Some("Slicing successful"));
    }

    #[test]
    fn rejects_missing_price() {
        let err = parse_slice_response(br#"{"message":"ok","data":{}}"#).unwrap_err();
        assert!(matches!(err, SlantError::BadResponse(_)));
    }

    #[test]
    fn request_body_uses_file_url_capitalization() {
        let body = String::from_utf8(slice_request_body("https://example/a.stl")).unwrap();
        assert!(body.contains("\"fileURL\""));
        assert!(body.contains("https://example/a.stl"));
    }
}

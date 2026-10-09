//! Recording a command's HTTP requests through a local proxy, and checking
//! them again before a cached result is replayed.
//!
//! A GET or HEAD request is an input like a file: before replaying, memo
//! sends it again, with `If-None-Match` and `If-Modified-Since` when the
//! server gave validators. A `304 Not Modified` or an identical response
//! means it's unchanged. Requests with other methods can't be checked
//! without repeating their side effects.

mod client;
mod proxy;
mod wire;

pub use proxy::Proxy;

use client::Url;
use rustls::ClientConfig;
use serde::{Deserialize, Serialize};
use std::io;
use std::sync::Arc;
use wire::Head;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Exchange {
    pub method: String,
    pub url: String,
    /// Request header fields, sent again when checking. They can include
    /// credentials, which is why the cache is readable only by its owner.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub headers: Vec<(String, String)>,
    pub status: u16,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub etag: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub last_modified: Option<String>,
    /// The BLAKE3 hash of the response body, or for HEAD of the header
    /// fields that describe the body.
    pub body: String,
}

/// Hashes the parts of a HEAD response that describe the resource.
fn head_digest(head: &Head, status: u16) -> String {
    let mut h = blake3::Hasher::new();
    h.update(&status.to_le_bytes());
    for name in ["content-length", "content-type", "etag", "last-modified"] {
        h.update(head.get(name).unwrap_or("").as_bytes());
        h.update(b"\n");
    }
    h.finalize().to_hex().to_string()
}

/// Sends recorded requests again to see whether their responses changed.
pub struct Checker {
    tls: Arc<ClientConfig>,
}

impl Checker {
    pub fn new() -> io::Result<Checker> {
        Ok(Checker {
            tls: client::tls_config()?,
        })
    }

    /// Returns what changed about `ex`, or `None` if the server's answer is
    /// the same.
    pub fn check(&self, ex: &Exchange) -> Option<String> {
        let what = format!("{} {}", ex.method, ex.url);
        self.compare(ex)
            .unwrap_or_else(|e| Some(format!("couldn't check it ({e})")))
            .map(|d| format!("{what}: {d}"))
    }

    fn compare(&self, ex: &Exchange) -> io::Result<Option<String>> {
        let url = Url::parse(&ex.url)?;
        let mut headers = ex.headers.clone();
        let has = |h: &[(String, String)], name: &str| {
            h.iter().any(|(k, _)| k.eq_ignore_ascii_case(name))
        };
        let mut conditional = false;
        if let Some(etag) = &ex.etag {
            if !has(&headers, "if-none-match") {
                headers.push(("If-None-Match".into(), etag.clone()));
                conditional = true;
            }
        }
        if let Some(lm) = &ex.last_modified {
            if !has(&headers, "if-modified-since") {
                headers.push(("If-Modified-Since".into(), lm.clone()));
                conditional = true;
            }
        }
        let mut resp = client::send(&self.tls, &ex.method, &url, &headers, None)?;
        if conditional && resp.status == 304 {
            return Ok(None);
        }
        let framing = wire::response_framing(&ex.method, resp.status, &resp.head)?;
        let body = wire::copy_body(&mut resp.body, &mut io::sink(), framing)?;
        let body = if ex.method == "HEAD" {
            head_digest(&resp.head, resp.status)
        } else {
            body
        };
        Ok(if resp.status != ex.status {
            Some(format!(
                "status changed from {} to {}",
                ex.status, resp.status
            ))
        } else if body != ex.body {
            Some("response changed".into())
        } else {
            None
        })
    }
}

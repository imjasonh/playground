//! Recording a command's HTTP requests through a local proxy, and checking
//! them again before a cached result is replayed.
//!
//! A GET or HEAD request is an input like a file. Before replaying a GET
//! whose response had an `ETag` or `Last-Modified`, memo sends a HEAD with
//! `If-None-Match` and `If-Modified-Since`, so neither answer downloads the
//! body: a `304 Not Modified`, or a 2xx response with the same validators,
//! means unchanged; different validators mean changed. memo compares the
//! validators in a 2xx response itself, because some servers ignore
//! conditional headers. When HEAD can't settle it, memo repeats the GET and
//! compares the response with the recorded hash. Requests with other methods
//! can't be checked without repeating their side effects.

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

/// Compares entity tags the way `If-None-Match` does (RFC 9110, section
/// 8.8.3.2): equal opaque tags match even if one or both are weak. `If-Match`
/// compares strongly, so a weak tag never matches it, even unchanged.
fn etag_matches(a: &str, b: &str) -> bool {
    let opaque = |t: &str| t.trim().trim_start_matches("W/").to_string();
    opaque(a) == opaque(b)
}

const CONDITIONALS: &[&str] = &[
    "if-match",
    "if-none-match",
    "if-modified-since",
    "if-unmodified-since",
    "if-range",
];

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
        let verdict = match Url::parse(&ex.url) {
            Ok(url) => match self.by_head(ex, &url) {
                Some(v) => Ok(v),
                None => self.by_request(ex, &url),
            },
            Err(e) => Err(e),
        };
        verdict
            .unwrap_or_else(|e| Some(format!("couldn't check it ({e})")))
            .map(|d| format!("{what}: {d}"))
    }

    /// Asks with HEAD whether the resource still has the recorded `ETag` or
    /// `Last-Modified`. Returns `None` if that can't settle it: nothing was
    /// recorded to compare, or the server refused HEAD or sent no
    /// validators back.
    fn by_head(&self, ex: &Exchange, url: &Url) -> Option<Option<String>> {
        let recorded_ok = (200..300).contains(&ex.status) || ex.status == 304;
        if ex.method != "GET" || !recorded_ok || (ex.etag.is_none() && ex.last_modified.is_none()) {
            return None;
        }
        // Only memo's own validators, so a 304 means "same as recorded" even
        // if the command sent conditional headers of its own.
        let mut headers: Vec<(String, String)> = ex
            .headers
            .iter()
            .filter(|(k, _)| !CONDITIONALS.iter().any(|c| k.eq_ignore_ascii_case(c)))
            .cloned()
            .collect();
        if let Some(etag) = &ex.etag {
            headers.push(("If-None-Match".into(), etag.clone()));
        }
        if let Some(lm) = &ex.last_modified {
            headers.push(("If-Modified-Since".into(), lm.clone()));
        }
        let resp = client::send(&self.tls, "HEAD", url, &headers, None).ok()?;
        if resp.status == 304 {
            return Some(None);
        }
        if !(200..300).contains(&resp.status) {
            return None;
        }
        if let (Some(want), Some(got)) = (&ex.etag, resp.head.get("etag")) {
            return Some(
                (!etag_matches(want, got)).then(|| format!("ETag changed from {want} to {got}")),
            );
        }
        if let (Some(want), Some(got)) = (&ex.last_modified, resp.head.get("last-modified")) {
            return Some(
                (want != got).then(|| format!("Last-Modified changed from {want} to {got}")),
            );
        }
        None
    }

    /// Repeats the request and compares the status and the hash of the
    /// response with the recording.
    fn by_request(&self, ex: &Exchange, url: &Url) -> io::Result<Option<String>> {
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
        let mut resp = client::send(&self.tls, &ex.method, url, &headers, None)?;
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn entity_tags_compare_weakly() {
        assert!(etag_matches("\"a\"", "\"a\""));
        assert!(etag_matches("W/\"a\"", "\"a\""));
        assert!(etag_matches("W/\"a\"", " W/\"a\" "));
        assert!(!etag_matches("\"a\"", "\"b\""));
        assert!(!etag_matches("W/\"a\"", "W/\"b\""));
    }
}

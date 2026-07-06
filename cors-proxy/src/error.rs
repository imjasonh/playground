//! Crate-wide error type for URL validation and request handling.

use std::fmt;

/// Reasons the proxy refuses to fetch a target URL. Each variant maps to an
/// HTTP status via [`GuardError::status`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GuardError {
    /// No `url` parameter (or path target) was supplied.
    MissingTarget,
    /// The target could not be parsed as an absolute URL.
    InvalidUrl,
    /// The URL scheme is not `http` or `https`.
    UnsupportedScheme(String),
    /// The URL has no host component.
    MissingHost,
    /// The host is a name on the denylist (loopback, metadata, `.local`, ...).
    BlockedHost(String),
    /// The host resolves to a literal private/reserved/loopback IP address.
    BlockedIp(String),
    /// The redirect chain exceeded the allowed number of hops.
    TooManyRedirects,
}

impl GuardError {
    /// The HTTP status code to return for this error.
    pub fn status(&self) -> u16 {
        match self {
            GuardError::MissingTarget | GuardError::InvalidUrl => 400,
            GuardError::UnsupportedScheme(_) | GuardError::MissingHost => 400,
            // A blocked target is a client asking us to do something we won't:
            // 403 makes the refusal explicit and distinguishes it from a 400.
            GuardError::BlockedHost(_) | GuardError::BlockedIp(_) => 403,
            GuardError::TooManyRedirects => 502,
        }
    }
}

impl fmt::Display for GuardError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            GuardError::MissingTarget => {
                write!(f, "missing target: pass ?url=<encoded absolute URL>")
            }
            GuardError::InvalidUrl => write!(f, "target is not a valid absolute URL"),
            GuardError::UnsupportedScheme(s) => {
                write!(
                    f,
                    "unsupported scheme '{s}': only http and https are allowed"
                )
            }
            GuardError::MissingHost => write!(f, "target URL has no host"),
            GuardError::BlockedHost(h) => write!(f, "host '{h}' is not allowed"),
            GuardError::BlockedIp(ip) => {
                write!(f, "address '{ip}' is private, loopback, or reserved")
            }
            GuardError::TooManyRedirects => write!(f, "too many redirects"),
        }
    }
}

impl std::error::Error for GuardError {}

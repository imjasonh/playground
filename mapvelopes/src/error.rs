//! Recoverable failures when planning a route or writing a PDF.

use std::fmt;

/// A mapvelopes failure the HTTP layer can turn into a status code.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Error {
    /// `from` or `to` was empty after trimming.
    EmptyAddress(&'static str),
    /// The request was malformed (missing fields, bad JSON, unknown path).
    BadRequest(String),
    /// Geocoding, directions, or static-map JSON/bytes were unusable.
    Maps(String),
    /// The PDF writer hit an invariant it cannot represent.
    Pdf(String),
}

impl Error {
    /// HTTP status that matches this error.
    pub fn status(&self) -> u16 {
        match self {
            Error::EmptyAddress(_) | Error::BadRequest(_) => 400,
            Error::Maps(_) => 502,
            Error::Pdf(_) => 500,
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::EmptyAddress(which) => write!(f, "{which} address is empty"),
            Error::BadRequest(msg) | Error::Maps(msg) | Error::Pdf(msg) => f.write_str(msg),
        }
    }
}

impl std::error::Error for Error {}

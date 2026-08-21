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
    /// `GOOGLE_MAPS_API_KEY` is missing, empty, or a known placeholder.
    Unavailable(String),
    /// The PDF writer hit an invariant it cannot represent.
    Pdf(String),
}

impl Error {
    /// HTTP status that matches this error.
    pub fn status(&self) -> u16 {
        match self {
            Error::EmptyAddress(_) | Error::BadRequest(_) => 400,
            Error::Maps(_) => 502,
            Error::Unavailable(_) => 503,
            Error::Pdf(_) => 500,
        }
    }

    /// Worker or CLI has no usable Google Maps key.
    pub fn missing_maps_key() -> Self {
        Error::Unavailable("GOOGLE_MAPS_API_KEY is missing or unusable".into())
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::EmptyAddress(which) => write!(f, "{which} address is empty"),
            Error::BadRequest(msg)
            | Error::Maps(msg)
            | Error::Unavailable(msg)
            | Error::Pdf(msg) => f.write_str(msg),
        }
    }
}

impl std::error::Error for Error {}

//! Crate-wide error type.

use std::fmt;

/// Errors produced while verifying App Attest material or minting tokens.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Error {
    /// Invalid base64 or base64url input.
    Base64,
    /// A request body could not be parsed.
    BadRequest(String),
    /// The attestation object is not valid CBOR or is the wrong format.
    Attestation(&'static str),
    /// Certificate chain or nonce extension check failed.
    Certificate(&'static str),
    /// Bound client JSON, challenge, or App ID did not match.
    Binding(&'static str),
    /// A stored challenge is missing or already used.
    Challenge,
    /// JWT mint or verify failed.
    Token(&'static str),
    /// Storage backend failed.
    Store(String),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::Base64 => write!(f, "invalid base64 input"),
            Error::BadRequest(why) => write!(f, "{why}"),
            Error::Attestation(why) => write!(f, "attestation: {why}"),
            Error::Certificate(why) => write!(f, "certificate: {why}"),
            Error::Binding(why) => write!(f, "{why}"),
            Error::Challenge => write!(f, "challenge missing, used, or expired"),
            Error::Token(why) => write!(f, "token: {why}"),
            Error::Store(why) => write!(f, "store: {why}"),
        }
    }
}

impl std::error::Error for Error {}

impl Error {
    /// HTTP status that matches this error.
    pub fn status(&self) -> u16 {
        match self {
            Error::Store(_) => 500,
            Error::Token("missing") | Error::Token("expired") | Error::Token("invalid") => 401,
            _ => 400,
        }
    }
}

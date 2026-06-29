//! Crate-wide error type.

use std::fmt;

/// Errors produced while parsing subscriptions or building encrypted Web Push
/// requests.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Error {
    /// Invalid base64/base64url input.
    Base64,
    /// A public key was not a valid uncompressed P-256 point.
    InvalidPublicKey,
    /// The `auth` secret was not exactly 16 bytes.
    InvalidAuthSecret,
    /// A private key was not a valid P-256 scalar.
    InvalidPrivateKey,
    /// The plaintext does not fit in a single aes128gcm record of `record_size`.
    PayloadTooLarge { max: usize },
    /// AEAD encryption/decryption failed.
    Crypto(&'static str),
    /// The encrypted body was malformed (bad header or padding).
    MalformedBody(&'static str),
    /// A request body could not be parsed.
    BadRequest(String),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::Base64 => write!(f, "invalid base64url input"),
            Error::InvalidPublicKey => write!(f, "invalid P-256 public key"),
            Error::InvalidAuthSecret => write!(f, "auth secret must be 16 bytes"),
            Error::InvalidPrivateKey => write!(f, "invalid P-256 private key"),
            Error::PayloadTooLarge { max } => {
                write!(f, "payload too large (max {max} plaintext bytes)")
            }
            Error::Crypto(why) => write!(f, "cryptographic operation failed: {why}"),
            Error::MalformedBody(why) => write!(f, "malformed encrypted body: {why}"),
            Error::BadRequest(why) => write!(f, "bad request: {why}"),
        }
    }
}

impl std::error::Error for Error {}

//! The Sigstore keys and identity policy a slot check uses.
//!
//! [`crate::trusted_root::extract`] builds a [`TrustRoot`] from Sigstore's
//! TUF-verified `trusted_root.json` and the compiled-in policy.

/// The most Fulcio intermediates a trust root can list.
pub const MAX_FULCIO: usize = 8;
/// The most log keys a trust root can list.
pub const MAX_LOGS: usize = 16;
/// The most TSA signers a trust root can list.
pub const MAX_TSAS: usize = 8;
/// The length of an uncompressed SEC1 P-384 point.
pub const P384_POINT_LEN: usize = 97;

/// An inclusive validity window, in seconds since the Unix epoch.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Window {
    /// The first second the key is valid.
    pub not_before: u64,
    /// The last second the key is valid.
    pub not_after: u64,
}

impl Window {
    /// Reports whether `t` is inside the window.
    pub fn contains(&self, t: u64) -> bool {
        self.not_before <= t && t <= self.not_after
    }
}

/// A Fulcio intermediate that may sign leaf certificates.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FulcioIntermediate<'a> {
    /// The intermediate's subject name, DER.
    pub subject: &'a [u8],
    /// The intermediate's P-384 public key, uncompressed SEC1.
    pub public_key: &'a [u8; P384_POINT_LEN],
    /// When the intermediate may be used.
    pub window: Window,
}

/// A transparency log key that may sign checkpoints.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LogKey<'a> {
    /// The log's origin string.
    pub origin: &'a [u8],
    /// The log's Ed25519 public key.
    pub public_key: &'a [u8; 32],
    /// When the key may be used.
    pub window: Window,
}

/// A timestamp authority signer.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TsaSigner<'a> {
    /// The DER `SignerIdentifier` a token's `SignerInfo` must contain.
    pub signer_id: &'a [u8],
    /// The TSA's P-384 public key, uncompressed SEC1.
    pub public_key: &'a [u8; P384_POINT_LEN],
    /// When the signer may be used.
    pub window: Window,
}

/// The values the Fulcio leaf's extensions must equal exactly.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Policy<'a> {
    /// Issuer (V2), `1.3.6.1.4.1.57264.1.8`.
    pub issuer: &'a [u8],
    /// Build Signer URI, `1.3.6.1.4.1.57264.1.9`.
    pub build_signer_uri: &'a [u8],
    /// Source Repository Identifier, `1.3.6.1.4.1.57264.1.15`.
    pub repository_id: &'a [u8],
    /// Source Repository Owner Identifier, `1.3.6.1.4.1.57264.1.17`.
    pub owner_id: &'a [u8],
    /// Build Trigger, `1.3.6.1.4.1.57264.1.20`.
    pub trigger: &'a [u8],
}

/// The keys a slot's Sigstore bundle must chain to, and the identity
/// policy its Fulcio leaf must match.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TrustRoot<'a> {
    fulcio: [Option<FulcioIntermediate<'a>>; MAX_FULCIO],
    logs: [Option<LogKey<'a>>; MAX_LOGS],
    tsas: [Option<TsaSigner<'a>>; MAX_TSAS],
    /// The identity policy.
    pub policy: Policy<'a>,
}

impl<'a> TrustRoot<'a> {
    /// A trust root with these keys and policy. Entries after the first
    /// `None` in each list are ignored.
    pub fn from_parts(
        fulcio: [Option<FulcioIntermediate<'a>>; MAX_FULCIO],
        logs: [Option<LogKey<'a>>; MAX_LOGS],
        tsas: [Option<TsaSigner<'a>>; MAX_TSAS],
        policy: Policy<'a>,
    ) -> Self {
        TrustRoot {
            fulcio,
            logs,
            tsas,
            policy,
        }
    }

    /// The Fulcio intermediates the trust root lists.
    pub fn fulcio(&self) -> impl Iterator<Item = &FulcioIntermediate<'a>> {
        self.fulcio.iter().map_while(Option::as_ref)
    }

    /// The log keys the trust root lists.
    pub fn logs(&self) -> impl Iterator<Item = &LogKey<'a>> {
        self.logs.iter().map_while(Option::as_ref)
    }

    /// The TSA signers the trust root lists.
    pub fn tsas(&self) -> impl Iterator<Item = &TsaSigner<'a>> {
        self.tsas.iter().map_while(Option::as_ref)
    }
}

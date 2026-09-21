//! Apple App Attest fraud metric: DeviceCheck JWT + receipt refresh.
//!
//! A compromised genuine device can attest many keys and sign assertions for
//! patched copies running elsewhere. Apple's metric is an approximate 30-day
//! count of unique attested keys for this app on that device. This crate
//! refreshes the receipt when a [`FraudMetricClient`] is configured, stores the
//! number, and can reject `whoami` when `MAX_RISK_METRIC` is set.

use std::cell::RefCell;

use async_trait::async_trait;
use p256::ecdsa::signature::Signer;
use p256::ecdsa::{Signature, SigningKey};
use p256::pkcs8::DecodePrivateKey;

use crate::b64;
use crate::error::Error;
use crate::receipt::{self, ReceiptFields};
use crate::store::DeviceRecord;

const JWT_TTL_SECONDS: u64 = 20 * 60;

/// Result of asking Apple (or a test double) to refresh a receipt.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FraudRefreshResult {
    /// No DeviceCheck key is configured.
    Unconfigured,
    /// Apple returned 304; try again after field 19.
    NotModified,
    /// New receipt with a risk metric.
    Updated(RefreshedReceipt),
    /// Network or Apple error. The API request continues without a new metric.
    Failed(String),
}

/// A server-refreshed receipt (`RECEIPT` type) plus the parsed metric.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RefreshedReceipt {
    pub receipt: Vec<u8>,
    pub risk_metric: u32,
    pub not_before_unix: Option<u64>,
}

/// Server-to-server receipt refresh. Production talks to Apple; tests stub it.
#[async_trait(?Send)]
pub trait FraudMetricClient {
    async fn refresh(&self, receipt: &[u8], development: bool, now_unix: u64)
        -> FraudRefreshResult;
}

/// No Apple call. Used when DeviceCheck secrets are absent.
pub struct NoopFraudClient;

#[async_trait(?Send)]
impl FraudMetricClient for NoopFraudClient {
    async fn refresh(
        &self,
        _receipt: &[u8],
        _development: bool,
        _now_unix: u64,
    ) -> FraudRefreshResult {
        FraudRefreshResult::Unconfigured
    }
}

/// Test double that returns scripted refresh results in order.
pub struct ScriptedFraudClient {
    results: RefCell<Vec<FraudRefreshResult>>,
}

impl ScriptedFraudClient {
    pub fn new(results: Vec<FraudRefreshResult>) -> Self {
        Self {
            results: RefCell::new(results),
        }
    }
}

#[async_trait(?Send)]
impl FraudMetricClient for ScriptedFraudClient {
    async fn refresh(
        &self,
        _receipt: &[u8],
        _development: bool,
        _now_unix: u64,
    ) -> FraudRefreshResult {
        let mut q = self.results.borrow_mut();
        if q.is_empty() {
            FraudRefreshResult::Unconfigured
        } else {
            q.remove(0)
        }
    }
}

/// Production and development App Attest data hosts.
pub fn apple_data_url(development: bool) -> &'static str {
    if development {
        "https://data-development.appattest.apple.com/v1/attestationData"
    } else {
        "https://data.appattest.apple.com/v1/attestationData"
    }
}

/// ES256 DeviceCheck JWT (`iss` = Team ID, `kid` = key id).
pub fn device_check_jwt(
    team_id: &str,
    key_id: &str,
    private_key_pem: &str,
    now_unix: u64,
) -> Result<String, Error> {
    if team_id.is_empty() || key_id.is_empty() || private_key_pem.trim().is_empty() {
        return Err(Error::Token("DeviceCheck key missing"));
    }
    let signing = SigningKey::from_pkcs8_pem(private_key_pem.trim())
        .map_err(|_| Error::Token("DeviceCheck key"))?;
    let header = serde_json::json!({
        "alg": "ES256",
        "kid": key_id,
        "typ": "JWT",
    });
    let header_b64 = b64::encode_url(
        serde_json::to_vec(&header).map_err(|_| Error::Token("DeviceCheck header"))?,
    );
    let payload = serde_json::json!({
        "iss": team_id,
        "iat": now_unix,
        "exp": now_unix.saturating_add(JWT_TTL_SECONDS),
    });
    let payload_b64 = b64::encode_url(
        serde_json::to_vec(&payload).map_err(|_| Error::Token("DeviceCheck claims"))?,
    );
    let signing_input = format!("{header_b64}.{payload_b64}");
    let sig: Signature = signing.sign(signing_input.as_bytes());
    Ok(format!(
        "{signing_input}.{}",
        b64::encode_url(sig.to_bytes())
    ))
}

/// Team ID is the segment of `APP_ID` before the first `.`.
pub fn team_id_from_app_id(app_id: &str) -> Option<&str> {
    let (team, rest) = app_id.split_once('.')?;
    if team.is_empty() || rest.is_empty() {
        None
    } else {
        Some(team)
    }
}

/// Apply a refresh result onto a stored device row. Returns whether the row changed.
pub fn apply_refresh(record: &mut DeviceRecord, result: &FraudRefreshResult) -> bool {
    match result {
        FraudRefreshResult::Updated(updated) => {
            record.receipt = Some(b64::encode_std(&updated.receipt));
            record.risk_metric = Some(updated.risk_metric);
            record.risk_metric_not_before = updated.not_before_unix;
            true
        }
        _ => false,
    }
}

/// Skip Apple when the stored not-before is still in the future.
pub fn ready_to_refresh(record: &DeviceRecord, now_unix: u64) -> bool {
    match record.risk_metric_not_before {
        Some(not_before) => now_unix >= not_before,
        None => record.receipt.is_some(),
    }
}

/// Parse a refreshed receipt body (raw PKCS #7 bytes).
pub fn parse_refreshed(bytes: &[u8]) -> Result<RefreshedReceipt, Error> {
    let fields: ReceiptFields = receipt::parse(bytes)?;
    let risk_metric = fields
        .risk_metric
        .ok_or(Error::Attestation("receipt missing risk metric"))?;
    Ok(RefreshedReceipt {
        receipt: bytes.to_vec(),
        risk_metric,
        not_before_unix: fields.not_before_unix,
    })
}

/// Reject when a configured maximum is set and the stored metric is above it.
pub fn check_max_metric(record: &DeviceRecord, max: Option<u32>) -> Result<(), Error> {
    let Some(max) = max else {
        return Ok(());
    };
    let Some(metric) = record.risk_metric else {
        return Ok(());
    };
    if metric > max {
        return Err(Error::Risk(format!(
            "risk metric {metric} exceeds maximum {max}"
        )));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use p256::ecdsa::signature::Verifier;
    use p256::pkcs8::EncodePrivateKey;
    use rand_core::OsRng;

    #[test]
    fn team_id_splits_app_id() {
        assert_eq!(
            team_id_from_app_id("W5LPA2QM2W.io.github.imjasonh.playground"),
            Some("W5LPA2QM2W")
        );
        assert_eq!(team_id_from_app_id("noperiod"), None);
    }

    #[test]
    fn device_check_jwt_verifies() {
        let signing = SigningKey::random(&mut OsRng);
        let pem = signing
            .to_pkcs8_pem(p256::pkcs8::LineEnding::LF)
            .unwrap()
            .to_string();
        let token = device_check_jwt("TEAMID", "KEYID", &pem, 1_700_000_000).unwrap();
        let mut parts = token.split('.');
        let header = parts.next().unwrap();
        let payload = parts.next().unwrap();
        let sig = parts.next().unwrap();
        let header_json = String::from_utf8(b64::decode(header).unwrap()).unwrap();
        assert!(header_json.contains("KEYID"));
        let payload_json = String::from_utf8(b64::decode(payload).unwrap()).unwrap();
        assert!(payload_json.contains("TEAMID"));
        let sig_bytes = b64::decode(sig).unwrap();
        let signature = Signature::from_slice(&sig_bytes).unwrap();
        signing
            .verifying_key()
            .verify(format!("{header}.{payload}").as_bytes(), &signature)
            .unwrap();
    }

    #[test]
    fn max_metric_fail_open_without_value() {
        let record = DeviceRecord {
            key_id: "k".into(),
            user_id: "u".into(),
            device_id: "d".into(),
            public_key: String::new(),
            counter: 0,
            created_at: 1,
            unattested: false,
            receipt: None,
            risk_metric: None,
            risk_metric_not_before: None,
            development: false,
        };
        check_max_metric(&record, Some(2)).unwrap();
    }
}

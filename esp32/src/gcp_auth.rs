//! Google Cloud auth shared between cloud_log + metrics.
//!
//! One service account, one private key, one cached access token,
//! used by both the logging POST path (`cloud_log`) and the
//! monitoring POST path (`metrics`). The JWT requests both
//! `logging.write` and `monitoring.write` scopes so a single
//! exchange covers both APIs.
//!
//! Also exposes the HTTPS / time / base64url helpers both modules
//! need so we don't duplicate them.

use anyhow::{anyhow, bail, Context, Result};
use base64::Engine;
use embedded_svc::http::client::Client;
use embedded_svc::io::Write as _;
use esp_idf_svc::http::client::{
    Configuration as HttpConfig, EspHttpConnection, FollowRedirectsPolicy,
};
use esp_idf_svc::http::Method;
use rsa::pkcs1v15::SigningKey;
use rsa::pkcs8::DecodePrivateKey;
use rsa::signature::{SignatureEncoding, Signer};
use rsa::RsaPrivateKey;
use serde::{Deserialize, Serialize};
use std::sync::Mutex;
use std::time::Duration;

use crate::cloud_log::GcpConfig;
pub use crate::net_coord::{
    new_short_https_lock, ota_download_in_progress, OtaDownloadGuard, ShortHttpsLock,
};

/// `module_path!()` for this module — used by cloud_log to filter out
/// our own tracing events without hardcoding the crate name.
pub const TARGET: &str = module_path!();

/// A bearer token cached until ~5 min before expiry.
struct CachedToken {
    token: String,
    expires_at_unix: u64,
}

impl CachedToken {
    fn fresh(&self) -> bool {
        match now_unix_secs() {
            // Refresh 5 minutes before expiry to avoid races.
            Some(now) => now + 300 < self.expires_at_unix,
            None => false,
        }
    }
}

/// Mints + caches a single OAuth2 access token shareable across
/// cloud_log and metrics. Multi-scope so one token covers both APIs.
pub struct TokenProvider {
    cfg: GcpConfig,
    signing_key: SigningKey<rsa::sha2::Sha256>,
    cache: Mutex<Option<CachedToken>>,
}

impl TokenProvider {
    pub fn new(cfg: GcpConfig) -> Result<Self> {
        let signing_key = parse_signing_key(&cfg.sa_key_pem)?;
        Ok(Self {
            cfg,
            signing_key,
            cache: Mutex::new(None),
        })
    }

    /// Returns a Bearer token. Mints a new one (RSA sign + HTTPS POST
    /// to oauth2.googleapis.com) only when the cached one is missing
    /// or near expiry. Holding the lock through mint serialises
    /// concurrent callers, but mint runs ~hourly so the contention
    /// window is fine.
    pub fn get_or_refresh(&self) -> Result<String> {
        let mut g = self
            .cache
            .lock()
            .map_err(|_| anyhow!("token cache mutex poisoned"))?;
        if let Some(t) = g.as_ref() {
            if t.fresh() {
                return Ok(t.token.clone());
            }
        }
        let new =
            mint_access_token(&self.cfg, &self.signing_key).context("mint GCP access token")?;
        let bearer = new.token.clone();
        let exp_in = new
            .expires_at_unix
            .saturating_sub(now_unix_secs().unwrap_or(0));
        tracing::debug!(
            expires_in_secs = exp_in,
            "gcp_auth: minted new access token",
        );
        *g = Some(new);
        Ok(bearer)
    }
}

fn parse_signing_key(pem_bytes: &[u8]) -> Result<SigningKey<rsa::sha2::Sha256>> {
    // Trim trailing whitespace — jq -r adds a final newline on top of
    // the PEM's own trailing newline, and pem-rfc7468 then tries to
    // parse a second (empty) block and errors at "pre-encapsulation
    // boundary". Tolerate both forms.
    let pem_str = std::str::from_utf8(pem_bytes)
        .context("SA key PEM is not UTF-8")?
        .trim();
    let key = RsaPrivateKey::from_pkcs8_pem(pem_str).context("parse SA PKCS#8 private key")?;
    Ok(SigningKey::<rsa::sha2::Sha256>::new(key))
}

#[derive(Serialize)]
struct JwtHeader<'a> {
    alg: &'static str,
    typ: &'static str,
    kid: &'a str,
}

#[derive(Serialize)]
struct JwtClaims<'a> {
    iss: &'a str,
    scope: &'static str,
    aud: &'static str,
    iat: u64,
    exp: u64,
}

#[derive(Deserialize)]
struct TokenResp {
    access_token: String,
    expires_in: u64,
}

/// Multi-scope so the resulting access token works against both
/// `logging.googleapis.com` and `monitoring.googleapis.com`.
const SCOPES: &str =
    "https://www.googleapis.com/auth/logging.write https://www.googleapis.com/auth/monitoring.write";

fn mint_access_token(
    cfg: &GcpConfig,
    signing_key: &SigningKey<rsa::sha2::Sha256>,
) -> Result<CachedToken> {
    let now = now_unix_secs().ok_or_else(|| anyhow!("NTP not synced; cannot mint JWT"))?;

    let header = JwtHeader {
        alg: "RS256",
        typ: "JWT",
        kid: &cfg.sa_key_id,
    };
    let claims = JwtClaims {
        iss: &cfg.sa_email,
        scope: SCOPES,
        aud: "https://oauth2.googleapis.com/token",
        iat: now,
        exp: now + 3600,
    };

    let header_b64 = b64url(&serde_json::to_vec(&header)?);
    let claims_b64 = b64url(&serde_json::to_vec(&claims)?);
    let signing_input = format!("{}.{}", header_b64, claims_b64);
    let sig = signing_key.sign(signing_input.as_bytes());
    let sig_b64 = b64url(sig.to_bytes().as_ref());
    let jwt = format!("{}.{}", signing_input, sig_b64);

    let body = format!(
        "grant_type=urn%3Aietf%3Aparams%3Aoauth%3Agrant-type%3Ajwt-bearer&assertion={}",
        jwt
    );
    let resp_bytes = http_post(
        "https://oauth2.googleapis.com/token",
        "application/x-www-form-urlencoded",
        body.as_bytes(),
        None,
    )
    .context("POST oauth2/token")?;
    let resp: TokenResp =
        serde_json::from_slice(&resp_bytes).context("parse token response JSON")?;

    Ok(CachedToken {
        token: resp.access_token,
        expires_at_unix: now + resp.expires_in,
    })
}

/// Wall-clock time in UNIX seconds, or None if the system clock is
/// still at the ESP-IDF default epoch (anything before 2020-01-01
/// counts as not-yet-synced).
pub fn now_unix_secs() -> Option<u64> {
    use std::time::{SystemTime, UNIX_EPOCH};
    let secs = SystemTime::now().duration_since(UNIX_EPOCH).ok()?.as_secs();
    if secs < 1_577_836_800 {
        None
    } else {
        Some(secs)
    }
}

pub fn unix_to_rfc3339(secs: u64) -> Option<String> {
    use time::format_description::well_known::Rfc3339;
    use time::OffsetDateTime;
    OffsetDateTime::from_unix_timestamp(secs as i64)
        .ok()
        .and_then(|dt| dt.format(&Rfc3339).ok())
}

pub fn b64url(input: &[u8]) -> String {
    base64::engine::general_purpose::URL_SAFE_NO_PAD.encode(input)
}

/// HTTPS POST helper. Returns the response body bytes. Errors on any
/// non-2xx with the body included for diagnosis.
pub fn http_post(
    url: &str,
    content_type: &str,
    body: &[u8],
    bearer: Option<&str>,
) -> Result<Vec<u8>> {
    let conn = EspHttpConnection::new(&HttpConfig {
        crt_bundle_attach: Some(esp_idf_svc::sys::esp_crt_bundle_attach),
        follow_redirects_policy: FollowRedirectsPolicy::FollowAll,
        timeout: Some(Duration::from_secs(30)),
        buffer_size: Some(2048),
        buffer_size_tx: Some(4096),
        ..Default::default()
    })?;
    let mut client = Client::wrap(conn);
    let body_len = body.len().to_string();
    let mut headers: Vec<(&str, &str)> = vec![
        ("content-type", content_type),
        ("content-length", body_len.as_str()),
        ("accept", "application/json"),
    ];
    if let Some(b) = bearer {
        headers.push(("authorization", b));
    }
    let mut req = client.request(Method::Post, url, &headers)?;
    req.write_all(body).context("write request body")?;
    req.flush().ok();
    let mut resp = req.submit()?;
    let status = resp.status();
    let mut buf = Vec::with_capacity(1024);
    let mut chunk = [0u8; 1024];
    loop {
        let n = resp.read(&mut chunk).context("read response chunk")?;
        if n == 0 {
            break;
        }
        buf.extend_from_slice(&chunk[..n]);
    }
    if !(200..300).contains(&status) {
        bail!(
            "POST {} -> HTTP {} body={}",
            url,
            status,
            String::from_utf8_lossy(&buf)
        );
    }
    Ok(buf)
}

/// MAC address as a `aabbccddeeff` hex string. Used as the `node_id`
/// label on Cloud Logging entries + Cloud Monitoring resource labels.
pub fn device_mac() -> String {
    let mut mac = [0u8; 8];
    unsafe {
        esp_idf_svc::sys::esp_efuse_mac_get_default(mac.as_mut_ptr());
    }
    let mut s = String::with_capacity(12);
    for b in &mac[..6] {
        use std::fmt::Write as _;
        let _ = write!(s, "{:02x}", b);
    }
    s
}

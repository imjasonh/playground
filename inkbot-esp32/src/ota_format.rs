//! Host-testable OTA encoding and firmware-config checks.

/// OCI layer media type written by `tools/publisher` and required by the device.
pub const OTA_LAYER_MEDIA_TYPE: &str = "application/vnd.esp32.firmware.bin";

/// OCI config media type written by `tools/publisher`.
pub const OTA_CONFIG_MEDIA_TYPE: &str = "application/vnd.esp32.firmware.v1+json";

/// Bytes reserved for each OTA slot in `partitions.csv` (`0x1F0000`).
pub const OTA_SLOT_BYTES: u64 = 0x1F_0000;

/// GHCR namespace that holds one package per firmware app.
pub const GHCR_NAMESPACE: &str = "ghcr.io/imjasonh/playground";

/// inkbot Worker poller image (`make flash`, default `ota/app`).
pub const OTA_APP_INKBOT: &str = "inkbot-esp32";

/// Offline maze image. inkbot can pull this; maze cannot pull back.
pub const OTA_APP_MAZE: &str = "maze-esp32";

/// Apps the device is willing to flash. Add a new OTA image here.
pub const OTA_APPS: &[&str] = &[OTA_APP_INKBOT, OTA_APP_MAZE];

/// Chip id the device accepts in the signed OCI config blob.
pub const OTA_TARGET_CHIP: &str = "esp32";

/// Cosign 2 registry attachment (`sha256-<digest>.sig` layer).
pub const COSIGN_SIMPLE_SIGNING_MEDIA_TYPE: &str =
    "application/vnd.dev.cosign.simplesigning.v1+json";

/// Sigstore bundle layer prefix (device-side DSSE / in-toto path).
pub const SIGSTORE_BUNDLE_MEDIA_TYPE_PREFIX: &str = "application/vnd.dev.sigstore.bundle.";

/// Tags Cosign 2 and older Cosign use for a signature attachment.
///
/// Cosign 2.5 tags `sha256-<hex>.sig`. The first firmware looked up
/// `sha256-<hex>` with no suffix and 404'd.
pub fn cosign_signature_tags(manifest_digest_hex: &str) -> [String; 2] {
    [
        format!("sha256-{manifest_digest_hex}.sig"),
        format!("sha256-{manifest_digest_hex}"),
    ]
}

/// Manifest digest hex (no `sha256:`) bound in a Cosign simple-signing payload.
pub fn cosign_manifest_digest_hex(payload: &[u8]) -> Result<String, &'static str> {
    #[derive(serde::Deserialize)]
    struct Payload {
        critical: Critical,
    }
    #[derive(serde::Deserialize)]
    struct Critical {
        image: Image,
        #[serde(rename = "type")]
        kind: String,
    }
    #[derive(serde::Deserialize)]
    struct Image {
        #[serde(rename = "docker-manifest-digest")]
        digest: String,
    }

    let p: Payload = serde_json::from_slice(payload).map_err(|_| "cosign payload is not JSON")?;
    if p.critical.kind != "cosign container image signature" {
        return Err("cosign payload type is not a container image signature");
    }
    let d = p.critical.image.digest;
    d.strip_prefix("sha256:")
        .map(str::to_string)
        .filter(|h| !h.is_empty() && h.bytes().all(|b| b.is_ascii_hexdigit()))
        .ok_or("cosign payload digest is not sha256:<hex>")
}

/// True when `app` is a firmware image this device knows how to boot.
pub fn known_ota_app(app: &str) -> bool {
    OTA_APPS.contains(&app)
}

/// Default GHCR repo for `app` when NVS `ota/repo` is unset.
pub fn default_ota_repo(app: &str) -> String {
    format!("{GHCR_NAMESPACE}/{app}")
}

/// DSSE Pre-Authentication Encoding (https://github.com/secure-systems-lab/dsse).
///
/// `PAE("DSSEv1", payloadType, payload)` is
/// `"DSSEv1 <len(type)> <type> <len(payload)> <payload>"`.
pub fn pae_dsse_v1(payload_type: &str, payload: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(64 + payload_type.len() + payload.len());
    out.extend_from_slice(b"DSSEv1 ");
    out.extend_from_slice(payload_type.len().to_string().as_bytes());
    out.push(b' ');
    out.extend_from_slice(payload_type.as_bytes());
    out.push(b' ');
    out.extend_from_slice(payload.len().to_string().as_bytes());
    out.push(b' ');
    out.extend_from_slice(payload);
    out
}

/// Base64url without padding (RFC 4648 §5).
pub fn b64url(input: &[u8]) -> String {
    const TABLE: &[u8; 64] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_";
    let mut out = String::with_capacity((input.len() * 4).div_ceil(3));
    let mut i = 0;
    while i < input.len() {
        let b0 = input[i];
        let b1 = if i + 1 < input.len() { input[i + 1] } else { 0 };
        let b2 = if i + 2 < input.len() { input[i + 2] } else { 0 };
        let n = ((b0 as u32) << 16) | ((b1 as u32) << 8) | (b2 as u32);
        out.push(TABLE[((n >> 18) & 63) as usize] as char);
        out.push(TABLE[((n >> 12) & 63) as usize] as char);
        if i + 1 < input.len() {
            out.push(TABLE[((n >> 6) & 63) as usize] as char);
        }
        if i + 2 < input.len() {
            out.push(TABLE[(n & 63) as usize] as char);
        }
        i += 3;
    }
    out
}

/// Escape `s` for embedding in a JSON string value.
pub fn json_escape(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => {
                use std::fmt::Write as _;
                let _ = write!(out, "\\u{:04x}", c as u32);
            }
            c => out.push(c),
        }
    }
    out
}

/// Return an error unless `url` uses `https://`.
pub fn require_https_url(url: &str) -> Result<(), &'static str> {
    if url.starts_with("https://") {
        Ok(())
    } else {
        Err("URL must start with https://")
    }
}

/// Result of comparing unix `now` to a certificate notBefore/notAfter window.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CertWindow {
    Valid,
    NotYetValid,
    Expired,
}

/// Classify `now` against `[not_before, not_after]`.
pub fn cert_window(now: u64, not_before: u64, not_after: u64) -> CertWindow {
    if now < not_before {
        CertWindow::NotYetValid
    } else if now > not_after {
        CertWindow::Expired
    } else {
        CertWindow::Valid
    }
}

/// Fulcio signing leaves last about 10 minutes. Cosign uses Rekor's integrated
/// time after that. This firmware does not query Rekor, so an expired leaf is
/// still accepted when chain, identity, and signature match. A not-yet-valid
/// leaf is rejected.
pub fn fulcio_leaf_window_ok(
    now: u64,
    not_before: u64,
    not_after: u64,
) -> Result<(), &'static str> {
    match cert_window(now, not_before, not_after) {
        CertWindow::NotYetValid => Err("leaf cert not yet valid"),
        CertWindow::Valid | CertWindow::Expired => Ok(()),
    }
}

/// Intermediate and root certificates keep a full wall-clock validity check.
pub fn ca_cert_window_ok(now: u64, not_before: u64, not_after: u64) -> Result<(), &'static str> {
    match cert_window(now, not_before, not_after) {
        CertWindow::Valid => Ok(()),
        CertWindow::NotYetValid => Err("cert not yet valid"),
        CertWindow::Expired => Err("cert expired"),
    }
}

/// Decode a Fulcio OIDC issuer extension value.
///
/// OID `1.3.6.1.4.1.57264.1.8` is a DER UTF8String. The deprecated
/// `1.3.6.1.4.1.57264.1.1` extension is raw UTF-8.
pub fn decode_fulcio_issuer_value(bytes: &[u8]) -> Result<String, &'static str> {
    if bytes.first() == Some(&0x0c) {
        der_utf8_string(bytes)
    } else {
        std::str::from_utf8(bytes)
            .map(str::to_string)
            .map_err(|_| "issuer is not UTF-8")
    }
}

fn der_utf8_string(bytes: &[u8]) -> Result<String, &'static str> {
    if bytes.len() < 2 || bytes[0] != 0x0c {
        return Err("not a DER UTF8String");
    }
    let (len, header) = der_len(&bytes[1..])?;
    let start = 1 + header;
    let data = bytes
        .get(start..start.checked_add(len).ok_or("truncated DER UTF8String")?)
        .ok_or("truncated DER UTF8String")?;
    std::str::from_utf8(data)
        .map(str::to_string)
        .map_err(|_| "issuer is not UTF-8")
}

/// Parse a DER length at the start of `rest`. Returns `(value, header_bytes)`.
fn der_len(rest: &[u8]) -> Result<(usize, usize), &'static str> {
    let first = *rest.first().ok_or("truncated DER length")?;
    if first < 0x80 {
        return Ok((first as usize, 1));
    }
    let n = (first & 0x7f) as usize;
    if n == 0 || n > 2 || rest.len() < 1 + n {
        return Err("unsupported DER length");
    }
    let mut len = 0usize;
    for b in &rest[1..1 + n] {
        len = (len << 8) | (*b as usize);
    }
    Ok((len, 1 + n))
}

/// Fields the device reads from the publisher's OCI config blob.
#[derive(Debug, serde::Deserialize, PartialEq, Eq)]
pub struct FirmwareConfig {
    pub target_chip: String,
    pub app: String,
    #[serde(default)]
    pub bin_size: Option<u64>,
}

/// Check that a signed config blob is the requested app and fits one OTA slot.
///
/// `expected_app` is the NVS `ota/app` value (or the compile-time default),
/// not the binary that is currently running. That is how inkbot pulls maze.
pub fn check_ota_image(
    cfg: &FirmwareConfig,
    layer_size: u64,
    expected_app: &str,
) -> Result<(), String> {
    if !known_ota_app(expected_app) {
        return Err(format!("unknown expected app {expected_app}"));
    }
    if cfg.target_chip != OTA_TARGET_CHIP {
        return Err(format!(
            "firmware config target_chip={} (want {OTA_TARGET_CHIP})",
            cfg.target_chip
        ));
    }
    if cfg.app != expected_app {
        return Err(format!(
            "firmware config app={} (want {expected_app})",
            cfg.app
        ));
    }
    if layer_size == 0 || layer_size > OTA_SLOT_BYTES {
        return Err(format!(
            "firmware layer size {layer_size} does not fit OTA slot ({OTA_SLOT_BYTES} bytes)"
        ));
    }
    if let Some(n) = cfg.bin_size {
        if n != layer_size {
            return Err(format!(
                "firmware config bin_size={n} does not match layer size {layer_size}"
            ));
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pae_matches_dsse_spec_example_shape() {
        let pae = pae_dsse_v1("application/vnd.in-toto+json", b"{}");
        assert_eq!(pae, b"DSSEv1 28 application/vnd.in-toto+json 2 {}".to_vec());
    }

    #[test]
    fn b64url_no_pad_is_rfc4648() {
        assert_eq!(b64url(b""), "");
        assert_eq!(b64url(b"f"), "Zg");
        assert_eq!(b64url(b"fo"), "Zm8");
        assert_eq!(b64url(b"foo"), "Zm9v");
        assert_eq!(b64url(&[0xfb, 0xff]), "-_8");
    }

    #[test]
    fn json_escape_quotes_and_controls() {
        assert_eq!(json_escape(r#"a"b\c"#), r#"a\"b\\c"#);
        assert_eq!(json_escape("line\nnext\tend"), r#"line\nnext\tend"#);
        assert_eq!(json_escape("\u{0001}"), r#"\u0001"#);
    }

    #[test]
    fn require_https_url_rejects_plaintext() {
        assert!(require_https_url("https://inkbot.example.workers.dev").is_ok());
        assert!(require_https_url("http://inkbot.example.workers.dev").is_err());
        assert!(require_https_url("inkbot.example.workers.dev").is_err());
    }

    #[test]
    fn fulcio_issuer_v2_is_der_utf8string() {
        let mut der = vec![0x0c, 0x0b];
        der.extend_from_slice(b"https://x.y");
        assert_eq!(decode_fulcio_issuer_value(&der).unwrap(), "https://x.y");
    }

    #[test]
    fn fulcio_issuer_v1_is_raw_utf8() {
        assert_eq!(
            decode_fulcio_issuer_value(b"https://accounts.google.com").unwrap(),
            "https://accounts.google.com"
        );
    }

    #[test]
    fn cert_window_classifies_not_before_and_not_after() {
        assert_eq!(cert_window(50, 100, 200), CertWindow::NotYetValid);
        assert_eq!(cert_window(100, 100, 200), CertWindow::Valid);
        assert_eq!(cert_window(200, 100, 200), CertWindow::Valid);
        assert_eq!(cert_window(201, 100, 200), CertWindow::Expired);
    }

    #[test]
    fn fulcio_leaf_accepts_expired_window() {
        // Issued 1h ago, 10-minute Fulcio lifetime, verified later.
        assert!(fulcio_leaf_window_ok(3_600, 0, 600).is_ok());
        assert!(fulcio_leaf_window_ok(300, 0, 600).is_ok());
        assert_eq!(
            fulcio_leaf_window_ok(50, 100, 200).unwrap_err(),
            "leaf cert not yet valid"
        );
        assert!(ca_cert_window_ok(3_600, 0, 600).is_err());
        assert!(ca_cert_window_ok(300, 0, 600).is_ok());
        assert!(ca_cert_window_ok(50, 100, 200).is_err());
    }

    #[test]
    fn check_ota_image_accepts_requested_app() {
        let inkbot = FirmwareConfig {
            target_chip: OTA_TARGET_CHIP.into(),
            app: OTA_APP_INKBOT.into(),
            bin_size: Some(100),
        };
        assert!(check_ota_image(&inkbot, 100, OTA_APP_INKBOT).is_ok());

        let maze = FirmwareConfig {
            target_chip: OTA_TARGET_CHIP.into(),
            app: OTA_APP_MAZE.into(),
            bin_size: Some(100),
        };
        assert!(check_ota_image(&maze, 100, OTA_APP_MAZE).is_ok());
        assert!(check_ota_image(&maze, 100, OTA_APP_INKBOT).is_err());
        assert!(check_ota_image(&inkbot, 100, OTA_APP_MAZE).is_err());
    }

    #[test]
    fn cosign_signature_tags_try_dot_sig_first() {
        assert_eq!(
            cosign_signature_tags("abc"),
            ["sha256-abc.sig".to_string(), "sha256-abc".to_string(),]
        );
    }

    #[test]
    fn cosign_manifest_digest_hex_from_simple_signing() {
        let payload = br#"{"critical":{"identity":{"docker-reference":"ghcr.io/imjasonh/playground/inkbot-esp32"},"image":{"docker-manifest-digest":"sha256:cb75825bdc31b9121b9a5ff45f27170b3ce32898d727bc336ff171ee55ba3155"},"type":"cosign container image signature"},"optional":null}"#;
        assert_eq!(
            cosign_manifest_digest_hex(payload).unwrap(),
            "cb75825bdc31b9121b9a5ff45f27170b3ce32898d727bc336ff171ee55ba3155"
        );
    }

    #[test]
    fn cosign_manifest_digest_hex_rejects_wrong_type() {
        let payload = br#"{"critical":{"identity":{"docker-reference":"x"},"image":{"docker-manifest-digest":"sha256:aa"},"type":"not-cosign"},"optional":null}"#;
        assert!(cosign_manifest_digest_hex(payload).is_err());
    }

    #[test]
    fn check_ota_image_rejects_unknown_expected_app() {
        let cfg = FirmwareConfig {
            target_chip: OTA_TARGET_CHIP.into(),
            app: "not-an-app".into(),
            bin_size: None,
        };
        assert!(check_ota_image(&cfg, 100, "not-an-app").is_err());
    }

    #[test]
    fn check_ota_image_rejects_wrong_chip_or_size() {
        let chip = FirmwareConfig {
            target_chip: "esp32s3".into(),
            app: OTA_APP_INKBOT.into(),
            bin_size: None,
        };
        assert!(check_ota_image(&chip, 100, OTA_APP_INKBOT).is_err());

        let ok = FirmwareConfig {
            target_chip: OTA_TARGET_CHIP.into(),
            app: OTA_APP_INKBOT.into(),
            bin_size: None,
        };
        assert!(check_ota_image(&ok, OTA_SLOT_BYTES + 1, OTA_APP_INKBOT).is_err());
        assert!(check_ota_image(&ok, 0, OTA_APP_INKBOT).is_err());
    }

    #[test]
    fn default_ota_repo_uses_namespace_and_app() {
        assert_eq!(
            default_ota_repo(OTA_APP_INKBOT),
            format!("{GHCR_NAMESPACE}/{OTA_APP_INKBOT}")
        );
        assert_eq!(
            default_ota_repo(OTA_APP_MAZE),
            format!("{GHCR_NAMESPACE}/{OTA_APP_MAZE}")
        );
    }

    #[test]
    fn known_ota_app_accepts_catalog() {
        assert!(known_ota_app(OTA_APP_INKBOT));
        assert!(known_ota_app(OTA_APP_MAZE));
        assert!(!known_ota_app("not-an-app"));
        assert_eq!(OTA_APPS, &[OTA_APP_INKBOT, OTA_APP_MAZE]);
    }
}

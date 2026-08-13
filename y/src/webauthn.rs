//! WebAuthn (passkey) options + ES256 verification.
//!
//! Single-user model: one virtual user (`y-admin`). RP ID and origin come from
//! `SITE_URL`. Stored public keys are COSE_Key bytes (same as
//! `@simplewebauthn/server`), so existing D1 credentials keep working.
//! Only ES256 (P-256) is verified — that is what platform authenticators
//! actually emit for this app.

use p256::ecdsa::signature::Verifier;
use p256::ecdsa::{Signature, VerifyingKey};
use p256::EncodedPoint;
use serde::Deserialize;
use serde_json::{json, Value};
use sha2::{Digest, Sha256};

use crate::auth::random_challenge;

pub const RP_NAME_DEFAULT: &str = "y";
pub const USER_HANDLE: &str = "y-admin";
pub const USER_NAME: &str = "admin";

#[derive(Debug, Clone)]
pub struct RpContext {
    pub rp_id: String,
    pub origin: String,
    pub rp_name: String,
}

impl RpContext {
    pub fn from_site(site_url: &str, site_title: &str) -> Result<Self, String> {
        let u = url::Url::parse(site_url).map_err(|_| "invalid SITE_URL".to_string())?;
        let host = u
            .host_str()
            .ok_or_else(|| "SITE_URL missing host".to_string())?;
        Ok(Self {
            rp_id: host.to_string(),
            origin: u.origin().ascii_serialization(),
            rp_name: if site_title.is_empty() {
                RP_NAME_DEFAULT.to_string()
            } else {
                site_title.to_string()
            },
        })
    }
}

#[derive(Debug, Clone)]
pub struct Credential {
    pub id: String,
    pub public_key: Vec<u8>,
    pub counter: u32,
    pub transports: Option<String>,
}

#[derive(Debug, Deserialize)]
pub struct RegistrationResponse {
    pub id: String,
    pub response: RegistrationResponseInner,
}

#[derive(Debug, Deserialize)]
pub struct RegistrationResponseInner {
    #[serde(rename = "attestationObject")]
    pub attestation_object: String,
    #[serde(rename = "clientDataJSON")]
    pub client_data_json: String,
    pub transports: Option<Vec<String>>,
}

#[derive(Debug, Deserialize)]
pub struct AuthenticationResponse {
    pub id: String,
    pub response: AuthenticationResponseInner,
}

#[derive(Debug, Deserialize)]
pub struct AuthenticationResponseInner {
    #[serde(rename = "authenticatorData")]
    pub authenticator_data: String,
    #[serde(rename = "clientDataJSON")]
    pub client_data_json: String,
    pub signature: String,
}

#[derive(Debug, Deserialize)]
struct ClientData {
    #[serde(rename = "type")]
    type_: String,
    challenge: String,
    origin: String,
}

pub fn b64url_encode(bytes: &[u8]) -> String {
    use base64::engine::general_purpose::URL_SAFE_NO_PAD;
    use base64::Engine;
    URL_SAFE_NO_PAD.encode(bytes)
}

pub fn b64url_decode(s: &str) -> Result<Vec<u8>, String> {
    use base64::engine::general_purpose::{URL_SAFE, URL_SAFE_NO_PAD};
    use base64::Engine;
    let s = s.trim();
    if s.contains('=') {
        URL_SAFE.decode(s)
    } else {
        URL_SAFE_NO_PAD.decode(s)
    }
    .map_err(|_| "invalid base64url".to_string())
}

pub fn registration_options(rp: &RpContext, existing: &[Credential]) -> Value {
    let challenge = random_challenge();
    let user_id = b64url_encode(USER_HANDLE.as_bytes());
    let exclude: Vec<Value> = existing
        .iter()
        .map(|c| {
            let mut cred = json!({ "type": "public-key", "id": c.id });
            if let Some(t) = &c.transports {
                let parts: Vec<&str> = t.split(',').filter(|s| !s.is_empty()).collect();
                if !parts.is_empty() {
                    cred["transports"] = json!(parts);
                }
            }
            cred
        })
        .collect();
    json!({
        "challenge": challenge,
        "rp": { "name": rp.rp_name, "id": rp.rp_id },
        "user": {
            "id": user_id,
            "name": USER_NAME,
            "displayName": USER_NAME,
        },
        "pubKeyCredParams": [
            { "alg": -7, "type": "public-key" }
        ],
        "timeout": 60000,
        "attestation": "none",
        "excludeCredentials": exclude,
        "authenticatorSelection": {
            "residentKey": "preferred",
            "userVerification": "preferred",
            "requireResidentKey": false
        },
    })
}

pub fn authentication_options(rp: &RpContext, existing: &[Credential]) -> Value {
    let challenge = random_challenge();
    let allow: Vec<Value> = existing
        .iter()
        .map(|c| {
            let mut cred = json!({ "type": "public-key", "id": c.id });
            if let Some(t) = &c.transports {
                let parts: Vec<&str> = t.split(',').filter(|s| !s.is_empty()).collect();
                if !parts.is_empty() {
                    cred["transports"] = json!(parts);
                }
            }
            cred
        })
        .collect();
    json!({
        "challenge": challenge,
        "timeout": 60000,
        "rpId": rp.rp_id,
        "allowCredentials": allow,
        "userVerification": "preferred",
    })
}

pub struct VerifiedRegistration {
    pub credential_id: String,
    pub public_key: Vec<u8>,
    pub counter: u32,
    pub transports: Option<Vec<String>>,
}

pub fn verify_registration(
    rp: &RpContext,
    expected_challenge: &str,
    response: &RegistrationResponse,
) -> Result<VerifiedRegistration, String> {
    let client_raw = b64url_decode(&response.response.client_data_json)?;
    check_client_data(
        &client_raw,
        "webauthn.create",
        expected_challenge,
        &rp.origin,
    )?;

    let att = b64url_decode(&response.response.attestation_object)?;
    let auth_data = attestation_auth_data(&att)?;
    let parsed = parse_auth_data(&auth_data, true)?;
    check_rp_id_hash(&parsed.rp_id_hash, &rp.rp_id)?;
    let cred = parsed
        .credential
        .ok_or_else(|| "attestation missing credential".to_string())?;
    // Touch the COSE key now so we refuse non-ES256 at registration time.
    cose_p256_key(&cred.public_key)?;
    Ok(VerifiedRegistration {
        credential_id: b64url_encode(&cred.id),
        public_key: cred.public_key,
        counter: parsed.counter,
        transports: response.response.transports.clone(),
    })
}

pub struct VerifiedAuthentication {
    pub new_counter: u32,
}

pub fn verify_authentication(
    rp: &RpContext,
    expected_challenge: &str,
    stored: &Credential,
    response: &AuthenticationResponse,
) -> Result<VerifiedAuthentication, String> {
    if response.id != stored.id {
        return Err("credential id mismatch".into());
    }
    let client_raw = b64url_decode(&response.response.client_data_json)?;
    check_client_data(&client_raw, "webauthn.get", expected_challenge, &rp.origin)?;

    let auth_data = b64url_decode(&response.response.authenticator_data)?;
    let parsed = parse_auth_data(&auth_data, false)?;
    check_rp_id_hash(&parsed.rp_id_hash, &rp.rp_id)?;
    if stored.counter > 0 && parsed.counter <= stored.counter {
        return Err("authenticator counter did not increase".into());
    }

    let sig = b64url_decode(&response.response.signature)?;
    let client_hash = Sha256::digest(&client_raw);
    let mut signed = Vec::with_capacity(auth_data.len() + 32);
    signed.extend_from_slice(&auth_data);
    signed.extend_from_slice(&client_hash);

    let vk = cose_p256_key(&stored.public_key)?;
    let signature = Signature::from_der(&sig)
        .or_else(|_| Signature::from_slice(&sig))
        .map_err(|_| "invalid assertion signature".to_string())?;
    vk.verify(&signed, &signature)
        .map_err(|_| "assertion not verified".to_string())?;

    Ok(VerifiedAuthentication {
        new_counter: parsed.counter,
    })
}

fn check_client_data(
    raw: &[u8],
    expected_type: &str,
    expected_challenge: &str,
    expected_origin: &str,
) -> Result<(), String> {
    let data: ClientData =
        serde_json::from_slice(raw).map_err(|_| "invalid clientDataJSON".to_string())?;
    if data.type_ != expected_type {
        return Err("unexpected clientData type".into());
    }
    if data.origin != expected_origin {
        return Err("origin mismatch".into());
    }
    if data.challenge != expected_challenge {
        let got = b64url_decode(&data.challenge)?;
        let want = b64url_decode(expected_challenge)?;
        if got != want {
            return Err("challenge mismatch".into());
        }
    }
    Ok(())
}

fn check_rp_id_hash(got: &[u8; 32], rp_id: &str) -> Result<(), String> {
    let want = Sha256::digest(rp_id.as_bytes());
    if got[..] != want[..] {
        return Err("rpIdHash mismatch".into());
    }
    Ok(())
}

struct AttestedCred {
    id: Vec<u8>,
    public_key: Vec<u8>,
}

struct ParsedAuthData {
    rp_id_hash: [u8; 32],
    counter: u32,
    credential: Option<AttestedCred>,
}

fn parse_auth_data(data: &[u8], require_at: bool) -> Result<ParsedAuthData, String> {
    if data.len() < 37 {
        return Err("authenticatorData too short".into());
    }
    let mut rp_id_hash = [0u8; 32];
    rp_id_hash.copy_from_slice(&data[..32]);
    let flags = data[32];
    let counter = u32::from_be_bytes(data[33..37].try_into().unwrap());
    let at = flags & 0x40 != 0;
    if require_at && !at {
        return Err("attested credential data missing".into());
    }
    let credential = if at {
        if data.len() < 55 {
            return Err("attested credential truncated".into());
        }
        let cred_id_len = u16::from_be_bytes(data[53..55].try_into().unwrap()) as usize;
        let id_start: usize = 55;
        let id_end = id_start
            .checked_add(cred_id_len)
            .ok_or_else(|| "credential id overflow".to_string())?;
        if data.len() < id_end {
            return Err("credential id truncated".into());
        }
        let id = data[id_start..id_end].to_vec();
        let cose = data[id_end..].to_vec();
        // COSE key may be followed by extensions; take the first CBOR value.
        let (key, _) = take_cbor_item(&cose)?;
        Some(AttestedCred {
            id,
            public_key: key,
        })
    } else {
        None
    };
    Ok(ParsedAuthData {
        rp_id_hash,
        counter,
        credential,
    })
}

fn attestation_auth_data(att: &[u8]) -> Result<Vec<u8>, String> {
    let (item, _) = take_cbor_item(att)?;
    let map = decode_text_map(&item)?;
    map.into_iter()
        .find(|(k, _)| k == "authData")
        .map(|(_, v)| v)
        .ok_or_else(|| "attestationObject missing authData".to_string())
        .and_then(|v| match v {
            Cbor::Bytes(b) => Ok(b),
            _ => Err("authData is not a bstr".into()),
        })
}

fn cose_p256_key(cose: &[u8]) -> Result<VerifyingKey, String> {
    let map = decode_int_map(cose)?;
    let kty = map
        .iter()
        .find(|(k, _)| *k == 1)
        .and_then(|(_, v)| v.as_int())
        .ok_or_else(|| "COSE key missing kty".to_string())?;
    if kty != 2 {
        return Err("unsupported COSE kty (want EC2/P-256)".into());
    }
    let crv = map
        .iter()
        .find(|(k, _)| *k == -1)
        .and_then(|(_, v)| v.as_int())
        .ok_or_else(|| "COSE key missing crv".to_string())?;
    if crv != 1 {
        return Err("unsupported COSE curve (want P-256)".into());
    }
    let x = map
        .iter()
        .find(|(k, _)| *k == -2)
        .and_then(|(_, v)| v.as_bytes())
        .ok_or_else(|| "COSE key missing x".to_string())?;
    let y = map
        .iter()
        .find(|(k, _)| *k == -3)
        .and_then(|(_, v)| v.as_bytes())
        .ok_or_else(|| "COSE key missing y".to_string())?;
    if x.len() != 32 || y.len() != 32 {
        return Err("COSE P-256 coordinates must be 32 bytes".into());
    }
    let mut uncompressed = [0u8; 65];
    uncompressed[0] = 0x04;
    uncompressed[1..33].copy_from_slice(x);
    uncompressed[33..].copy_from_slice(y);
    let point =
        EncodedPoint::from_bytes(uncompressed).map_err(|_| "invalid P-256 point".to_string())?;
    VerifyingKey::from_encoded_point(&point).map_err(|_| "invalid P-256 public key".to_string())
}

#[derive(Debug)]
#[allow(dead_code)]
enum Cbor {
    Unsigned(u64),
    Negative(i64),
    Bytes(Vec<u8>),
    Text(String),
    #[allow(dead_code)]
    Array(Vec<Cbor>),
    Map(Vec<(Cbor, Cbor)>),
    Other,
}

impl Cbor {
    fn as_int(&self) -> Option<i64> {
        match self {
            Cbor::Unsigned(n) if *n <= i64::MAX as u64 => Some(*n as i64),
            Cbor::Negative(n) => Some(*n),
            _ => None,
        }
    }
    fn as_bytes(&self) -> Option<&[u8]> {
        match self {
            Cbor::Bytes(b) => Some(b),
            _ => None,
        }
    }
}

fn take_cbor_item(input: &[u8]) -> Result<(Vec<u8>, usize), String> {
    let (val, n) = decode_cbor(input)?;
    let _ = val;
    Ok((input[..n].to_vec(), n))
}

fn decode_text_map(item: &[u8]) -> Result<Vec<(String, Cbor)>, String> {
    let (val, _) = decode_cbor(item)?;
    match val {
        Cbor::Map(entries) => {
            let mut out = Vec::new();
            for (k, v) in entries {
                if let Cbor::Text(s) = k {
                    out.push((s, v));
                }
            }
            Ok(out)
        }
        _ => Err("expected CBOR map".into()),
    }
}

fn decode_int_map(item: &[u8]) -> Result<Vec<(i64, Cbor)>, String> {
    let (val, _) = decode_cbor(item)?;
    match val {
        Cbor::Map(entries) => {
            let mut out = Vec::new();
            for (k, v) in entries {
                if let Some(i) = k.as_int() {
                    out.push((i, v));
                }
            }
            Ok(out)
        }
        _ => Err("expected COSE CBOR map".into()),
    }
}

fn decode_cbor(input: &[u8]) -> Result<(Cbor, usize), String> {
    if input.is_empty() {
        return Err("truncated CBOR".into());
    }
    let b = input[0];
    let major = b >> 5;
    let ai = b & 0x1f;
    let (len, hdr) = additional(input, ai)?;
    let rest = &input[hdr..];
    match major {
        0 => Ok((Cbor::Unsigned(len), hdr)),
        1 => Ok((Cbor::Negative(-1 - (len as i64)), hdr)),
        2 => {
            let n = len as usize;
            if rest.len() < n {
                return Err("truncated bstr".into());
            }
            Ok((Cbor::Bytes(rest[..n].to_vec()), hdr + n))
        }
        3 => {
            let n = len as usize;
            if rest.len() < n {
                return Err("truncated tstr".into());
            }
            let s = std::str::from_utf8(&rest[..n]).map_err(|_| "invalid tstr utf8".to_string())?;
            Ok((Cbor::Text(s.to_string()), hdr + n))
        }
        4 => {
            let mut pos = hdr;
            let mut items = Vec::with_capacity(len as usize);
            for _ in 0..len {
                let (v, n) = decode_cbor(&input[pos..])?;
                items.push(v);
                pos += n;
            }
            Ok((Cbor::Array(items), pos))
        }
        5 => {
            let mut pos = hdr;
            let mut items = Vec::with_capacity(len as usize);
            for _ in 0..len {
                let (k, n1) = decode_cbor(&input[pos..])?;
                pos += n1;
                let (v, n2) = decode_cbor(&input[pos..])?;
                pos += n2;
                items.push((k, v));
            }
            Ok((Cbor::Map(items), pos))
        }
        6 => {
            let (inner, n) = decode_cbor(rest)?;
            Ok((inner, hdr + n))
        }
        _ => {
            if ai == 31 {
                return Err("indefinite CBOR not supported".into());
            }
            Ok((Cbor::Other, hdr))
        }
    }
}

fn additional(input: &[u8], ai: u8) -> Result<(u64, usize), String> {
    match ai {
        n @ 0..=23 => Ok((n as u64, 1)),
        24 => {
            if input.len() < 2 {
                return Err("truncated CBOR".into());
            }
            Ok((input[1] as u64, 2))
        }
        25 => {
            if input.len() < 3 {
                return Err("truncated CBOR".into());
            }
            Ok((u16::from_be_bytes([input[1], input[2]]) as u64, 3))
        }
        26 => {
            if input.len() < 5 {
                return Err("truncated CBOR".into());
            }
            Ok((
                u32::from_be_bytes(input[1..5].try_into().unwrap()) as u64,
                5,
            ))
        }
        27 => {
            if input.len() < 9 {
                return Err("truncated CBOR".into());
            }
            Ok((u64::from_be_bytes(input[1..9].try_into().unwrap()), 9))
        }
        _ => Err("unsupported CBOR additional info".into()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use p256::ecdsa::signature::Signer;
    use p256::ecdsa::SigningKey;
    use rand_core::OsRng;

    fn encode_bstr(bytes: &[u8]) -> Vec<u8> {
        let mut out = Vec::new();
        if bytes.len() < 24 {
            out.push(0x40 | bytes.len() as u8);
        } else if bytes.len() < 256 {
            out.push(0x58);
            out.push(bytes.len() as u8);
        } else {
            out.push(0x59);
            out.extend_from_slice(&(bytes.len() as u16).to_be_bytes());
        }
        out.extend_from_slice(bytes);
        out
    }

    fn encode_tstr(s: &str) -> Vec<u8> {
        let b = s.as_bytes();
        let mut out = Vec::new();
        out.push(0x60 | b.len() as u8);
        out.extend_from_slice(b);
        out
    }

    fn encode_u(n: u64) -> Vec<u8> {
        if n < 24 {
            vec![n as u8]
        } else {
            vec![24, n as u8]
        }
    }

    fn encode_neg(n: i64) -> Vec<u8> {
        // n is the CBOR negative value itself (e.g. -1)
        let payload = (-1 - n) as u64;
        if payload < 24 {
            vec![0x20 | payload as u8]
        } else {
            vec![0x38, payload as u8]
        }
    }

    fn cose_from_vk(vk: &VerifyingKey) -> Vec<u8> {
        let point = vk.to_encoded_point(false);
        let bytes = point.as_bytes();
        let x = &bytes[1..33];
        let y = &bytes[33..65];
        // map of 5: kty=2, alg=-7, crv=1, x, y
        let mut out = vec![0xa5];
        out.extend(encode_u(1));
        out.extend(encode_u(2));
        out.extend(encode_u(3));
        out.extend(encode_neg(-7));
        out.extend(encode_neg(-1));
        out.extend(encode_u(1));
        out.extend(encode_neg(-2));
        out.extend(encode_bstr(x));
        out.extend(encode_neg(-3));
        out.extend(encode_bstr(y));
        out
    }

    fn auth_data(rp_id: &str, counter: u32, cred: Option<(&[u8], &[u8])>) -> Vec<u8> {
        let hash = Sha256::digest(rp_id.as_bytes());
        let mut out = Vec::new();
        out.extend_from_slice(&hash);
        let mut flags = 0x01; // UP
        if cred.is_some() {
            flags |= 0x40; // AT
        }
        out.push(flags);
        out.extend_from_slice(&counter.to_be_bytes());
        if let Some((id, cose)) = cred {
            out.extend_from_slice(&[0u8; 16]); // aaguid
            out.extend_from_slice(&(id.len() as u16).to_be_bytes());
            out.extend_from_slice(id);
            out.extend_from_slice(cose);
        }
        out
    }

    fn att_object(auth_data: &[u8]) -> Vec<u8> {
        // {"fmt":"none","attStmt":{},"authData": ...}  — 3-entry map
        let mut out = vec![0xa3];
        out.extend(encode_tstr("fmt"));
        out.extend(encode_tstr("none"));
        out.extend(encode_tstr("attStmt"));
        out.push(0xa0);
        out.extend(encode_tstr("authData"));
        out.extend(encode_bstr(auth_data));
        out
    }

    #[test]
    fn registration_and_assertion_es256() {
        let rp = RpContext {
            rp_id: "example.com".into(),
            origin: "https://example.com".into(),
            rp_name: "y".into(),
        };
        let signing = SigningKey::random(&mut OsRng);
        let vk = signing.verifying_key();
        let cose = cose_from_vk(vk);
        let cred_id = b"cred-1";
        let ad = auth_data(&rp.rp_id, 1, Some((cred_id, &cose)));
        let att = att_object(&ad);
        let challenge = b64url_encode(b"challenge-bytes-0123456789abcd");
        let client = serde_json::json!({
            "type": "webauthn.create",
            "challenge": challenge,
            "origin": rp.origin,
        });
        let client_bytes = serde_json::to_vec(&client).unwrap();
        let resp = RegistrationResponse {
            id: b64url_encode(cred_id),
            response: RegistrationResponseInner {
                attestation_object: b64url_encode(&att),
                client_data_json: b64url_encode(&client_bytes),
                transports: Some(vec!["internal".into()]),
            },
        };
        let verified = verify_registration(&rp, &challenge, &resp).expect("register");
        assert_eq!(verified.credential_id, b64url_encode(cred_id));
        assert_eq!(verified.counter, 1);

        let stored = Credential {
            id: verified.credential_id.clone(),
            public_key: verified.public_key.clone(),
            counter: verified.counter,
            transports: None,
        };
        let get_ad = auth_data(&rp.rp_id, 2, None);
        let get_client = serde_json::json!({
            "type": "webauthn.get",
            "challenge": challenge,
            "origin": rp.origin,
        });
        let get_client_bytes = serde_json::to_vec(&get_client).unwrap();
        let client_hash = Sha256::digest(&get_client_bytes);
        let mut signed = get_ad.clone();
        signed.extend_from_slice(&client_hash);
        let sig: Signature = signing.sign(&signed);
        let auth_resp = AuthenticationResponse {
            id: stored.id.clone(),
            response: AuthenticationResponseInner {
                authenticator_data: b64url_encode(&get_ad),
                client_data_json: b64url_encode(&get_client_bytes),
                signature: b64url_encode(&sig.to_bytes()[..]),
            },
        };
        let ok = verify_authentication(&rp, &challenge, &stored, &auth_resp).expect("assert");
        assert_eq!(ok.new_counter, 2);
    }

    #[test]
    fn rp_from_site_url() {
        let rp = RpContext::from_site("https://y.imjasonh.workers.dev", "y").unwrap();
        assert_eq!(rp.rp_id, "y.imjasonh.workers.dev");
        assert_eq!(rp.origin, "https://y.imjasonh.workers.dev");
    }
}

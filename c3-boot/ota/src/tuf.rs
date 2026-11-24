//! Packages Sigstore's TUF metadata for a slot, checks it with the device's
//! code, and signs metadata for the development repository and for tests.
//!
//! Sigstore publishes its metadata pretty-printed. The device reads only
//! canonical JSON, so [`package`] and [`pinned_root`] re-encode each
//! document in the canonical form that TUF signs, which leaves every
//! signature valid.

use base64::Engine;
use base64::engine::general_purpose::STANDARD;
use c3_verify::trustroot::Policy;
use c3_verify::tuf::Verified;
use c3_verify::tuf_slot::Accepted;
use c3_verify::tuf_slot::TufSlotParts;
use ed25519_dalek::Signer;
use p256::ecdsa::signature::hazmat::PrehashSigner;
use serde_json::Value;
use serde_json::json;
use std::path::Path;

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn encode(v: &Value, out: &mut Vec<u8>) -> Result<(), String> {
    match v {
        Value::Null => out.extend_from_slice(b"null"),
        Value::Bool(b) => out.extend_from_slice(if *b { b"true" } else { b"false" }),
        Value::Number(n) => {
            let n = n
                .as_u64()
                .ok_or_else(|| format!("{n} isn't a natural number"))?;
            out.extend_from_slice(n.to_string().as_bytes());
        }
        Value::String(s) => {
            if s.contains(['"', '\\']) {
                return Err(format!("string {s:?} holds a quote or backslash"));
            }
            out.push(b'"');
            out.extend_from_slice(s.as_bytes());
            out.push(b'"');
        }
        Value::Array(items) => {
            out.push(b'[');
            for (i, item) in items.iter().enumerate() {
                if i > 0 {
                    out.push(b',');
                }
                encode(item, out)?;
            }
            out.push(b']');
        }
        Value::Object(members) => {
            let mut sorted: Vec<_> = members.iter().collect();
            sorted.sort_by(|a, b| a.0.as_bytes().cmp(b.0.as_bytes()));
            out.push(b'{');
            for (i, (k, v)) in sorted.into_iter().enumerate() {
                if i > 0 {
                    out.push(b',');
                }
                encode(&Value::String(k.clone()), out)?;
                out.push(b':');
                encode(v, out)?;
            }
            out.push(b'}');
        }
    }
    Ok(())
}

/// The canonical JSON encoding of `v`, as TUF signs it: sorted keys, no
/// whitespace, and natural numbers only. Strings that would need an escape
/// are rejected, because the device can't read them.
pub fn canonical_value(v: &Value) -> Result<Vec<u8>, String> {
    let mut out = Vec::new();
    encode(v, &mut out)?;
    Ok(out)
}

/// Re-encodes the JSON document `json`, ordinary or already canonical, as
/// canonical JSON.
pub fn canonical(json: &[u8]) -> Result<Vec<u8>, String> {
    let v: Value = serde_json::from_slice(&escape_controls(json)).map_err(|e| e.to_string())?;
    canonical_value(&v)
}

/// Escapes the raw control characters, such as a PEM key's newlines, that
/// canonical JSON leaves in strings and ordinary JSON doesn't allow.
fn escape_controls(json: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(json.len());
    let (mut in_string, mut escaped) = (false, false);
    for &b in json {
        if in_string && b < 0x20 {
            out.extend_from_slice(format!("\\u{b:04x}").as_bytes());
            continue;
        }
        out.push(b);
        if escaped {
            escaped = false;
        } else if in_string && b == b'\\' {
            escaped = true;
        } else if b == b'"' {
            in_string = !in_string;
        }
    }
    out
}

/// The canonical form of a root to compile into the bootloader.
pub fn pinned_root(json: &[u8]) -> Result<Vec<u8>, String> {
    let root = canonical(json)?;
    c3_verify::tuf::parse_root(&root).map_err(|e| format!("pinned root: {e:?}"))?;
    Ok(root)
}

/// Builds the TUF part of a slot from documents already in their final
/// form: the magic `C3TU`, version 2, the root count, an index of 4-byte
/// lengths for each root, `targets.json`, and `trusted_root.json`, then the
/// documents in that order.
pub fn container(roots: &[Vec<u8>], targets: &[u8], trusted_root: &[u8]) -> Vec<u8> {
    let docs: Vec<&[u8]> = roots
        .iter()
        .map(Vec::as_slice)
        .chain([targets, trusted_root])
        .collect();
    let mut out = c3_verify::tuf::TUF_MAGIC.to_vec();
    out.extend_from_slice(&2u16.to_le_bytes());
    out.extend_from_slice(&(roots.len() as u16).to_le_bytes());
    for doc in &docs {
        out.extend_from_slice(&(doc.len() as u32).to_le_bytes());
    }
    for doc in docs {
        out.extend_from_slice(doc);
    }
    out
}

fn tuf_len(tuf: &[u8]) -> Result<u32, String> {
    u32::try_from(tuf.len()).map_err(|e| e.to_string())
}

/// Builds the TUF part of a slot from metadata as Sigstore publishes it:
/// the roots after the pinned one in version order, `targets.json`, and
/// `trusted_root.json`, which is kept byte for byte because `targets.json`
/// lists its digest.
pub fn package(roots: &[Vec<u8>], targets: &[u8], trusted_root: &[u8]) -> Result<Vec<u8>, String> {
    let roots = roots
        .iter()
        .map(|r| canonical(r))
        .collect::<Result<Vec<_>, _>>()?;
    if roots.len() > c3_verify::tuf::MAX_ROOTS {
        return Err(format!(
            "{} new roots, and a slot holds at most {}",
            roots.len(),
            c3_verify::tuf::MAX_ROOTS
        ));
    }
    let targets = canonical(targets)?;
    let max_doc = c3_verify::tuf::MAX_DOC_LEN as usize;
    for (name, doc) in roots
        .iter()
        .enumerate()
        .map(|(i, r)| (format!("root {}", i + 1), r.as_slice()))
        .chain([
            ("targets.json".to_string(), targets.as_slice()),
            ("trusted_root.json".to_string(), trusted_root),
        ])
    {
        if doc.len() > max_doc {
            return Err(format!(
                "{name} is {} bytes, and the device reads at most {max_doc}",
                doc.len()
            ));
        }
    }
    let out = container(&roots, &targets, trusted_root);
    let max = c3_verify::tuf::MAX_TUF_LEN as usize;
    if out.len() > max {
        return Err(format!(
            "the TUF part is {} bytes, and a slot holds at most {max}",
            out.len()
        ));
    }
    c3_verify::tuf::read_index(&mut out.as_slice(), tuf_len(&out)?)
        .map_err(|e| format!("TUF part: {e:?}"))?;
    Ok(out)
}

/// Checks the TUF part of a slot from `pinned` with the device's code,
/// reading one document at a time as the bootloader does.
pub fn verify(pinned: &[u8], tuf: &[u8]) -> Result<Verified, String> {
    let mut doc = vec![0u8; c3_verify::tuf::MAX_DOC_LEN as usize];
    let (verified, _) = c3_verify::tuf::verify(pinned, &mut &tuf[..], tuf_len(tuf)?, &mut doc)
        .map_err(|e| format!("{e:?}"))?;
    Ok(verified)
}

/// Checks a slot's image, bundle container, and TUF part with the device's
/// code, from `pinned`, with the release identity `policy`: issuer, Build
/// Signer URI, repository ID, owner ID, and trigger.
pub fn accept(
    image: &[u8],
    bundle: &[u8],
    tuf: &[u8],
    pinned: &[u8],
    policy: &[String; 5],
    efuse_level: u8,
) -> Result<Accepted, String> {
    let [issuer, build_signer_uri, repository_id, owner_id, trigger] = policy;
    let policy = Policy {
        issuer: issuer.as_bytes(),
        build_signer_uri: build_signer_uri.as_bytes(),
        repository_id: repository_id.as_bytes(),
        owner_id: owner_id.as_bytes(),
        trigger: trigger.as_bytes(),
    };
    let slot = TufSlotParts {
        image_header: image,
        image_length: u32::try_from(image.len()).map_err(|e| e.to_string())?,
        image_digest: c3_crypto::sha256(image),
        bundle,
        tuf,
        tuf_length: tuf_len(tuf)?,
    };
    let max_doc = c3_verify::tuf::MAX_DOC_LEN as usize;
    let mut doc = vec![0u8; max_doc];
    let mut buf = vec![0u8; c3_verify::trusted_root::buffer_len(max_doc)];
    c3_verify::tuf_slot::accept_slot(slot, pinned, &policy, efuse_level, &mut doc, &mut buf)
        .map_err(|e| format!("{e:?}"))
}

/// A key that signs synthetic TUF metadata in tests.
pub enum TestKey {
    /// An ECDSA P-256 key, `ecdsa-sha2-nistp256`.
    P256(p256::ecdsa::SigningKey),
    /// An ECDSA P-384 key, `ecdsa-sha2-nistp384`.
    P384(p384::ecdsa::SigningKey),
    /// An Ed25519 key.
    Ed25519(ed25519_dalek::SigningKey),
}

fn pem(spki: &[u8]) -> String {
    let text = STANDARD.encode(spki);
    let mut out = String::from("-----BEGIN PUBLIC KEY-----\n");
    for line in text.as_bytes().chunks(64) {
        out.push_str(std::str::from_utf8(line).unwrap_or_default());
        out.push('\n');
    }
    out.push_str("-----END PUBLIC KEY-----\n");
    out
}

fn der_integer(bytes: &[u8]) -> Vec<u8> {
    let start = bytes.iter().position(|&b| b != 0).unwrap_or(bytes.len());
    let mut content = bytes[start..].to_vec();
    if content.first().is_none_or(|&b| b & 0x80 != 0) {
        content.insert(0, 0);
    }
    let mut out = vec![0x02, content.len() as u8];
    out.extend(content);
    out
}

fn der_signature(r: &[u8], s: &[u8]) -> Vec<u8> {
    let body = [der_integer(r), der_integer(s)].concat();
    let mut out = vec![0x30, body.len() as u8];
    out.extend(body);
    out
}

impl TestKey {
    /// A P-256 key from `seed`, which must be a valid scalar.
    pub fn p256(seed: u8) -> Self {
        let key = p256::ecdsa::SigningKey::from_slice(&[seed; 32]).expect("valid P-256 scalar");
        TestKey::P256(key)
    }

    /// A P-384 key from `seed`, which must be a valid scalar.
    pub fn p384(seed: u8) -> Self {
        let key = p384::ecdsa::SigningKey::from_slice(&[seed; 48]).expect("valid P-384 scalar");
        TestKey::P384(key)
    }

    /// An Ed25519 key from `seed`.
    pub fn ed25519(seed: u8) -> Self {
        TestKey::Ed25519(ed25519_dalek::SigningKey::from_bytes(&[seed; 32]))
    }

    /// A P-256 key from a file that holds its 32-byte scalar in hex.
    pub fn read_p256(path: &Path) -> Result<Self, String> {
        let text = std::fs::read_to_string(path).map_err(|e| format!("{}: {e}", path.display()))?;
        let text = text.trim();
        if text.len() != 64 || !text.bytes().all(|b| b.is_ascii_hexdigit()) {
            return Err(format!("{}: a seed is 64 hex characters", path.display()));
        }
        p256::ecdsa::SigningKey::from_slice(&hex_bytes(text))
            .map(TestKey::P256)
            .map_err(|e| format!("{}: {e}", path.display()))
    }

    /// The key's TUF key object.
    pub fn key_json(&self) -> Value {
        let (keytype, scheme, public) = match self {
            TestKey::P256(k) => {
                let point = k.verifying_key().to_sec1_point(false);
                let spki = [
                    hex_bytes("3059301306072a8648ce3d020106082a8648ce3d030107034200"),
                    point.as_bytes().to_vec(),
                ]
                .concat();
                ("ecdsa", "ecdsa-sha2-nistp256", pem(&spki))
            }
            TestKey::P384(k) => {
                let point = k.verifying_key().to_sec1_point(false);
                let spki = [
                    hex_bytes("3076301006072a8648ce3d020106052b81040022036200"),
                    point.as_bytes().to_vec(),
                ]
                .concat();
                ("ecdsa", "ecdsa-sha2-nistp384", pem(&spki))
            }
            TestKey::Ed25519(k) => ("ed25519", "ed25519", hex(&k.verifying_key().to_bytes())),
        };
        json!({"keytype": keytype, "scheme": scheme, "keyval": {"public": public}})
    }

    /// The key's ID: the SHA-256 digest of its canonical key object, in
    /// lowercase hex.
    pub fn keyid(&self) -> String {
        let canonical = canonical_value(&self.key_json()).unwrap_or_default();
        hex(&c3_crypto::sha256(&canonical))
    }

    /// The key's signature over `message`, in lowercase hex.
    pub fn sign(&self, message: &[u8]) -> String {
        match self {
            TestKey::P256(k) => {
                let sig: p256::ecdsa::Signature = k
                    .sign_prehash(&c3_crypto::sha256(message))
                    .expect("P-256 signs a digest");
                let (r, s) = sig.split_bytes();
                hex(&der_signature(&r, &s))
            }
            TestKey::P384(k) => {
                let sig: p384::ecdsa::Signature = k
                    .sign_prehash(&c3_crypto::sha384(message))
                    .expect("P-384 signs a digest");
                let (r, s) = sig.split_bytes();
                hex(&der_signature(&r, &s))
            }
            TestKey::Ed25519(k) => hex(&k.sign(message).to_bytes()),
        }
    }
}

fn hex_bytes(text: &str) -> Vec<u8> {
    (0..text.len() / 2)
        .map(|i| u8::from_str_radix(&text[2 * i..2 * i + 2], 16).unwrap_or(0))
        .collect()
}

/// The `signed` object of a synthetic root: version `version`, expiring at
/// `expires`, with `root` signing roots and `targets` signing targets.
/// The snapshot and timestamp roles reuse the targets keys.
pub fn root_signed(
    version: u64,
    expires: &str,
    root: (&[&TestKey], u64),
    targets: (&[&TestKey], u64),
) -> Value {
    let mut keys = serde_json::Map::new();
    for k in root.0.iter().chain(targets.0) {
        keys.insert(k.keyid(), k.key_json());
    }
    let role = |(ks, threshold): (&[&TestKey], u64)| json!({"keyids": ks.iter().map(|k| k.keyid()).collect::<Vec<_>>(), "threshold": threshold});
    json!({
        "_type": "root",
        "consistent_snapshot": true,
        "expires": expires,
        "keys": keys,
        "roles": {
            "root": role(root),
            "snapshot": role(targets),
            "targets": role(targets),
            "timestamp": role(targets),
        },
        "spec_version": "1.0",
        "version": version,
    })
}

/// The `signed` object of a synthetic `targets.json` that lists
/// `trusted_root`.
pub fn targets_signed(version: u64, expires: &str, trusted_root: &[u8]) -> Value {
    json!({
        "_type": "targets",
        "expires": expires,
        "spec_version": "1.0",
        "targets": {
            "trusted_root.json": {
                "hashes": {"sha256": hex(&c3_crypto::sha256(trusted_root))},
                "length": trusted_root.len(),
            },
        },
        "version": version,
    })
}

/// A canonical metadata document: `signed` with each signer's signature
/// over its canonical form.
pub fn sign_metadata(signed: &Value, signers: &[&TestKey]) -> Result<Vec<u8>, String> {
    let message = canonical_value(signed)?;
    let signatures: Vec<Value> = signers
        .iter()
        .map(|k| json!({"keyid": k.keyid(), "sig": k.sign(&message)}))
        .collect();
    canonical_value(&json!({"signatures": signatures, "signed": signed}))
}

/// When the development repository's metadata expires.
pub const DEV_EXPIRES: &str = "2099-12-31T23:59:59Z";

/// The keys of the development TUF repository, which stands in for
/// Sigstore's in development builds and QEMU runs. Their seeds are public.
pub struct DevKeys {
    root: [TestKey; 3],
    targets: [TestKey; 2],
}

impl DevKeys {
    /// Reads `tuf-dev-root-{1,2,3}.seed` and `tuf-dev-targets-{1,2}.seed`
    /// from `dir`.
    pub fn read(dir: &Path) -> Result<Self, String> {
        let key = |name: &str| TestKey::read_p256(&dir.join(format!("tuf-dev-{name}.seed")));
        Ok(DevKeys {
            root: [key("root-1")?, key("root-2")?, key("root-3")?],
            targets: [key("targets-1")?, key("targets-2")?],
        })
    }

    fn targets_key(&self, root_version: u64) -> Result<&TestKey, String> {
        match root_version {
            1 => Ok(&self.targets[0]),
            2 => Ok(&self.targets[1]),
            _ => Err(format!(
                "the development roots are versions 1 and 2, not {root_version}"
            )),
        }
    }

    /// Root version 1 or 2. Both name the three root keys with threshold
    /// 2 and are signed by root keys 1 and 2. Version 1 trusts targets key
    /// 1, and version 2 rotates to targets key 2.
    pub fn root(&self, version: u64) -> Result<Vec<u8>, String> {
        let root: Vec<&TestKey> = self.root.iter().collect();
        let signed = root_signed(
            version,
            DEV_EXPIRES,
            (&root, 2),
            (&[self.targets_key(version)?], 1),
        );
        sign_metadata(&signed, &root[..2])
    }

    /// A `targets.json` that lists `trusted_root`, signed by the targets key
    /// that root `root_version` trusts.
    pub fn targets(
        &self,
        root_version: u64,
        trusted_root: &[u8],
        expires: &str,
    ) -> Result<Vec<u8>, String> {
        let signed = targets_signed(1, expires, trusted_root);
        sign_metadata(&signed, &[self.targets_key(root_version)?])
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const KEYS: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/../testdata/keys");

    #[test]
    fn canonical_json_reencodes_to_itself() {
        let root = std::fs::read(Path::new(KEYS).join("tuf-dev-root.json")).unwrap();
        assert!(root.contains(&b'\n'));
        assert_eq!(canonical(&root).unwrap(), root);
        let pinned = include_bytes!("../../release/pinned-root.json");
        assert_eq!(
            canonical(include_bytes!("../../testdata/tuf/16.root.json")).unwrap(),
            pinned
        );
    }

    #[test]
    fn package_enforces_the_device_limits() {
        let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../testdata/tuf");
        let read = |name: &str| std::fs::read(dir.join(name)).unwrap();
        let roots: Vec<_> = (5..=16).map(|v| read(&format!("{v}.root.json"))).collect();
        let (targets, trusted) = (read("targets.json"), read("trusted_root.json"));
        assert!(package(&roots, &targets, &trusted).is_ok());
        let many = vec![roots[0].clone(); c3_verify::tuf::MAX_ROOTS + 1];
        let err = package(&many, &targets, &trusted).unwrap_err();
        assert!(err.contains("at most 64"), "{err}");
        let long = format!(r#"{{"pad":"{}"}}"#, "x".repeat(10_240));
        let err = package(&[long.into_bytes()], &targets, &trusted).unwrap_err();
        assert!(err.contains("root 1 is 10250 bytes"), "{err}");
    }

    #[test]
    fn the_committed_development_root_is_current() {
        let keys = DevKeys::read(Path::new(KEYS)).unwrap();
        let committed = std::fs::read(Path::new(KEYS).join("tuf-dev-root.json")).unwrap();
        assert_eq!(keys.root(1).unwrap(), committed, "run c3-ota tuf-dev-root");
    }

    #[test]
    fn the_development_repository_rotates_its_targets_key() {
        let keys = DevKeys::read(Path::new(KEYS)).unwrap();
        let pinned = keys.root(1).unwrap();
        let trusted = include_bytes!("../../release/trusted_root.json");
        let v1 = keys.targets(1, trusted, DEV_EXPIRES).unwrap();
        let v2 = keys.targets(2, trusted, DEV_EXPIRES).unwrap();
        let root2 = keys.root(2).unwrap();
        let check = |roots: &[Vec<u8>], targets: &[u8]| {
            verify(&pinned, &container(roots, targets, trusted)).map(|v| v.root_version)
        };
        assert_eq!(check(&[], &v1), Ok(1));
        assert_eq!(check(std::slice::from_ref(&root2), &v2), Ok(2));
        assert_eq!(check(&[], &v2), Err("Threshold".into()));
        assert_eq!(check(&[root2], &v1), Err("Threshold".into()));
    }
}

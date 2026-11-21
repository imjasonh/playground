//! The Fulcio leaf certificate, checked against the leaf certificate profile
//! in `docs/formats.md`.

use crate::der;
use crate::der::CONTEXT_0;
use crate::der::CONTEXT_3;
use crate::der::Der;
use crate::der::GENERALIZED_TIME;
use crate::der::OID;
use crate::der::SEQUENCE;
use crate::der::UTC_TIME;
use crate::der::UTF8_STRING;
use crate::error::Error;
use crate::time;
use crate::trustroot::FulcioIntermediate;

/// `ecdsa-with-SHA384`, 1.2.840.10045.4.3.3.
const ECDSA_WITH_SHA384: &[u8] = &[0x2a, 0x86, 0x48, 0xce, 0x3d, 0x04, 0x03, 0x03];
/// `id-ecPublicKey`, 1.2.840.10045.2.1.
const EC_PUBLIC_KEY: &[u8] = &[0x2a, 0x86, 0x48, 0xce, 0x3d, 0x02, 0x01];
/// `prime256v1`, 1.2.840.10045.3.1.7.
const PRIME256V1: &[u8] = &[0x2a, 0x86, 0x48, 0xce, 0x3d, 0x03, 0x01, 0x07];
/// `keyUsage`, 2.5.29.15.
const KEY_USAGE: &[u8] = &[0x55, 0x1d, 0x0f];
/// `subjectAltName`, 2.5.29.17.
const SUBJECT_ALT_NAME: &[u8] = &[0x55, 0x1d, 0x11];
/// `basicConstraints`, 2.5.29.19.
const BASIC_CONSTRAINTS: &[u8] = &[0x55, 0x1d, 0x13];
/// `extKeyUsage`, 2.5.29.37.
const EXT_KEY_USAGE: &[u8] = &[0x55, 0x1d, 0x25];
/// `codeSigning`, 1.3.6.1.5.5.7.3.3.
const CODE_SIGNING: &[u8] = &[0x2b, 0x06, 0x01, 0x05, 0x05, 0x07, 0x03, 0x03];
/// The identity-policy extensions, in the order of the identity policy table:
/// 1.3.6.1.4.1.57264.1.8, .1.9, .1.15, .1.17, and .1.20.
const POLICY_OIDS: [&[u8]; 5] = [
    &[0x2b, 0x06, 0x01, 0x04, 0x01, 0x83, 0xbf, 0x30, 0x01, 0x08],
    &[0x2b, 0x06, 0x01, 0x04, 0x01, 0x83, 0xbf, 0x30, 0x01, 0x09],
    &[0x2b, 0x06, 0x01, 0x04, 0x01, 0x83, 0xbf, 0x30, 0x01, 0x0f],
    &[0x2b, 0x06, 0x01, 0x04, 0x01, 0x83, 0xbf, 0x30, 0x01, 0x11],
    &[0x2b, 0x06, 0x01, 0x04, 0x01, 0x83, 0xbf, 0x30, 0x01, 0x14],
];
/// The extensions that may be marked critical.
const CRITICAL_ALLOWED: [&[u8]; 4] = [
    KEY_USAGE,
    SUBJECT_ALT_NAME,
    BASIC_CONSTRAINTS,
    EXT_KEY_USAGE,
];
/// The longest serial number, in content bytes.
const MAX_SERIAL_LEN: usize = 20;
/// The length of an uncompressed SEC1 P-256 point.
const P256_POINT_LEN: usize = 65;

/// A leaf certificate that fits the profile. Its signature hasn't been
/// checked; [`verify_leaf`] does that.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Leaf<'a> {
    /// The whole `tbsCertificate` element, the bytes the issuer signed.
    pub tbs: &'a [u8],
    /// The whole issuer `Name` element.
    pub issuer: &'a [u8],
    /// The first second the certificate is valid, since the Unix epoch.
    pub not_before: u64,
    /// The last second the certificate is valid, since the Unix epoch.
    pub not_after: u64,
    /// The subject's P-256 public key, uncompressed SEC1.
    pub public_key: &'a [u8; P256_POINT_LEN],
    /// The issuer's signature `(r, s)`, as 48-byte big-endian numbers.
    pub signature: ([u8; 48], [u8; 48]),
    /// The contents of the Issuer (V2) extension's `UTF8String`.
    pub issuer_v2: &'a [u8],
    /// The contents of the Build Signer URI extension's `UTF8String`.
    pub build_signer_uri: &'a [u8],
    /// The contents of the Source Repository Identifier extension's
    /// `UTF8String`.
    pub repository_id: &'a [u8],
    /// The contents of the Source Repository Owner Identifier extension's
    /// `UTF8String`.
    pub owner_id: &'a [u8],
    /// The contents of the Build Trigger extension's `UTF8String`.
    pub trigger: &'a [u8],
}

/// Reads a `UTCTime` or `GeneralizedTime`.
fn read_time(d: &mut Der<'_>) -> Result<u64, Error> {
    match d.peek_tag() {
        Some(UTC_TIME) => time::utc_time(d.tlv()?.content),
        Some(GENERALIZED_TIME) => time::generalized_time(d.tlv()?.content),
        Some(_) => Err(Error::BadDer),
        None => Err(Error::Truncated),
    }
}

/// Reads a `SubjectPublicKeyInfo` and returns its P-256 point.
fn read_public_key<'a>(d: &mut Der<'a>) -> Result<&'a [u8; P256_POINT_LEN], Error> {
    let mut spki = d.sequence()?;
    let (algorithm, params) = spki.algorithm()?;
    let curve_ok = params.is_some_and(|p| p.tag == OID && p.content == PRIME256V1);
    if algorithm != EC_PUBLIC_KEY || !curve_ok {
        return Err(Error::BadCertificate);
    }
    let point: &[u8; P256_POINT_LEN] = spki
        .bit_string()?
        .try_into()
        .map_err(|_| Error::BadCertificate)?;
    spki.finish()?;
    if !c3_crypto::p256_public_key_ok(point) {
        return Err(Error::BadKey);
    }
    Ok(point)
}

/// Checks a `KeyUsage` value and reports whether `digitalSignature` is set.
fn has_digital_signature(value: &[u8]) -> Result<bool, Error> {
    let mut d = Der::new(value);
    let bits = d.named_bits()?;
    d.finish()?;
    Ok(bits.first().is_some_and(|b| b & 0x80 != 0))
}

/// Checks an `ExtKeyUsageSyntax` value and reports whether it lists
/// `codeSigning`.
fn has_code_signing(value: &[u8]) -> Result<bool, Error> {
    let mut d = Der::new(value);
    let mut purposes = d.sequence()?;
    d.finish()?;
    let mut found = false;
    while !purposes.is_empty() {
        found |= purposes.oid()? == CODE_SIGNING;
    }
    Ok(found)
}

/// Checks a `BasicConstraints` value and reports whether it sets `cA`.
fn is_ca(value: &[u8]) -> Result<bool, Error> {
    let mut d = Der::new(value);
    let mut constraints = d.sequence()?;
    d.finish()?;
    let ca = constraints.peek_tag() == Some(der::BOOLEAN);
    if ca {
        constraints.boolean_true()?;
    }
    if constraints.peek_tag() == Some(der::INTEGER) {
        constraints.integer()?;
    }
    constraints.finish()?;
    Ok(ca)
}

/// Returns the contents of an identity-policy value, which must be one
/// `UTF8String` that fills it.
fn policy_string(value: &[u8]) -> Result<&[u8], Error> {
    let mut d = Der::new(value);
    let s = d.tlv()?;
    if s.tag != UTF8_STRING {
        return Err(Error::BadExtension);
    }
    d.finish()?;
    Ok(s.content)
}

/// Checks the extensions against the extension rules and returns the five
/// identity-policy strings in table order.
fn read_extensions(content: &[u8]) -> Result<[&[u8]; 5], Error> {
    let mut outer = Der::new(content);
    let list = outer.element(SEQUENCE)?.content;
    outer.finish()?;
    let mut extensions = Der::new(list);
    let mut key_usage = false;
    let mut code_signing = false;
    let mut policy: [Option<&[u8]>; 5] = [None; 5];
    while !extensions.is_empty() {
        let earlier = extensions.consumed()?;
        let mut extension = extensions.sequence()?;
        let oid = extension.oid()?;
        let critical = extension.peek_tag() == Some(der::BOOLEAN);
        if critical {
            extension.boolean_true()?;
        }
        let value = extension.octet_string()?;
        extension.finish()?;
        if der::lists_oid(earlier, oid)? {
            return Err(Error::BadExtension);
        }
        if critical && !CRITICAL_ALLOWED.contains(&oid) {
            return Err(Error::BadExtension);
        }
        if oid == KEY_USAGE {
            if !has_digital_signature(value)? {
                return Err(Error::BadExtension);
            }
            key_usage = true;
        } else if oid == EXT_KEY_USAGE {
            if !has_code_signing(value)? {
                return Err(Error::BadExtension);
            }
            code_signing = true;
        } else if oid == BASIC_CONSTRAINTS {
            if is_ca(value)? {
                return Err(Error::BadExtension);
            }
        } else if let Some((_, slot)) = POLICY_OIDS
            .iter()
            .zip(policy.iter_mut())
            .find(|(policy_oid, _)| **policy_oid == oid)
        {
            *slot = Some(policy_string(value)?);
        }
    }
    match policy {
        [Some(a), Some(b), Some(c), Some(d), Some(e)] if key_usage && code_signing => {
            Ok([a, b, c, d, e])
        }
        _ => Err(Error::BadExtension),
    }
}

/// Parses a DER leaf certificate and checks it against the leaf certificate
/// profile.
///
/// The certificate's signature isn't checked here; [`verify_leaf`] checks it.
pub fn parse_leaf(der: &[u8]) -> Result<Leaf<'_>, Error> {
    let mut input = Der::new(der);
    let mut certificate = input.sequence()?;
    input.finish()?;
    let tbs = certificate.element(SEQUENCE)?;
    let outer_algorithm = certificate.element(SEQUENCE)?;
    let signature_value = certificate.bit_string()?;
    certificate.finish()?;

    let mut t = Der::new(tbs.content);
    let version = t.optional(CONTEXT_0)?.ok_or(Error::BadCertificate)?;
    let mut version = Der::new(version.content);
    if !version.integer_is(2)? {
        return Err(Error::BadCertificate);
    }
    version.finish()?;
    if t.positive_integer()?.len() > MAX_SERIAL_LEN {
        return Err(Error::BadCertificate);
    }
    let algorithm = t.element(SEQUENCE)?;
    let (algorithm_oid, params) = Der::new(algorithm.raw).algorithm()?;
    if algorithm_oid != ECDSA_WITH_SHA384 || params.is_some() {
        return Err(Error::BadCertificate);
    }
    let issuer = t.element(SEQUENCE)?.raw;
    let mut validity = t.sequence()?;
    let not_before = read_time(&mut validity)?;
    let not_after = read_time(&mut validity)?;
    validity.finish()?;
    t.element(SEQUENCE)?;
    let public_key = read_public_key(&mut t)?;
    let extensions = t.optional(CONTEXT_3)?.ok_or(Error::BadCertificate)?;
    t.finish()?;
    let [
        issuer_v2,
        build_signer_uri,
        repository_id,
        owner_id,
        trigger,
    ] = read_extensions(extensions.content)?;

    if outer_algorithm.raw != algorithm.raw {
        return Err(Error::BadCertificate);
    }
    let signature = der::ecdsa_signature::<48>(signature_value)?;
    Ok(Leaf {
        tbs: tbs.raw,
        issuer,
        not_before,
        not_after,
        public_key,
        signature,
        issuer_v2,
        build_signer_uri,
        repository_id,
        owner_id,
        trigger,
    })
}

/// Checks that `intermediate` issued and signed `leaf`.
///
/// Fails with [`Error::NoMatchingKey`] if the leaf's issuer isn't the
/// intermediate's subject, and with [`Error::BadSignature`] if the signature
/// over the `tbsCertificate` doesn't verify. Validity windows are the caller's
/// to check.
pub fn verify_leaf(leaf: &Leaf<'_>, intermediate: &FulcioIntermediate<'_>) -> Result<(), Error> {
    if leaf.issuer != intermediate.subject {
        return Err(Error::NoMatchingKey);
    }
    let digest = c3_crypto::sha384(leaf.tbs);
    let (r, s) = &leaf.signature;
    if c3_crypto::p384_verify_prehash(intermediate.public_key, &digest, r, s) {
        Ok(())
    } else {
        Err(Error::BadSignature)
    }
}

#[cfg(test)]
#[allow(clippy::arithmetic_side_effects, clippy::indexing_slicing)]
mod tests {
    use super::*;
    use crate::der::INTEGER;
    use crate::der::OCTET_STRING;
    use crate::der::tests::all_bundles;
    use crate::der::tests::at;
    use crate::der::tests::edit;
    use crate::der::tests::happy_path;
    use crate::der::tests::seq;
    use crate::der::tests::subject_and_p384_key;
    use crate::der::tests::tlv;
    use crate::der::tests::trusted_certificates;
    use crate::trustroot::Window;

    /// The path from the certificate to its list of extensions.
    const EXTENSIONS: [usize; 3] = [0, 7, 0];

    fn leaf() -> Vec<u8> {
        happy_path().leaf
    }

    fn ext(oid: &[u8], critical: Option<u8>, value: &[u8]) -> Vec<u8> {
        let mut parts = vec![tlv(OID, oid)];
        if let Some(c) = critical {
            parts.push(tlv(der::BOOLEAN, &[c]));
        }
        parts.push(tlv(OCTET_STRING, value));
        tlv(SEQUENCE, &parts.concat())
    }

    /// The OID contents of an encoded extension.
    fn ext_oid(e: &[u8]) -> Vec<u8> {
        Der::new(e).sequence().unwrap().oid().unwrap().to_vec()
    }

    fn edit_extensions<F: FnOnce(&mut Vec<Vec<u8>>)>(f: F) -> Vec<u8> {
        edit(&leaf(), &EXTENSIONS, f)
    }

    fn replace_extension(oid: &[u8], new: Vec<u8>) -> Vec<u8> {
        edit_extensions(|list| {
            let i = list.iter().position(|e| ext_oid(e) == oid).unwrap();
            list[i] = new;
        })
    }

    fn remove_extension(oid: &[u8]) -> Vec<u8> {
        edit_extensions(|list| list.retain(|e| ext_oid(e) != oid))
    }

    fn intermediate_parts() -> (Vec<u8>, [u8; 97]) {
        subject_and_p384_key(&trusted_certificates().0)
    }

    const ANY_TIME: Window = Window {
        not_before: 0,
        not_after: u64::MAX,
    };

    #[test]
    fn parses_real_leaf() {
        let der = leaf();
        let l = parse_leaf(&der).unwrap();
        assert_eq!(l.issuer_v2, b"https://token.actions.githubusercontent.com");
        assert_eq!(
            l.build_signer_uri,
            &b"https://github.com/sigstore-conformance/extremely-dangerous-public-oidc-beacon/.github/workflows/extremely-dangerous-oidc-beacon.yml@refs/heads/main"[..]
        );
        assert_eq!(l.repository_id, b"632596897");
        assert_eq!(l.owner_id, b"131804563");
        assert_eq!(l.trigger, b"workflow_dispatch");
        assert_eq!(l.not_before, 1_749_729_736);
        assert_eq!(l.not_after, l.not_before + 600);
        assert_eq!(l.tbs, &at(&der, &[0])[..]);
        assert_eq!(l.issuer, &at(&der, &[0, 3])[..]);
        assert_eq!(l.public_key[0], 0x04);
    }

    #[test]
    fn verifies_real_leaf() {
        let (subject, key) = intermediate_parts();
        let intermediate = FulcioIntermediate {
            subject: &subject,
            public_key: &key,
            window: ANY_TIME,
        };
        let der = leaf();
        let l = parse_leaf(&der).unwrap();
        assert_eq!(verify_leaf(&l, &intermediate), Ok(()));

        let mut tampered = der.clone();
        tampered[30] ^= 1;
        let t = parse_leaf(&tampered).unwrap();
        assert_eq!(verify_leaf(&t, &intermediate), Err(Error::BadSignature));

        let (_, tsa_key) = subject_and_p384_key(&trusted_certificates().1);
        let wrong_key = FulcioIntermediate {
            public_key: &tsa_key,
            ..intermediate
        };
        assert_eq!(verify_leaf(&l, &wrong_key), Err(Error::BadSignature));
        let wrong_subject = FulcioIntermediate {
            subject: &subject[..subject.len() - 1],
            ..intermediate
        };
        assert_eq!(verify_leaf(&l, &wrong_subject), Err(Error::NoMatchingKey));
    }

    #[test]
    fn parses_every_conformance_leaf() {
        for (name, f) in all_bundles() {
            assert!(parse_leaf(&f.leaf).is_ok(), "{name}");
        }
    }

    #[test]
    fn rejects_trailing_and_truncated_certificates() {
        let mut der = leaf();
        der.push(0);
        assert_eq!(parse_leaf(&der), Err(Error::TrailingBytes));
        der.truncate(der.len() - 2);
        assert_eq!(parse_leaf(&der), Err(Error::Truncated));
    }

    #[test]
    fn rejects_explicit_false_critical_flag() {
        let value = at(&leaf(), &[0, 7, 0, 1, 1]);
        let der = replace_extension(EXT_KEY_USAGE, ext(EXT_KEY_USAGE, Some(0x00), &value[2..]));
        assert_eq!(parse_leaf(&der), Err(Error::BadDer));
    }

    #[test]
    fn rejects_unknown_critical_extension() {
        let der =
            edit_extensions(|list| list.push(ext(&[0x55, 0x1d, 0x20], Some(0xff), &[0x30, 0x00])));
        assert_eq!(parse_leaf(&der), Err(Error::BadExtension));
        let der = edit_extensions(|list| list.push(ext(&[0x55, 0x1d, 0x20], None, &[0x30, 0x00])));
        assert!(parse_leaf(&der).is_ok());
    }

    #[test]
    fn rejects_duplicate_extension() {
        let der = edit_extensions(|list| {
            let last = list.last().unwrap().clone();
            list.push(last);
        });
        assert_eq!(parse_leaf(&der), Err(Error::BadExtension));
        let der = edit_extensions(|list| {
            let first = list[0].clone();
            list.push(first);
        });
        assert_eq!(parse_leaf(&der), Err(Error::BadExtension));
    }

    #[test]
    fn requires_key_usage_with_digital_signature() {
        assert_eq!(
            parse_leaf(&remove_extension(KEY_USAGE)),
            Err(Error::BadExtension)
        );
        let encipherment = tlv(der::BIT_STRING, &[0x05, 0x20]);
        let der = replace_extension(KEY_USAGE, ext(KEY_USAGE, Some(0xff), &encipherment));
        assert_eq!(parse_leaf(&der), Err(Error::BadExtension));
    }

    #[test]
    fn requires_code_signing() {
        assert_eq!(
            parse_leaf(&remove_extension(EXT_KEY_USAGE)),
            Err(Error::BadExtension)
        );
        let time_stamping = seq(&[&tlv(OID, &[0x2b, 0x06, 0x01, 0x05, 0x05, 0x07, 0x03, 0x08])]);
        let der = replace_extension(EXT_KEY_USAGE, ext(EXT_KEY_USAGE, None, &time_stamping));
        assert_eq!(parse_leaf(&der), Err(Error::BadExtension));
        let both = seq(&[
            &tlv(OID, &[0x2b, 0x06, 0x01, 0x05, 0x05, 0x07, 0x03, 0x08]),
            &tlv(OID, CODE_SIGNING),
        ]);
        let der = replace_extension(EXT_KEY_USAGE, ext(EXT_KEY_USAGE, None, &both));
        assert!(parse_leaf(&der).is_ok());
    }

    #[test]
    fn rejects_ca_basic_constraints() {
        let ca = seq(&[&tlv(der::BOOLEAN, &[0xff])]);
        let der = edit_extensions(|list| list.push(ext(BASIC_CONSTRAINTS, Some(0xff), &ca)));
        assert_eq!(parse_leaf(&der), Err(Error::BadExtension));
        let not_ca = seq(&[]);
        let der = edit_extensions(|list| list.push(ext(BASIC_CONSTRAINTS, Some(0xff), &not_ca)));
        assert!(parse_leaf(&der).is_ok());
        let explicit_false = seq(&[&tlv(der::BOOLEAN, &[0x00])]);
        let der = edit_extensions(|list| list.push(ext(BASIC_CONSTRAINTS, None, &explicit_false)));
        assert_eq!(parse_leaf(&der), Err(Error::BadDer));
    }

    #[test]
    fn requires_utf8_policy_strings() {
        for oid in POLICY_OIDS {
            assert_eq!(parse_leaf(&remove_extension(oid)), Err(Error::BadExtension));
        }
        let printable = tlv(0x13, b"632596897");
        let der = replace_extension(POLICY_OIDS[2], ext(POLICY_OIDS[2], None, &printable));
        assert_eq!(parse_leaf(&der), Err(Error::BadExtension));
        let mut two = tlv(UTF8_STRING, b"632596897");
        two.extend_from_slice(&tlv(UTF8_STRING, b"1"));
        let der = replace_extension(POLICY_OIDS[2], ext(POLICY_OIDS[2], None, &two));
        assert_eq!(parse_leaf(&der), Err(Error::TrailingBytes));
        let other = tlv(UTF8_STRING, b"1");
        let der = replace_extension(POLICY_OIDS[2], ext(POLICY_OIDS[2], None, &other));
        assert_eq!(parse_leaf(&der).unwrap().repository_id, b"1");
    }

    fn algorithm(oid: &[u8]) -> Vec<u8> {
        seq(&[&tlv(OID, oid)])
    }

    const ECDSA_WITH_SHA256: &[u8] = &[0x2a, 0x86, 0x48, 0xce, 0x3d, 0x04, 0x03, 0x02];

    #[test]
    fn rejects_wrong_signature_algorithm() {
        let mut der = edit(&leaf(), &[0], |tbs| tbs[2] = algorithm(ECDSA_WITH_SHA256));
        der = edit(&der, &[], |c| c[1] = algorithm(ECDSA_WITH_SHA256));
        assert_eq!(parse_leaf(&der), Err(Error::BadCertificate));
        let with_null = seq(&[&tlv(OID, ECDSA_WITH_SHA384), &tlv(der::NULL, &[])]);
        let mut der = edit(&leaf(), &[0], |tbs| tbs[2] = with_null.clone());
        der = edit(&der, &[], |c| c[1] = with_null);
        assert_eq!(parse_leaf(&der), Err(Error::BadCertificate));
    }

    #[test]
    fn rejects_mismatched_outer_algorithm() {
        let der = edit(&leaf(), &[], |c| c[1] = algorithm(ECDSA_WITH_SHA256));
        assert_eq!(parse_leaf(&der), Err(Error::BadCertificate));
    }

    #[test]
    fn requires_version_3() {
        let der = edit(&leaf(), &[0], |tbs| {
            tbs.remove(0);
        });
        assert_eq!(parse_leaf(&der), Err(Error::BadCertificate));
        let der = edit(&leaf(), &[0], |tbs| {
            tbs[0] = tlv(CONTEXT_0, &tlv(INTEGER, &[1]))
        });
        assert_eq!(parse_leaf(&der), Err(Error::BadCertificate));
    }

    #[test]
    fn checks_serial_numbers() {
        let der = edit(&leaf(), &[0], |tbs| tbs[1] = tlv(INTEGER, &[0x7f; 21]));
        assert_eq!(parse_leaf(&der), Err(Error::BadCertificate));
        let der = edit(&leaf(), &[0], |tbs| tbs[1] = tlv(INTEGER, &[0x7f; 20]));
        assert!(parse_leaf(&der).is_ok());
        let der = edit(&leaf(), &[0], |tbs| tbs[1] = tlv(INTEGER, &[0x80]));
        assert_eq!(parse_leaf(&der), Err(Error::BadDer));
        let der = edit(&leaf(), &[0], |tbs| tbs[1] = tlv(INTEGER, &[0x00, 0x01]));
        assert_eq!(parse_leaf(&der), Err(Error::BadDer));
    }

    #[test]
    fn checks_public_key() {
        let der = edit(&leaf(), &[0, 6], |spki| {
            let mut bits = spki[1].clone();
            let n = bits.len();
            bits[n - 1] ^= 1;
            spki[1] = bits;
        });
        assert_eq!(parse_leaf(&der), Err(Error::BadKey));
        let p384 = &[0x2b, 0x81, 0x04, 0x00, 0x22];
        let der = edit(&leaf(), &[0, 6, 0], |alg| alg[1] = tlv(OID, p384));
        assert_eq!(parse_leaf(&der), Err(Error::BadCertificate));
    }

    #[test]
    fn rejects_unique_ids_and_missing_extensions() {
        let der = edit(&leaf(), &[0], |tbs| tbs.insert(7, tlv(0x81, &[0x00, 0x01])));
        assert_eq!(parse_leaf(&der), Err(Error::BadCertificate));
        let der = edit(&leaf(), &[0], |tbs| {
            tbs.pop();
        });
        assert_eq!(parse_leaf(&der), Err(Error::BadCertificate));
    }

    #[test]
    fn rejects_bad_validity() {
        let der = edit(&leaf(), &[0, 4], |v| v[0] = tlv(UTC_TIME, b"250230120216Z"));
        assert_eq!(parse_leaf(&der), Err(Error::BadTime));
        let der = edit(&leaf(), &[0, 4], |v| {
            v[0] = tlv(GENERALIZED_TIME, b"20250612120216Z")
        });
        assert_eq!(parse_leaf(&der).unwrap().not_before, 1_749_729_736);
        let der = edit(&leaf(), &[0, 4], |v| {
            v[0] = tlv(OCTET_STRING, b"250612120216Z")
        });
        assert_eq!(parse_leaf(&der), Err(Error::BadDer));
    }

    #[test]
    fn rejects_bad_signature_value() {
        let der = edit(&leaf(), &[], |c| {
            let mut bits = c[2].clone();
            bits[2] = 1;
            c[2] = bits;
        });
        assert_eq!(parse_leaf(&der), Err(Error::BadDer));
        let der = edit(&leaf(), &[], |c| {
            c[2] = tlv(der::BIT_STRING, &[0x00, 0x30, 0x00])
        });
        assert_eq!(parse_leaf(&der), Err(Error::Truncated));
    }
}

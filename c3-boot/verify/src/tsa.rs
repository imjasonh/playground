//! The RFC 3161 timestamp, checked against the timestamp profile in
//! `docs/formats.md`.

use crate::der;
use crate::der::BOOLEAN;
use crate::der::CONTEXT_0;
use crate::der::CONTEXT_1;
use crate::der::Der;
use crate::der::GENERALIZED_TIME;
use crate::der::INTEGER;
use crate::der::SEQUENCE;
use crate::error::Error;
use crate::time;
use crate::trustroot::TsaSigner;

/// `signedData`, 1.2.840.113549.1.7.2.
const SIGNED_DATA: &[u8] = &[0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x07, 0x02];
/// `id-ct-TSTInfo`, 1.2.840.113549.1.9.16.1.4.
const TST_INFO: &[u8] = &[
    0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x09, 0x10, 0x01, 0x04,
];
/// `contentType`, 1.2.840.113549.1.9.3.
const CONTENT_TYPE: &[u8] = &[0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x09, 0x03];
/// `messageDigest`, 1.2.840.113549.1.9.4.
const MESSAGE_DIGEST: &[u8] = &[0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x09, 0x04];
/// `sha256`, 2.16.840.1.101.3.4.2.1.
const SHA256: &[u8] = &[0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x01];
/// `ecdsa-with-SHA256`, 1.2.840.10045.4.3.2.
const ECDSA_WITH_SHA256: &[u8] = &[0x2a, 0x86, 0x48, 0xce, 0x3d, 0x04, 0x03, 0x02];
/// The longest `TSTInfo` serial number without its sign byte: RFC 3161 TSA
/// users must accept integers up to 160 bits.
const MAX_SERIAL_MAGNITUDE: usize = 20;
/// The `SET OF` tag that replaces `[0]` when the signed attributes are hashed.
const SET_OF_TAG: u8 = 0x31;

/// A timestamp that fits the profile. Its signature and digests haven't been
/// checked; [`verify_timestamp`] does that.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Timestamp<'a> {
    /// The signed time `t`, in seconds since the Unix epoch.
    pub gen_time: u64,
    /// The `TSTInfo`'s `messageImprint` digest.
    pub message_imprint: &'a [u8; 32],
    /// The DER `TSTInfo`, the contents of the `eContent` `OCTET STRING`.
    pub tst_info: &'a [u8],
    /// The signed `messageDigest` attribute.
    pub message_digest: &'a [u8; 32],
    /// The whole `sid` element, an `IssuerAndSerialNumber`.
    pub signer_id: &'a [u8],
    /// The whole `[0]` signed attributes element, tag included.
    pub signed_attrs: &'a [u8],
    /// The TSA's signature `(r, s)`, as 48-byte big-endian numbers.
    pub signature: ([u8; 48], [u8; 48]),
}

/// Reads an `AlgorithmIdentifier` and reports whether it is `sha256` with
/// absent or `NULL` parameters.
fn is_sha256(d: &mut Der<'_>) -> Result<bool, Error> {
    let (oid, params) = d.algorithm()?;
    Ok(oid == SHA256 && der::absent_or_null(params))
}

/// Fails with [`Error::BadTimestamp`] unless `d` has been read to the end.
fn end(d: &Der<'_>) -> Result<(), Error> {
    if d.is_empty() {
        Ok(())
    } else {
        Err(Error::BadTimestamp)
    }
}

/// The two signed attributes the profile requires.
struct SignedAttributes<'a> {
    message_digest: &'a [u8; 32],
}

/// Checks the contents of the `[0]` signed attributes.
fn read_signed_attributes(content: &[u8]) -> Result<SignedAttributes<'_>, Error> {
    let mut attributes = Der::new(content);
    let mut content_type = false;
    let mut message_digest = None;
    while !attributes.is_empty() {
        let earlier = attributes.consumed()?;
        let mut attribute = attributes.sequence()?;
        let oid = attribute.oid()?;
        let mut values = attribute.set()?;
        attribute.finish()?;
        if der::lists_oid(earlier, oid)? {
            return Err(Error::BadTimestamp);
        }
        if oid == CONTENT_TYPE {
            if values.oid()? != TST_INFO {
                return Err(Error::BadTimestamp);
            }
            end(&values)?;
            content_type = true;
        } else if oid == MESSAGE_DIGEST {
            let digest: &[u8; 32] = values
                .octet_string()?
                .try_into()
                .map_err(|_| Error::BadTimestamp)?;
            end(&values)?;
            message_digest = Some(digest);
        }
    }
    match message_digest {
        Some(message_digest) if content_type => Ok(SignedAttributes { message_digest }),
        _ => Err(Error::BadTimestamp),
    }
}

/// The `TSTInfo` fields the bootloader uses.
struct TstInfo<'a> {
    gen_time: u64,
    message_imprint: &'a [u8; 32],
}

/// Parses a DER `TSTInfo`.
fn read_tst_info(der: &[u8]) -> Result<TstInfo<'_>, Error> {
    let mut input = Der::new(der);
    let mut info = input.sequence()?;
    input.finish()?;
    if !info.integer_is(1)? {
        return Err(Error::BadTimestamp);
    }
    info.oid()?;
    let mut imprint = info.sequence()?;
    if !is_sha256(&mut imprint)? {
        return Err(Error::BadTimestamp);
    }
    let message_imprint: &[u8; 32] = imprint
        .octet_string()?
        .try_into()
        .map_err(|_| Error::BadTimestamp)?;
    imprint.finish()?;
    let serial = info.positive_integer()?;
    let magnitude = match serial {
        [0x00, rest @ ..] => rest,
        _ => serial,
    };
    if magnitude.len() > MAX_SERIAL_MAGNITUDE {
        return Err(Error::BadTimestamp);
    }
    let gen_time = time::generalized_time(info.element(GENERALIZED_TIME)?.content)?;
    info.optional(SEQUENCE)?;
    if info.peek_tag() == Some(BOOLEAN) {
        info.boolean_true()?;
    }
    if info.peek_tag() == Some(INTEGER) {
        info.integer()?;
    }
    info.optional(CONTEXT_0)?;
    info.optional(CONTEXT_1)?;
    end(&info)?;
    Ok(TstInfo {
        gen_time,
        message_imprint,
    })
}

/// Parses a DER `TimeStampResp` and checks it against the timestamp profile.
///
/// The signature, the `messageDigest` attribute, and the `messageImprint`
/// aren't checked here; [`verify_timestamp`] checks them.
pub fn parse_timestamp(der: &[u8]) -> Result<Timestamp<'_>, Error> {
    let mut input = Der::new(der);
    let mut response = input.sequence()?;
    input.finish()?;
    let mut status = response.sequence()?;
    if !status.integer_is(0)? {
        return Err(Error::BadTimestamp);
    }
    end(&status)?;
    let mut content_info = response.sequence()?;
    response.finish()?;
    if content_info.oid()? != SIGNED_DATA {
        return Err(Error::BadTimestamp);
    }
    let mut explicit = content_info.nested(CONTEXT_0)?;
    content_info.finish()?;
    let mut signed_data = explicit.sequence()?;
    explicit.finish()?;

    if !signed_data.integer_is(3)? {
        return Err(Error::BadTimestamp);
    }
    let mut digest_algorithms = signed_data.set()?;
    if !is_sha256(&mut digest_algorithms)? {
        return Err(Error::BadTimestamp);
    }
    end(&digest_algorithms)?;
    let mut encap = signed_data.sequence()?;
    if encap.oid()? != TST_INFO {
        return Err(Error::BadTimestamp);
    }
    let mut econtent = encap
        .optional(CONTEXT_0)?
        .map(|t| Der::new(t.content))
        .ok_or(Error::BadTimestamp)?;
    encap.finish()?;
    let tst_info = econtent.octet_string()?;
    econtent.finish()?;
    signed_data.optional(CONTEXT_0)?;
    if signed_data.peek_tag() == Some(CONTEXT_1) {
        return Err(Error::BadTimestamp);
    }
    let mut signer_infos = signed_data.set()?;
    signed_data.finish()?;
    let mut signer_info = signer_infos.sequence()?;
    end(&signer_infos)?;

    if !signer_info.integer_is(1)? {
        return Err(Error::BadTimestamp);
    }
    let signer_id = signer_info.element(SEQUENCE)?.raw;
    if !is_sha256(&mut signer_info)? {
        return Err(Error::BadTimestamp);
    }
    let signed_attrs = signer_info
        .optional(CONTEXT_0)?
        .ok_or(Error::BadTimestamp)?;
    let attributes = read_signed_attributes(signed_attrs.content)?;
    let (algorithm, params) = signer_info.algorithm()?;
    if algorithm != ECDSA_WITH_SHA256 || params.is_some() {
        return Err(Error::BadTimestamp);
    }
    let signature = der::ecdsa_signature::<48>(signer_info.octet_string()?)?;
    end(&signer_info)?;

    let info = read_tst_info(tst_info)?;
    Ok(Timestamp {
        gen_time: info.gen_time,
        message_imprint: info.message_imprint,
        tst_info,
        message_digest: attributes.message_digest,
        signer_id,
        signed_attrs: signed_attrs.raw,
        signature,
    })
}

/// Checks that `signer` signed `ts` and that `ts` covers `image_signature`.
///
/// Fails with [`Error::NoMatchingKey`] if the token's `sid` isn't the signer's
/// ID, with [`Error::DigestMismatch`] if the `messageDigest` attribute doesn't
/// match the `TSTInfo` or the `messageImprint` doesn't match
/// `image_signature`, and with [`Error::BadSignature`] if the signature over
/// the signed attributes doesn't verify. Validity windows are the caller's to
/// check.
pub fn verify_timestamp(
    ts: &Timestamp<'_>,
    signer: &TsaSigner<'_>,
    image_signature: &[u8],
) -> Result<(), Error> {
    if ts.signer_id != signer.signer_id {
        return Err(Error::NoMatchingKey);
    }
    if c3_crypto::sha256(ts.tst_info) != *ts.message_digest {
        return Err(Error::DigestMismatch);
    }
    if c3_crypto::sha256(image_signature) != *ts.message_imprint {
        return Err(Error::DigestMismatch);
    }
    let (_, attributes) = ts.signed_attrs.split_first().ok_or(Error::Truncated)?;
    let prehash = c3_crypto::sha256_parts(&[&[SET_OF_TAG], attributes]);
    let (r, s) = &ts.signature;
    if c3_crypto::p384_verify_prehash(signer.public_key, &prehash, r, s) {
        Ok(())
    } else {
        Err(Error::BadSignature)
    }
}

#[cfg(test)]
#[allow(clippy::arithmetic_side_effects, clippy::indexing_slicing)]
mod tests {
    use super::*;
    use crate::der::OCTET_STRING;
    use crate::der::OID;
    use crate::der::tests::all_bundles;
    use crate::der::tests::at;
    use crate::der::tests::edit;
    use crate::der::tests::happy_path;
    use crate::der::tests::seq;
    use crate::der::tests::subject_and_p384_key;
    use crate::der::tests::tlv;
    use crate::der::tests::trusted_certificates;
    use crate::trustroot::Window;

    /// Paths from the `TimeStampResp` to the parts the tests change.
    const STATUS: [usize; 1] = [0];
    const SIGNED_DATA_PATH: [usize; 3] = [1, 1, 0];
    const SIGNER_INFOS: [usize; 4] = [1, 1, 0, 4];
    const SIGNER_INFO: [usize; 5] = [1, 1, 0, 4, 0];
    const SIGNED_ATTRS: [usize; 6] = [1, 1, 0, 4, 0, 3];
    const TST_INFO_PATH: [usize; 7] = [1, 1, 0, 2, 1, 0, 0];

    /// 2025-06-12T12:02:20Z.
    const HAPPY_GEN_TIME: u64 = 1_749_729_740;

    fn token() -> Vec<u8> {
        happy_path().timestamp.unwrap()
    }

    fn tsa_key() -> [u8; 97] {
        subject_and_p384_key(&trusted_certificates().1).1
    }

    const ANY_TIME: Window = Window {
        not_before: 0,
        not_after: u64::MAX,
    };

    #[test]
    fn parses_real_timestamp() {
        let f = happy_path();
        let der = f.timestamp.unwrap();
        let ts = parse_timestamp(&der).unwrap();
        assert_eq!(ts.gen_time, HAPPY_GEN_TIME);
        assert_eq!(
            time::generalized_time(b"20250612120220Z"),
            Ok(HAPPY_GEN_TIME)
        );
        assert_eq!(*ts.message_imprint, c3_crypto::sha256(&f.signature));
        assert_eq!(*ts.message_digest, c3_crypto::sha256(ts.tst_info));
        assert_eq!(ts.signer_id, &at(&der, &[1, 1, 0, 4, 0, 1])[..]);
        assert_eq!(ts.signed_attrs, &at(&der, &SIGNED_ATTRS)[..]);
        assert_eq!(ts.signed_attrs[0], CONTEXT_0);
        assert_eq!(ts.tst_info, &at(&der, &TST_INFO_PATH)[..]);
    }

    #[test]
    fn verifies_real_timestamp() {
        let f = happy_path();
        let der = f.timestamp.unwrap();
        let ts = parse_timestamp(&der).unwrap();
        let key = tsa_key();
        let signer = TsaSigner {
            signer_id: ts.signer_id,
            public_key: &key,
            window: ANY_TIME,
        };
        assert_eq!(verify_timestamp(&ts, &signer, &f.signature), Ok(()));

        let mut flipped = ts;
        flipped.signature.0[20] ^= 1;
        assert_eq!(
            verify_timestamp(&flipped, &signer, &f.signature),
            Err(Error::BadSignature)
        );
        let mut wrong_image = f.signature.clone();
        wrong_image[10] ^= 1;
        assert_eq!(
            verify_timestamp(&ts, &signer, &wrong_image),
            Err(Error::DigestMismatch)
        );
        let other_id = [ts.signer_id, &[0]].concat();
        let wrong_id = TsaSigner {
            signer_id: &other_id,
            ..signer
        };
        assert_eq!(
            verify_timestamp(&ts, &wrong_id, &f.signature),
            Err(Error::NoMatchingKey)
        );
        let (_, intermediate_key) = subject_and_p384_key(&trusted_certificates().0);
        let wrong_key = TsaSigner {
            public_key: &intermediate_key,
            ..signer
        };
        assert_eq!(
            verify_timestamp(&ts, &wrong_key, &f.signature),
            Err(Error::BadSignature)
        );
    }

    #[test]
    fn rejects_tampered_tst_info() {
        let f = happy_path();
        let der = edit(&token(), &TST_INFO_PATH, |info| {
            info[1] = tlv(OID, &[0x2a, 0x03])
        });
        let ts = parse_timestamp(&der).unwrap();
        let key = tsa_key();
        let signer = TsaSigner {
            signer_id: ts.signer_id,
            public_key: &key,
            window: ANY_TIME,
        };
        assert_eq!(
            verify_timestamp(&ts, &signer, &f.signature),
            Err(Error::DigestMismatch)
        );
    }

    /// The bundles whose TSA uses SHA-512 and RSA, which the profile rejects.
    const OUTSIDE_PROFILE: [&str; 2] = [
        "rekor2-timestamp-untrusted-tsa-with-embedded-cert_fail",
        "rekor2-timestamp-untrusted-tsa-without-embedded-cert_fail",
    ];

    #[test]
    fn parses_every_conformance_timestamp() {
        let mut parsed = 0;
        for (name, f) in all_bundles() {
            let Some(der) = f.timestamp else {
                continue;
            };
            let result = parse_timestamp(&der);
            if OUTSIDE_PROFILE.contains(&name.as_str()) {
                assert_eq!(result, Err(Error::BadTimestamp), "{name}");
            } else {
                let ts = result.unwrap_or_else(|e| panic!("{name}: {e:?}"));
                assert_eq!(*ts.message_digest, c3_crypto::sha256(ts.tst_info), "{name}");
                parsed += 1;
            }
        }
        assert_eq!(parsed, 19);
    }

    #[test]
    fn accepts_21_byte_serial_with_sign_byte() {
        let mut serial = vec![0x00, 0x80];
        serial.extend_from_slice(&[1; 19]);
        let der = edit(&token(), &TST_INFO_PATH, |info| {
            info[3] = tlv(INTEGER, &serial)
        });
        assert!(parse_timestamp(&der).is_ok());
        let der = edit(&token(), &TST_INFO_PATH, |info| {
            info[3] = tlv(INTEGER, &[0x7f; 21])
        });
        assert_eq!(parse_timestamp(&der), Err(Error::BadTimestamp));
    }

    #[test]
    fn rejects_rejected_status() {
        let der = edit(&token(), &STATUS, |s| s[0] = tlv(INTEGER, &[2]));
        assert_eq!(parse_timestamp(&der), Err(Error::BadTimestamp));
        let der = edit(&token(), &STATUS, |s| s.push(seq(&[])));
        assert_eq!(parse_timestamp(&der), Err(Error::BadTimestamp));
    }

    #[test]
    fn rejects_signed_data_version_1() {
        let der = edit(&token(), &SIGNED_DATA_PATH, |sd| sd[0] = tlv(INTEGER, &[1]));
        assert_eq!(parse_timestamp(&der), Err(Error::BadTimestamp));
    }

    #[test]
    fn rejects_two_signer_infos() {
        let der = edit(&token(), &SIGNER_INFOS, |set| {
            let first = set[0].clone();
            set.push(first);
        });
        assert_eq!(parse_timestamp(&der), Err(Error::BadTimestamp));
    }

    #[test]
    fn requires_message_digest_once() {
        let der = edit(&token(), &SIGNED_ATTRS, |attrs| {
            attrs.remove(2);
        });
        assert_eq!(parse_timestamp(&der), Err(Error::BadTimestamp));
        let der = edit(&token(), &SIGNED_ATTRS, |attrs| {
            attrs.remove(0);
        });
        assert_eq!(parse_timestamp(&der), Err(Error::BadTimestamp));
        let der = edit(&token(), &SIGNED_ATTRS, |attrs| {
            let digest = attrs[2].clone();
            attrs.push(digest);
        });
        assert_eq!(parse_timestamp(&der), Err(Error::BadTimestamp));
        let der = edit(&token(), &SIGNED_ATTRS, |attrs| {
            let time = attrs[1].clone();
            attrs.push(time);
        });
        assert_eq!(parse_timestamp(&der), Err(Error::BadTimestamp));
    }

    #[test]
    fn checks_attribute_values() {
        let two_values = edit(&token(), &[1, 1, 0, 4, 0, 3, 2, 1], |values| {
            let v = values[0].clone();
            values.push(v);
        });
        assert_eq!(parse_timestamp(&two_values), Err(Error::BadTimestamp));
        let short = edit(&token(), &[1, 1, 0, 4, 0, 3, 2, 1], |values| {
            values[0] = tlv(OCTET_STRING, &[0; 31]);
        });
        assert_eq!(parse_timestamp(&short), Err(Error::BadTimestamp));
        let wrong_type = edit(&token(), &[1, 1, 0, 4, 0, 3, 0, 1], |values| {
            values[0] = tlv(OID, SIGNED_DATA);
        });
        assert_eq!(parse_timestamp(&wrong_type), Err(Error::BadTimestamp));
    }

    #[test]
    fn rejects_ecdsa_with_sha384() {
        let alg = seq(&[&tlv(OID, &[0x2a, 0x86, 0x48, 0xce, 0x3d, 0x04, 0x03, 0x03])]);
        let der = edit(&token(), &SIGNER_INFO, |si| si[4] = alg);
        assert_eq!(parse_timestamp(&der), Err(Error::BadTimestamp));
    }

    #[test]
    fn rejects_33_byte_message_imprint() {
        let der = edit(&token(), &[1, 1, 0, 2, 1, 0, 0, 2], |mi| {
            mi[1] = tlv(OCTET_STRING, &[0; 33]);
        });
        assert_eq!(parse_timestamp(&der), Err(Error::BadTimestamp));
    }

    #[test]
    fn rejects_crls_and_unsigned_attributes() {
        let der = edit(&token(), &SIGNED_DATA_PATH, |sd| {
            sd.insert(4, tlv(CONTEXT_1, &[]))
        });
        assert_eq!(parse_timestamp(&der), Err(Error::BadTimestamp));
        let der = edit(&token(), &SIGNER_INFO, |si| si.push(tlv(CONTEXT_1, &[])));
        assert_eq!(parse_timestamp(&der), Err(Error::BadTimestamp));
    }

    #[test]
    fn handles_optional_certificates() {
        let der = edit(&token(), &SIGNED_DATA_PATH, |sd| {
            sd.remove(3);
        });
        assert!(parse_timestamp(&der).is_ok());
    }

    #[test]
    fn requires_signed_attributes() {
        let der = edit(&token(), &SIGNER_INFO, |si| {
            si.remove(3);
        });
        assert_eq!(parse_timestamp(&der), Err(Error::BadTimestamp));
    }

    #[test]
    fn rejects_wrong_digest_algorithms() {
        let sha512 = seq(&[&tlv(
            OID,
            &[0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x03],
        )]);
        let der = edit(&token(), &[1, 1, 0, 1], |set| set[0] = sha512.clone());
        assert_eq!(parse_timestamp(&der), Err(Error::BadTimestamp));
        let der = edit(&token(), &[1, 1, 0, 1], |set| {
            let sha256 = set[0].clone();
            set.push(sha256);
        });
        assert_eq!(parse_timestamp(&der), Err(Error::BadTimestamp));
        let der = edit(&token(), &SIGNER_INFO, |si| si[2] = sha512);
        assert_eq!(parse_timestamp(&der), Err(Error::BadTimestamp));
    }

    #[test]
    fn checks_tst_info_optional_fields() {
        let swapped = edit(&token(), &TST_INFO_PATH, |info| info.swap(5, 6));
        assert_eq!(parse_timestamp(&swapped), Err(Error::BadTimestamp));
        let twice = edit(&token(), &TST_INFO_PATH, |info| {
            let nonce = info[6].clone();
            info.insert(6, nonce);
        });
        assert_eq!(parse_timestamp(&twice), Err(Error::BadTimestamp));
        let ordering_false = edit(&token(), &TST_INFO_PATH, |info| {
            info.insert(6, tlv(BOOLEAN, &[0x00]));
        });
        assert_eq!(parse_timestamp(&ordering_false), Err(Error::BadDer));
        let ordering_true = edit(&token(), &TST_INFO_PATH, |info| {
            info.insert(6, tlv(BOOLEAN, &[0xff]));
        });
        assert!(parse_timestamp(&ordering_true).is_ok());
        let bare = edit(&token(), &TST_INFO_PATH, |info| info.truncate(5));
        assert!(parse_timestamp(&bare).is_ok());
        let extensions = edit(&token(), &TST_INFO_PATH, |info| {
            info.push(tlv(CONTEXT_1, &seq(&[])));
        });
        assert!(parse_timestamp(&extensions).is_ok());
    }

    #[test]
    fn rejects_trailing_bytes() {
        let mut der = token();
        der.push(0);
        assert_eq!(parse_timestamp(&der), Err(Error::TrailingBytes));
    }
}

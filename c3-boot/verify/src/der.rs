//! A strict DER reader for the ASN.1 structures in `docs/formats.md`.
//!
//! The reader accepts one-byte tags and definite lengths in their shortest
//! form only. Each helper expects one universal type and rejects any other tag
//! with [`Error::BadDer`].

use crate::error::Error;

pub(crate) const BOOLEAN: u8 = 0x01;
pub(crate) const INTEGER: u8 = 0x02;
pub(crate) const BIT_STRING: u8 = 0x03;
pub(crate) const OCTET_STRING: u8 = 0x04;
pub(crate) const NULL: u8 = 0x05;
pub(crate) const OID: u8 = 0x06;
pub(crate) const UTF8_STRING: u8 = 0x0c;
pub(crate) const UTC_TIME: u8 = 0x17;
pub(crate) const GENERALIZED_TIME: u8 = 0x18;
pub(crate) const SEQUENCE: u8 = 0x30;
pub(crate) const SET: u8 = 0x31;
pub(crate) const CONTEXT_0: u8 = 0xa0;
pub(crate) const CONTEXT_1: u8 = 0xa1;
pub(crate) const CONTEXT_3: u8 = 0xa3;

/// The most bytes a long-form length can use after its first byte.
const MAX_LENGTH_BYTES: usize = 4;

/// One DER element.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Tlv<'a> {
    /// The one-byte tag.
    pub(crate) tag: u8,
    /// The contents, after the tag and length.
    pub(crate) content: &'a [u8],
    /// The whole element: tag, length, and contents.
    pub(crate) raw: &'a [u8],
}

/// Reads DER elements one after another from a byte slice.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Der<'a> {
    input: &'a [u8],
    rest: &'a [u8],
}

impl<'a> Der<'a> {
    pub(crate) fn new(input: &'a [u8]) -> Self {
        Der { input, rest: input }
    }

    /// Reports whether every element has been read.
    pub(crate) fn is_empty(&self) -> bool {
        self.rest.is_empty()
    }

    /// The bytes read so far.
    pub(crate) fn consumed(&self) -> Result<&'a [u8], Error> {
        let n = self
            .input
            .len()
            .checked_sub(self.rest.len())
            .ok_or(Error::Overflow)?;
        self.input.get(..n).ok_or(Error::Truncated)
    }

    /// The tag of the next element, if there is one.
    pub(crate) fn peek_tag(&self) -> Option<u8> {
        self.rest.first().copied()
    }

    /// Reads the next element, whatever its tag.
    pub(crate) fn tlv(&mut self) -> Result<Tlv<'a>, Error> {
        let input = self.rest;
        let (&tag, after_tag) = input.split_first().ok_or(Error::Truncated)?;
        if tag & 0x1f == 0x1f {
            return Err(Error::BadDer);
        }
        let (&first, mut after_length) = after_tag.split_first().ok_or(Error::Truncated)?;
        let len = if first < 0x80 {
            usize::from(first)
        } else {
            let count = usize::from(first & 0x7f);
            if count == 0 || count > MAX_LENGTH_BYTES {
                return Err(Error::BadDer);
            }
            let (bytes, after) = after_length
                .split_at_checked(count)
                .ok_or(Error::Truncated)?;
            after_length = after;
            if bytes.first() == Some(&0) {
                return Err(Error::BadDer);
            }
            let mut len: usize = 0;
            for &b in bytes {
                len = len
                    .checked_mul(256)
                    .and_then(|l| l.checked_add(usize::from(b)))
                    .ok_or(Error::Overflow)?;
            }
            if len < 0x80 {
                return Err(Error::BadDer);
            }
            len
        };
        let (content, rest) = after_length.split_at_checked(len).ok_or(Error::Truncated)?;
        let raw_len = input.len().checked_sub(rest.len()).ok_or(Error::Overflow)?;
        let raw = input.get(..raw_len).ok_or(Error::Truncated)?;
        self.rest = rest;
        Ok(Tlv { tag, content, raw })
    }

    /// Reads the next element and fails unless its tag is `tag`.
    pub(crate) fn element(&mut self, tag: u8) -> Result<Tlv<'a>, Error> {
        if self.peek_tag() != Some(tag) {
            return Err(if self.is_empty() {
                Error::Truncated
            } else {
                Error::BadDer
            });
        }
        self.tlv()
    }

    /// Reads the next element if its tag is `tag`.
    pub(crate) fn optional(&mut self, tag: u8) -> Result<Option<Tlv<'a>>, Error> {
        if self.peek_tag() == Some(tag) {
            self.tlv().map(Some)
        } else {
            Ok(None)
        }
    }

    /// Reads an element with tag `tag` and returns a reader over its contents.
    pub(crate) fn nested(&mut self, tag: u8) -> Result<Der<'a>, Error> {
        Ok(Der::new(self.element(tag)?.content))
    }

    /// Reads a `SEQUENCE` and returns a reader over its contents.
    pub(crate) fn sequence(&mut self) -> Result<Der<'a>, Error> {
        self.nested(SEQUENCE)
    }

    /// Reads a `SET` and returns a reader over its contents.
    pub(crate) fn set(&mut self) -> Result<Der<'a>, Error> {
        self.nested(SET)
    }

    /// Reads an `OBJECT IDENTIFIER` and returns its contents.
    ///
    /// Each subidentifier must be in its shortest base-128 form, and the last
    /// byte must end one.
    pub(crate) fn oid(&mut self) -> Result<&'a [u8], Error> {
        let content = self.element(OID)?.content;
        let mut at_start = true;
        for &b in content {
            if at_start && b == 0x80 {
                return Err(Error::BadDer);
            }
            at_start = b & 0x80 == 0;
        }
        if content.is_empty() || !at_start {
            return Err(Error::BadDer);
        }
        Ok(content)
    }

    /// Reads a minimally encoded `INTEGER` and returns its contents.
    pub(crate) fn integer(&mut self) -> Result<&'a [u8], Error> {
        let content = self.element(INTEGER)?.content;
        match content {
            [] => Err(Error::BadDer),
            [0x00, next, ..] if next & 0x80 == 0 => Err(Error::BadDer),
            [0xff, next, ..] if next & 0x80 != 0 => Err(Error::BadDer),
            _ => Ok(content),
        }
    }

    /// Reads a minimally encoded `INTEGER` greater than zero and returns its
    /// contents, including the leading zero byte if it has one.
    pub(crate) fn positive_integer(&mut self) -> Result<&'a [u8], Error> {
        let content = self.integer()?;
        match content {
            [0x00] => Err(Error::BadDer),
            [first, ..] if first & 0x80 != 0 => Err(Error::BadDer),
            _ => Ok(content),
        }
    }

    /// Reads a minimally encoded `INTEGER` and reports whether it equals
    /// `value`, which must be below 128.
    pub(crate) fn integer_is(&mut self, value: u8) -> Result<bool, Error> {
        Ok(self.integer()? == [value].as_slice())
    }

    /// Reads a `BOOLEAN` whose ASN.1 default is `FALSE`.
    ///
    /// DER omits a field equal to its default, so the only value allowed is
    /// `TRUE`, encoded as `0xFF`.
    pub(crate) fn boolean_true(&mut self) -> Result<(), Error> {
        if self.element(BOOLEAN)?.content == [0xff] {
            Ok(())
        } else {
            Err(Error::BadDer)
        }
    }

    /// Reads an `OCTET STRING` and returns its contents.
    pub(crate) fn octet_string(&mut self) -> Result<&'a [u8], Error> {
        Ok(self.element(OCTET_STRING)?.content)
    }

    /// Reads a `BIT STRING` with zero unused bits and returns its bytes.
    pub(crate) fn bit_string(&mut self) -> Result<&'a [u8], Error> {
        match self.element(BIT_STRING)?.content.split_first() {
            Some((0, bits)) => Ok(bits),
            _ => Err(Error::BadDer),
        }
    }

    /// Reads a `BIT STRING` that holds a named bit list, such as `KeyUsage`,
    /// and returns its bytes.
    ///
    /// DER requires the unused bits to be zero and removes trailing zero bits,
    /// so the last byte's lowest used bit is set.
    pub(crate) fn named_bits(&mut self) -> Result<&'a [u8], Error> {
        let (&unused, bits) = self
            .element(BIT_STRING)?
            .content
            .split_first()
            .ok_or(Error::BadDer)?;
        match bits.last() {
            None if unused == 0 => Ok(bits),
            Some(last) if last.trailing_zeros() == u32::from(unused) => Ok(bits),
            _ => Err(Error::BadDer),
        }
    }

    /// Reads an `AlgorithmIdentifier` and returns its OID contents and its
    /// parameters, if any.
    pub(crate) fn algorithm(&mut self) -> Result<(&'a [u8], Option<Tlv<'a>>), Error> {
        let mut seq = self.sequence()?;
        let oid = seq.oid()?;
        let params = if seq.is_empty() {
            None
        } else {
            Some(seq.tlv()?)
        };
        seq.finish()?;
        Ok((oid, params))
    }

    /// Fails unless every element has been read.
    pub(crate) fn finish(&self) -> Result<(), Error> {
        if self.is_empty() {
            Ok(())
        } else {
            Err(Error::TrailingBytes)
        }
    }
}

/// Reports whether algorithm parameters are absent or an empty `NULL`.
pub(crate) fn absent_or_null(params: Option<Tlv<'_>>) -> bool {
    match params {
        None => true,
        Some(p) => p.tag == NULL && p.content.is_empty(),
    }
}

/// Reports whether `list`, a run of `SEQUENCE`s that each start with an OID,
/// holds one that starts with `oid`.
pub(crate) fn lists_oid(list: &[u8], oid: &[u8]) -> Result<bool, Error> {
    let mut d = Der::new(list);
    while !d.is_empty() {
        if d.sequence()?.oid()? == oid {
            return Ok(true);
        }
    }
    Ok(false)
}

/// Reads one `INTEGER` of an `ECDSA-Sig-Value` as an `N`-byte big-endian
/// number.
fn scalar<const N: usize>(d: &mut Der<'_>) -> Result<[u8; N], Error> {
    let content = d.positive_integer()?;
    let magnitude = match content {
        [0x00, rest @ ..] => rest,
        _ => content,
    };
    let pad = N.checked_sub(magnitude.len()).ok_or(Error::OutOfRange)?;
    let mut out = [0u8; N];
    for (o, m) in out.iter_mut().skip(pad).zip(magnitude) {
        *o = *m;
    }
    Ok(out)
}

/// Parses a DER `ECDSA-Sig-Value`, `SEQUENCE { r INTEGER, s INTEGER }`, with
/// nothing after it.
///
/// Each integer must be positive, minimally encoded, and at most `N` bytes
/// long without its sign byte. The result holds `r` and `s` as `N`-byte
/// big-endian numbers. The caller checks them against the group order.
pub fn ecdsa_signature<const N: usize>(der: &[u8]) -> Result<([u8; N], [u8; N]), Error> {
    let mut input = Der::new(der);
    let mut seq = input.sequence()?;
    input.finish()?;
    let r = scalar::<N>(&mut seq)?;
    let s = scalar::<N>(&mut seq)?;
    seq.finish()?;
    Ok((r, s))
}

#[cfg(test)]
#[allow(clippy::arithmetic_side_effects, clippy::indexing_slicing)]
pub(crate) mod tests {
    use super::*;
    use base64::Engine;
    use base64::engine::general_purpose::STANDARD;

    /// Encodes one DER element with a minimal length.
    pub(crate) fn tlv(tag: u8, content: &[u8]) -> Vec<u8> {
        let mut out = vec![tag];
        let len = content.len();
        if len < 0x80 {
            out.push(len as u8);
        } else {
            let bytes = len.to_be_bytes();
            let skip = bytes.iter().take_while(|&&b| b == 0).count();
            out.push(0x80 | (bytes.len() - skip) as u8);
            out.extend_from_slice(&bytes[skip..]);
        }
        out.extend_from_slice(content);
        out
    }

    /// Encodes a `SEQUENCE` of already encoded elements.
    pub(crate) fn seq(parts: &[&[u8]]) -> Vec<u8> {
        tlv(SEQUENCE, &parts.concat())
    }

    /// Splits `content` into its encoded elements.
    pub(crate) fn children(content: &[u8]) -> Vec<Vec<u8>> {
        let mut d = Der::new(content);
        let mut out = Vec::new();
        while !d.is_empty() {
            out.push(d.tlv().unwrap().raw.to_vec());
        }
        out
    }

    /// Re-encodes `der` after applying `f` to the children of the element at
    /// `path`, where each step is a child index.
    pub(crate) fn edit<F: FnOnce(&mut Vec<Vec<u8>>)>(der: &[u8], path: &[usize], f: F) -> Vec<u8> {
        let t = Der::new(der).tlv().unwrap();
        let mut kids = children(t.content);
        match path.split_first() {
            None => f(&mut kids),
            Some((&i, rest)) => kids[i] = edit(&kids[i], rest, f),
        }
        tlv(t.tag, &kids.concat())
    }

    /// The raw DER of the element at `path`.
    pub(crate) fn at(der: &[u8], path: &[usize]) -> Vec<u8> {
        match path.split_first() {
            None => der.to_vec(),
            Some((&i, rest)) => {
                let t = Der::new(der).tlv().unwrap();
                at(&children(t.content)[i], rest)
            }
        }
    }

    /// The pieces of one conformance bundle that the parsers read.
    pub(crate) struct Fixture {
        pub(crate) leaf: Vec<u8>,
        pub(crate) timestamp: Option<Vec<u8>>,
        pub(crate) signature: Vec<u8>,
    }

    fn decode(v: &serde_json::Value) -> Vec<u8> {
        let text: String = v
            .as_str()
            .unwrap()
            .chars()
            .filter(|c| !c.is_whitespace())
            .collect();
        STANDARD.decode(text).unwrap()
    }

    pub(crate) fn bundle(json: &str) -> Fixture {
        let b: serde_json::Value = serde_json::from_str(json).unwrap();
        let vm = &b["verificationMaterial"];
        let timestamp = vm["timestampVerificationData"]["rfc3161Timestamps"]
            .as_array()
            .and_then(|a| a.first())
            .map(|t| decode(&t["signedTimestamp"]));
        Fixture {
            leaf: decode(&vm["certificate"]["rawBytes"]),
            timestamp,
            signature: decode(&b["messageSignature"]["signature"]),
        }
    }

    pub(crate) fn happy_path() -> Fixture {
        bundle(include_str!(
            "../../testdata/conformance/rekor2-happy-path/bundle.sigstore.json"
        ))
    }

    /// Every conformance bundle, by directory name.
    pub(crate) fn all_bundles() -> Vec<(String, Fixture)> {
        let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/../testdata/conformance");
        let mut out = Vec::new();
        for entry in std::fs::read_dir(dir).unwrap() {
            let path = entry.unwrap().path();
            let file = path.join("bundle.sigstore.json");
            if file.exists() {
                let name = path.file_name().unwrap().to_string_lossy().into_owned();
                out.push((name, bundle(&std::fs::read_to_string(file).unwrap())));
            }
        }
        out.sort_by(|a, b| a.0.cmp(&b.0));
        out
    }

    /// The first certificate of the first Fulcio CA and the first TSA in the
    /// happy path's trusted root.
    pub(crate) fn trusted_certificates() -> (Vec<u8>, Vec<u8>) {
        let t: serde_json::Value = serde_json::from_str(include_str!(
            "../../testdata/conformance/rekor2-happy-path/trusted_root.json"
        ))
        .unwrap();
        let first = |key: &str| decode(&t[key][0]["certChain"]["certificates"][0]["rawBytes"]);
        (
            first("certificateAuthorities"),
            first("timestampAuthorities"),
        )
    }

    /// A certificate's subject `Name` and its 97-byte P-384 public key.
    pub(crate) fn subject_and_p384_key(cert: &[u8]) -> (Vec<u8>, [u8; 97]) {
        let tbs = at(cert, &[0]);
        let subject = at(&tbs, &[5]);
        let bits = at(&tbs, &[6, 1]);
        let point = Der::new(&bits).bit_string().unwrap();
        (subject, point.try_into().unwrap())
    }

    fn read(bytes: &[u8]) -> Result<Tlv<'_>, Error> {
        let mut d = Der::new(bytes);
        let t = d.tlv()?;
        d.finish()?;
        Ok(t)
    }

    #[test]
    fn reads_short_and_long_lengths() {
        let t = read(&[0x04, 0x02, 0xaa, 0xbb]).unwrap();
        assert_eq!((t.tag, t.content), (0x04, &[0xaa, 0xbb][..]));
        let long = tlv(0x04, &[7; 200]);
        assert_eq!(&long[..3], &[0x04, 0x81, 200]);
        let t = read(&long).unwrap();
        assert_eq!(t.content.len(), 200);
        assert_eq!(t.raw, &long[..]);
        let longer = tlv(0x04, &[7; 300]);
        assert_eq!(&longer[..4], &[0x04, 0x82, 0x01, 0x2c]);
        assert_eq!(read(&longer).unwrap().content.len(), 300);
    }

    #[test]
    fn rejects_non_minimal_lengths() {
        assert_eq!(read(&[0x04, 0x81, 0x05, 1, 2, 3, 4, 5]), Err(Error::BadDer));
        let mut padded = vec![0x04, 0x82, 0x00, 0x80];
        padded.extend_from_slice(&[0; 128]);
        assert_eq!(read(&padded), Err(Error::BadDer));
    }

    #[test]
    fn rejects_indefinite_and_oversized_lengths() {
        assert_eq!(read(&[0x30, 0x80, 0x00, 0x00]), Err(Error::BadDer));
        assert_eq!(read(&[0x04, 0x85, 1, 0, 0, 0, 0]), Err(Error::BadDer));
        assert_eq!(read(&[0x04, 0xff]), Err(Error::BadDer));
    }

    #[test]
    fn rejects_multi_byte_tags() {
        assert_eq!(read(&[0x1f, 0x22, 0x00]), Err(Error::BadDer));
        assert_eq!(read(&[0xbf, 0x81, 0x00, 0x00]), Err(Error::BadDer));
    }

    #[test]
    fn rejects_lengths_past_the_input() {
        assert_eq!(read(&[0x04, 0x03, 1, 2]), Err(Error::Truncated));
        assert_eq!(read(&[0x04, 0x82, 0x01]), Err(Error::Truncated));
        assert_eq!(read(&[0x04]), Err(Error::Truncated));
        assert_eq!(read(&[]), Err(Error::Truncated));
    }

    #[test]
    fn rejects_trailing_bytes() {
        assert_eq!(read(&[0x05, 0x00, 0x00]), Err(Error::TrailingBytes));
    }

    #[test]
    fn checks_integers() {
        let int = |c: &[u8]| Der::new(&tlv(INTEGER, c)).integer().map(<[u8]>::to_vec);
        let pos = |c: &[u8]| {
            Der::new(&tlv(INTEGER, c))
                .positive_integer()
                .map(<[u8]>::to_vec)
        };
        assert_eq!(int(&[0x00, 0x01]), Err(Error::BadDer));
        assert_eq!(int(&[0xff, 0x80]), Err(Error::BadDer));
        assert_eq!(int(&[]), Err(Error::BadDer));
        assert_eq!(int(&[0x80]), Ok(vec![0x80]));
        assert_eq!(pos(&[0x80]), Err(Error::BadDer));
        assert_eq!(pos(&[0x00]), Err(Error::BadDer));
        assert_eq!(pos(&[0x00, 0x80]), Ok(vec![0x00, 0x80]));
        assert_eq!(pos(&[0x7f]), Ok(vec![0x7f]));
        assert_eq!(Der::new(&[0x02, 0x01, 0x03]).integer_is(3), Ok(true));
        assert_eq!(Der::new(&[0x02, 0x01, 0x01]).integer_is(3), Ok(false));
        assert_eq!(
            Der::new(&[0x01, 0x01, 0x03]).integer_is(3),
            Err(Error::BadDer)
        );
    }

    #[test]
    fn checks_booleans_and_bit_strings() {
        assert_eq!(Der::new(&[0x01, 0x01, 0xff]).boolean_true(), Ok(()));
        assert_eq!(
            Der::new(&[0x01, 0x01, 0x00]).boolean_true(),
            Err(Error::BadDer)
        );
        assert_eq!(
            Der::new(&[0x01, 0x01, 0x01]).boolean_true(),
            Err(Error::BadDer)
        );
        assert_eq!(
            Der::new(&[0x03, 0x02, 0x00, 0xaa]).bit_string(),
            Ok(&[0xaa][..])
        );
        assert_eq!(
            Der::new(&[0x03, 0x02, 0x01, 0xaa]).bit_string(),
            Err(Error::BadDer)
        );
        assert_eq!(Der::new(&[0x03, 0x00]).bit_string(), Err(Error::BadDer));
        assert_eq!(
            Der::new(&[0x03, 0x02, 0x07, 0x80]).named_bits(),
            Ok(&[0x80][..])
        );
        assert_eq!(Der::new(&[0x03, 0x01, 0x00]).named_bits(), Ok(&[][..]));
        assert_eq!(
            Der::new(&[0x03, 0x02, 0x06, 0x80]).named_bits(),
            Err(Error::BadDer)
        );
        assert_eq!(
            Der::new(&[0x03, 0x02, 0x07, 0x81]).named_bits(),
            Err(Error::BadDer)
        );
        assert_eq!(
            Der::new(&[0x03, 0x01, 0x01]).named_bits(),
            Err(Error::BadDer)
        );
    }

    #[test]
    fn checks_oids() {
        let oid = |c: &[u8]| Der::new(&tlv(OID, c)).oid().map(<[u8]>::to_vec);
        assert_eq!(oid(&[0x55, 0x1d, 0x0f]), Ok(vec![0x55, 0x1d, 0x0f]));
        assert_eq!(oid(&[]), Err(Error::BadDer));
        assert_eq!(oid(&[0x55, 0x80, 0x01]), Err(Error::BadDer));
        assert_eq!(oid(&[0x55, 0x81]), Err(Error::BadDer));
    }

    #[test]
    fn reads_algorithm_identifiers() {
        let oid = tlv(OID, &[0x2a, 0x03]);
        let null = tlv(NULL, &[]);
        let bare = seq(&[&oid]);
        let (o, p) = Der::new(&bare).algorithm().unwrap();
        assert_eq!((o, p), (&[0x2a, 0x03][..], None));
        assert!(absent_or_null(p));
        let both = seq(&[&oid, &null]);
        let (_, p) = Der::new(&both).algorithm().unwrap();
        assert!(absent_or_null(p));
        let other = seq(&[&oid, &oid]);
        assert!(!absent_or_null(Der::new(&other).algorithm().unwrap().1));
        let three = seq(&[&oid, &null, &null]);
        assert_eq!(Der::new(&three).algorithm(), Err(Error::TrailingBytes));
    }

    #[test]
    fn finds_listed_oids() {
        let a = seq(&[&tlv(OID, &[0x2a, 0x01]), &tlv(NULL, &[])]);
        let b = seq(&[&tlv(OID, &[0x2a, 0x02])]);
        let list = [a, b].concat();
        assert_eq!(lists_oid(&list, &[0x2a, 0x02]), Ok(true));
        assert_eq!(lists_oid(&list, &[0x2a, 0x03]), Ok(false));
        assert_eq!(lists_oid(&[], &[0x2a, 0x03]), Ok(false));
    }

    fn sig(r: &[u8], s: &[u8]) -> Vec<u8> {
        seq(&[&tlv(INTEGER, r), &tlv(INTEGER, s)])
    }

    #[test]
    fn parses_ecdsa_signatures() {
        let (r, s) = ecdsa_signature::<4>(&sig(&[0x00, 0x80, 1, 2, 3], &[0x05])).unwrap();
        assert_eq!(r, [0x80, 1, 2, 3]);
        assert_eq!(s, [0, 0, 0, 5]);
    }

    #[test]
    fn rejects_bad_ecdsa_signatures() {
        assert_eq!(
            ecdsa_signature::<4>(&sig(&[0x00, 0x01], &[1])),
            Err(Error::BadDer)
        );
        assert_eq!(
            ecdsa_signature::<4>(&sig(&[0x81], &[1])),
            Err(Error::BadDer)
        );
        assert_eq!(
            ecdsa_signature::<4>(&sig(&[0x00], &[1])),
            Err(Error::BadDer)
        );
        assert_eq!(ecdsa_signature::<4>(&sig(&[], &[1])), Err(Error::BadDer));
        assert_eq!(
            ecdsa_signature::<4>(&sig(&[1, 2, 3, 4, 5], &[1])),
            Err(Error::OutOfRange)
        );
        assert_eq!(
            ecdsa_signature::<4>(&sig(&[0x00, 0x80, 0, 0, 0, 0], &[1])),
            Err(Error::OutOfRange)
        );
        let mut trailing = sig(&[1], &[1]);
        trailing.push(0);
        assert_eq!(ecdsa_signature::<4>(&trailing), Err(Error::TrailingBytes));
        let three = seq(&[
            &tlv(INTEGER, &[1]),
            &tlv(INTEGER, &[1]),
            &tlv(INTEGER, &[1]),
        ]);
        assert_eq!(ecdsa_signature::<4>(&three), Err(Error::TrailingBytes));
        let one = seq(&[&tlv(INTEGER, &[1])]);
        assert_eq!(ecdsa_signature::<4>(&one), Err(Error::Truncated));
    }

    #[test]
    fn parses_real_signatures() {
        let f = happy_path();
        assert!(ecdsa_signature::<32>(&f.signature).is_ok());
    }
}

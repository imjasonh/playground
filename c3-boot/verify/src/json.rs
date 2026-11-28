//! JSON in the two profiles that Sigstore's TUF repository needs.
//!
//! [`Mode::Canonical`] is TUF's canonical JSON, the form that root and
//! targets signatures cover: no whitespace, object keys in strictly
//! increasing byte order, and strings written raw. A string value may hold
//! control bytes, but an object key never does. [`Mode::Strict`] is
//! RFC 8259 JSON, for `trusted_root.json`, with no duplicate keys.
//!
//! Both profiles are narrower than their standards, and
//! `docs/formats.md` lists the differences: strings have no escape
//! sequences, numbers are non-negative integers of at most 19 digits, and
//! containers nest at most [`MAX_DEPTH`] deep. Sigstore's metadata fits.
//!
//! [`parse`] checks a whole document in one pass. The navigation methods on
//! [`Value`] then read the checked bytes without copying them.

use crate::tuf::TufError;

/// The most containers that can be open at once.
pub const MAX_DEPTH: usize = 16;
/// The most digits a number can have, so that every number fits in a `u64`.
pub const MAX_DIGITS: usize = 19;

/// Which JSON profile a document must follow.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Mode {
    /// RFC 8259 JSON with no duplicate keys.
    Strict,
    /// TUF's canonical JSON. Its object keys have no control bytes.
    Canonical,
}

/// One value in a document that [`parse`] accepted: its bytes, from its
/// first byte to its last.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Value<'a> {
    bytes: &'a [u8],
}

fn is_ws(b: u8) -> bool {
    matches!(b, b' ' | b'\t' | b'\n' | b'\r')
}

fn skip_ws(doc: &[u8], pos: usize) -> usize {
    let rest = doc.get(pos..).unwrap_or(&[]);
    let n = rest.iter().take_while(|&&b| is_ws(b)).count();
    pos.saturating_add(n)
}

fn skip_ws_in(doc: &[u8], pos: usize, mode: Mode) -> usize {
    match mode {
        Mode::Strict => skip_ws(doc, pos),
        Mode::Canonical => pos,
    }
}

fn next(pos: usize) -> Result<usize, TufError> {
    pos.checked_add(1).ok_or(TufError::Json)
}

/// The position after the string that starts with the quote at `pos`.
fn string_end(doc: &[u8], pos: usize, mode: Mode) -> Result<usize, TufError> {
    let body_start = next(pos)?;
    let body = doc.get(body_start..).ok_or(TufError::Json)?;
    for (i, &b) in body.iter().enumerate() {
        if b == b'"' {
            return body_start
                .checked_add(i)
                .ok_or(TufError::Json)
                .and_then(next);
        }
        if b == b'\\' || (mode == Mode::Strict && b < 0x20) {
            return Err(TufError::Json);
        }
    }
    Err(TufError::Json)
}

/// The position after the number that starts with the digit at `pos`.
fn number_end(doc: &[u8], pos: usize) -> Result<usize, TufError> {
    let rest = doc.get(pos..).ok_or(TufError::Json)?;
    let digits = rest.iter().take_while(|b| b.is_ascii_digit()).count();
    let leading_zero = rest.first() == Some(&b'0') && digits > 1;
    if digits == 0 || digits > MAX_DIGITS || leading_zero {
        return Err(TufError::Json);
    }
    pos.checked_add(digits).ok_or(TufError::Json)
}

/// The position after the `true`, `false`, or `null` at `pos`.
fn literal_end(doc: &[u8], pos: usize) -> Result<usize, TufError> {
    let rest = doc.get(pos..).ok_or(TufError::Json)?;
    for word in [&b"true"[..], b"false", b"null"] {
        if rest.starts_with(word) {
            return pos.checked_add(word.len()).ok_or(TufError::Json);
        }
    }
    Err(TufError::Json)
}

/// The position after an object key and its colon, with `pos` at the key's
/// opening quote.
fn key_end(doc: &[u8], pos: usize, mode: Mode) -> Result<usize, TufError> {
    if doc.get(pos) != Some(&b'"') {
        return Err(TufError::Json);
    }
    let pos = skip_ws_in(doc, string_end(doc, pos, mode)?, mode);
    if doc.get(pos) != Some(&b':') {
        return Err(TufError::Json);
    }
    Ok(skip_ws_in(doc, next(pos)?, mode))
}

/// Checks an object's keys: strictly increasing in canonical mode, and
/// pairwise distinct in strict mode.
fn check_keys(object: &[u8], mode: Mode) -> Result<(), TufError> {
    let mut members = Value { bytes: object }.members()?;
    let mut previous: Option<&[u8]> = None;
    while let Some((key, _)) = members.next_member()? {
        let ok = match mode {
            Mode::Canonical => previous.is_none_or(|p| p < key),
            Mode::Strict => {
                let mut later = members.clone();
                let mut unique = true;
                while let Some((other, _)) = later.next_member()? {
                    unique &= other != key;
                }
                unique
            }
        };
        if !ok {
            return Err(TufError::Json);
        }
        previous = Some(key);
    }
    Ok(())
}

#[derive(Clone, Copy)]
struct Frame {
    object: bool,
    start: usize,
}

/// Checks that `doc` is one JSON value in `mode`'s profile and returns it.
///
/// Strict mode allows whitespace around the value and between tokens;
/// canonical mode allows none.
pub fn parse(doc: &[u8], mode: Mode) -> Result<Value<'_>, TufError> {
    let mut stack = [Frame {
        object: false,
        start: 0,
    }; MAX_DEPTH];
    let mut depth = 0usize;
    let start = skip_ws_in(doc, 0, mode);
    let mut pos = start;
    // Each pass reads one value, then the closing brackets and the comma
    // after it, so each pass reads at least one byte.
    for _ in 0..=doc.len() {
        let b = *doc.get(pos).ok_or(TufError::Json)?;
        match b {
            b'{' | b'[' => {
                let frame = stack.get_mut(depth).ok_or(TufError::Json)?;
                *frame = Frame {
                    object: b == b'{',
                    start: pos,
                };
                depth = depth.checked_add(1).ok_or(TufError::Json)?;
                pos = skip_ws_in(doc, next(pos)?, mode);
                let close = if b == b'{' { b'}' } else { b']' };
                if doc.get(pos) != Some(&close) {
                    if b == b'{' {
                        pos = key_end(doc, pos, mode)?;
                    }
                    continue;
                }
            }
            b'"' => pos = string_end(doc, pos, mode)?,
            b'0'..=b'9' => pos = number_end(doc, pos)?,
            b't' | b'f' | b'n' => pos = literal_end(doc, pos)?,
            _ => return Err(TufError::Json),
        }
        for _ in 0..=MAX_DEPTH {
            let end = pos;
            pos = skip_ws_in(doc, pos, mode);
            let Some(top) = depth.checked_sub(1) else {
                if pos != doc.len() {
                    return Err(TufError::Json);
                }
                let bytes = doc.get(start..end).ok_or(TufError::Json)?;
                return Ok(Value { bytes });
            };
            let frame = *stack.get(top).ok_or(TufError::Json)?;
            match doc.get(pos) {
                Some(b',') => {
                    pos = skip_ws_in(doc, next(pos)?, mode);
                    if frame.object {
                        pos = key_end(doc, pos, mode)?;
                    }
                    break;
                }
                Some(b'}') if frame.object => {
                    pos = next(pos)?;
                    check_keys(doc.get(frame.start..pos).ok_or(TufError::Json)?, mode)?;
                    depth = top;
                }
                Some(b']') if !frame.object => {
                    pos = next(pos)?;
                    depth = top;
                }
                _ => return Err(TufError::Json),
            }
        }
    }
    Err(TufError::Json)
}

/// The position after the value that starts at `pos` in a checked document.
fn value_end(doc: &[u8], pos: usize) -> Result<usize, TufError> {
    match doc.get(pos) {
        Some(b'"') => string_end(doc, pos, Mode::Canonical),
        Some(b'0'..=b'9') => number_end(doc, pos),
        Some(b't' | b'f' | b'n') => literal_end(doc, pos),
        Some(b'{' | b'[') => {
            let mut depth = 0usize;
            let mut i = pos;
            while let Some(&b) = doc.get(i) {
                match b {
                    b'"' => {
                        i = string_end(doc, i, Mode::Canonical)?;
                        continue;
                    }
                    b'{' | b'[' => depth = depth.checked_add(1).ok_or(TufError::Json)?,
                    b'}' | b']' => {
                        depth = depth.checked_sub(1).ok_or(TufError::Json)?;
                        if depth == 0 {
                            return next(i);
                        }
                    }
                    _ => {}
                }
                i = next(i)?;
            }
            Err(TufError::Json)
        }
        _ => Err(TufError::Json),
    }
}

/// Reads the value at `pos` and the comma after it, if any. Returns the value
/// and the position after both.
fn read_item(doc: &[u8], pos: usize) -> Result<(Value<'_>, usize), TufError> {
    let end = value_end(doc, pos)?;
    let value = Value {
        bytes: doc.get(pos..end).ok_or(TufError::Json)?,
    };
    let mut after = skip_ws(doc, end);
    if doc.get(after) == Some(&b',') {
        after = skip_ws(doc, next(after)?);
    }
    Ok((value, after))
}

/// A cursor over an object's members.
#[derive(Clone, Debug)]
pub struct Members<'a> {
    bytes: &'a [u8],
    pos: usize,
}

impl<'a> Members<'a> {
    /// The next key and value, or `None` after the last member.
    pub fn next_member(&mut self) -> Result<Option<(&'a [u8], Value<'a>)>, TufError> {
        if self.bytes.get(self.pos) == Some(&b'}') {
            return Ok(None);
        }
        let key_start = next(self.pos)?;
        let key_close = string_end(self.bytes, self.pos, Mode::Canonical)?
            .checked_sub(1)
            .ok_or(TufError::Json)?;
        let key = self.bytes.get(key_start..key_close).ok_or(TufError::Json)?;
        let value_start = key_end(self.bytes, self.pos, Mode::Strict)?;
        let (value, after) = read_item(self.bytes, value_start)?;
        self.pos = after;
        Ok(Some((key, value)))
    }
}

/// A cursor over an array's elements.
#[derive(Clone, Debug)]
pub struct Elements<'a> {
    bytes: &'a [u8],
    pos: usize,
}

impl<'a> Elements<'a> {
    /// The next element, or `None` after the last one.
    pub fn next_element(&mut self) -> Result<Option<Value<'a>>, TufError> {
        if self.bytes.get(self.pos) == Some(&b']') {
            return Ok(None);
        }
        let (value, after) = read_item(self.bytes, self.pos)?;
        self.pos = after;
        Ok(Some(value))
    }
}

impl<'a> Value<'a> {
    /// The value's bytes in its document.
    pub fn bytes(&self) -> &'a [u8] {
        self.bytes
    }

    /// The object's members. Fails with [`TufError::Schema`] if the value
    /// isn't an object.
    pub fn members(&self) -> Result<Members<'a>, TufError> {
        if self.bytes.first() != Some(&b'{') {
            return Err(TufError::Schema);
        }
        Ok(Members {
            bytes: self.bytes,
            pos: skip_ws(self.bytes, 1),
        })
    }

    /// The array's elements. Fails with [`TufError::Schema`] if the value
    /// isn't an array.
    pub fn elements(&self) -> Result<Elements<'a>, TufError> {
        if self.bytes.first() != Some(&b'[') {
            return Err(TufError::Schema);
        }
        Ok(Elements {
            bytes: self.bytes,
            pos: skip_ws(self.bytes, 1),
        })
    }

    /// The object's value for `key`, or `None` if it has no such member.
    pub fn get(&self, key: &[u8]) -> Result<Option<Value<'a>>, TufError> {
        let mut members = self.members()?;
        while let Some((k, v)) = members.next_member()? {
            if k == key {
                return Ok(Some(v));
            }
        }
        Ok(None)
    }

    /// The object's value for `key`. Fails with [`TufError::Schema`] if the
    /// object has no such member.
    pub fn field(&self, key: &[u8]) -> Result<Value<'a>, TufError> {
        self.get(key)?.ok_or(TufError::Schema)
    }

    /// The string's bytes, without the quotes.
    pub fn str(&self) -> Result<&'a [u8], TufError> {
        match self.bytes {
            [b'"', body @ .., b'"'] => Ok(body),
            _ => Err(TufError::Schema),
        }
    }

    /// The number's value.
    pub fn u64(&self) -> Result<u64, TufError> {
        let digits = self.bytes;
        if digits.is_empty() || !digits.iter().all(u8::is_ascii_digit) {
            return Err(TufError::Schema);
        }
        let mut n = 0u64;
        for &d in digits {
            n = n
                .checked_mul(10)
                .and_then(|n| n.checked_add(u64::from(d.wrapping_sub(b'0'))))
                .ok_or(TufError::Schema)?;
        }
        Ok(n)
    }
}

#[cfg(test)]
#[allow(clippy::arithmetic_side_effects, clippy::indexing_slicing)]
mod tests {
    use super::*;

    fn strict(s: &str) -> Result<Value<'_>, TufError> {
        parse(s.as_bytes(), Mode::Strict)
    }

    fn canonical(s: &str) -> Result<Value<'_>, TufError> {
        parse(s.as_bytes(), Mode::Canonical)
    }

    #[test]
    fn accepts_profile() {
        for doc in [
            "0",
            "123",
            "true",
            "null",
            "\"\"",
            "[]",
            "{}",
            "[1,[2,[]],{\"a\":false}]",
            "{\"a\":1,\"b\":{\"c\":\"x\"}}",
            "9999999999999999999",
        ] {
            assert!(canonical(doc).is_ok(), "{doc}");
            assert!(strict(doc).is_ok(), "{doc}");
        }
        assert!(strict(" { \"b\" : 1 ,\n\t\"a\" : [ ] } \r\n").is_ok());
        assert!(canonical("\"line\nfeed\"").is_ok());
    }

    #[test]
    fn rejects_outside_profile() {
        for doc in [
            "",
            " ",
            "01",
            "-1",
            "1.5",
            "1e3",
            "1234567890123456789012",
            "\"a\\\"b\"",
            "\"\\n\"",
            "[1,]",
            "[,1]",
            "{\"a\":1,}",
            "{\"a\"}",
            "{\"a\":}",
            "{1:2}",
            "[1 2]",
            "tru",
            "nul",
            "[]]",
            "[[]",
            "{}{}",
            "\"open",
            "{\"a\":1,\"a\":2}",
        ] {
            assert_eq!(strict(doc), Err(TufError::Json), "strict {doc:?}");
            assert_eq!(canonical(doc), Err(TufError::Json), "canonical {doc:?}");
        }
        assert_eq!(canonical(" 1"), Err(TufError::Json));
        assert_eq!(canonical("[1, 2]"), Err(TufError::Json));
        assert_eq!(canonical("{\"b\":1,\"a\":2}"), Err(TufError::Json));
        assert!(strict("{\"b\":1,\"a\":2}").is_ok());
        assert_eq!(strict("\"line\nfeed\""), Err(TufError::Json));
    }

    #[test]
    fn rejects_control_bytes_in_keys() {
        assert_eq!(canonical("{\"\u{1}\":1}"), Err(TufError::Json));
        assert_eq!(strict("{\"\u{1}\":1}"), Err(TufError::Json));
        assert!(canonical("\"\u{1}\"").is_ok());
        assert!(canonical("{\"a\":\"\u{1}\"}").is_ok());
    }

    #[test]
    fn limits_depth() {
        let ok = format!("{}{}", "[".repeat(MAX_DEPTH), "]".repeat(MAX_DEPTH));
        assert!(canonical(&ok).is_ok());
        let deep = format!("{}{}", "[".repeat(MAX_DEPTH + 1), "]".repeat(MAX_DEPTH + 1));
        assert_eq!(canonical(&deep), Err(TufError::Json));
    }

    #[test]
    fn navigates() {
        let doc = strict(" {\"a\" : [ 1 , \"x\" , {\"b\":true} ] , \"n\": 42 } ").unwrap();
        assert_eq!(doc.field(b"n").unwrap().u64(), Ok(42));
        assert_eq!(doc.get(b"z"), Ok(None));
        assert_eq!(doc.field(b"z"), Err(TufError::Schema));
        let mut items = doc.field(b"a").unwrap().elements().unwrap();
        assert_eq!(items.next_element().unwrap().unwrap().u64(), Ok(1));
        assert_eq!(items.next_element().unwrap().unwrap().str(), Ok(&b"x"[..]));
        let obj = items.next_element().unwrap().unwrap();
        assert_eq!(obj.field(b"b").unwrap().bytes(), b"true");
        assert_eq!(items.next_element(), Ok(None));
        assert_eq!(doc.str(), Err(TufError::Schema));
        assert_eq!(doc.field(b"a").unwrap().get(b"x"), Err(TufError::Schema));
    }
}

//! Just enough HTTP/1.1 to forward one request and its response: message
//! heads, body framing, and copying a body while hashing its content.

use std::io::{self, BufRead, Read, Write};

const MAX_HEAD: usize = 64 << 10;

/// A request line or status line and its header fields.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Head {
    pub line: String,
    pub headers: Vec<(String, String)>,
}

impl Head {
    pub fn get(&self, name: &str) -> Option<&str> {
        self.headers
            .iter()
            .find(|(k, _)| k.eq_ignore_ascii_case(name))
            .map(|(_, v)| v.as_str())
    }

    /// Splits a request line into method and target.
    pub fn request(&self) -> io::Result<(&str, &str)> {
        let mut parts = self.line.split(' ');
        match (parts.next(), parts.next(), parts.next()) {
            (Some(m), Some(t), Some(v)) if v.starts_with("HTTP/1.") => Ok((m, t)),
            _ => Err(invalid("malformed request line")),
        }
    }

    pub fn status(&self) -> io::Result<u16> {
        let mut parts = self.line.split(' ');
        match (parts.next(), parts.next()) {
            (Some(v), Some(code)) if v.starts_with("HTTP/1.") => {
                code.parse().map_err(|_| invalid("malformed status line"))
            }
            _ => Err(invalid("malformed status line")),
        }
    }

    pub fn encode(&self) -> Vec<u8> {
        let mut out = format!("{}\r\n", self.line);
        for (k, v) in &self.headers {
            out.push_str(&format!("{k}: {v}\r\n"));
        }
        out.push_str("\r\n");
        out.into_bytes()
    }
}

fn invalid(msg: &str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, msg)
}

fn parse_head(raw: &[u8]) -> io::Result<Head> {
    let text = std::str::from_utf8(raw).map_err(|_| invalid("head isn't UTF-8"))?;
    let mut lines = text.split("\r\n").map(|l| l.trim_end_matches('\n'));
    let line = lines.next().unwrap_or_default().to_string();
    let mut headers = Vec::new();
    for l in lines.filter(|l| !l.is_empty()) {
        let (k, v) = l
            .split_once(':')
            .ok_or_else(|| invalid("malformed header"))?;
        headers.push((k.trim().to_string(), v.trim().to_string()));
    }
    Ok(Head { line, headers })
}

/// Reads a message head. Returns `None` if the stream ends before it starts.
pub fn read_head<R: BufRead>(r: &mut R) -> io::Result<Option<Head>> {
    let mut raw = Vec::new();
    loop {
        let start = raw.len();
        if r.read_until(b'\n', &mut raw)? == 0 {
            return if raw.is_empty() {
                Ok(None)
            } else {
                Err(io::ErrorKind::UnexpectedEof.into())
            };
        }
        if raw.len() > MAX_HEAD {
            return Err(invalid("head too large"));
        }
        if raw[start..] == *b"\r\n" || raw[start..] == *b"\n" {
            if start == 0 {
                raw.clear();
                continue;
            }
            return parse_head(&raw[..start]).map(Some);
        }
    }
}

/// Reads a message head one byte at a time, so that nothing after it is
/// consumed from `r`.
pub fn read_head_exact<R: Read>(r: &mut R) -> io::Result<Option<Head>> {
    let mut raw = Vec::new();
    let mut byte = [0u8; 1];
    while !raw.ends_with(b"\r\n\r\n") {
        if r.read(&mut byte)? == 0 {
            return if raw.is_empty() {
                Ok(None)
            } else {
                Err(io::ErrorKind::UnexpectedEof.into())
            };
        }
        raw.push(byte[0]);
        if raw.len() > MAX_HEAD {
            return Err(invalid("head too large"));
        }
    }
    parse_head(&raw[..raw.len() - 4]).map(Some)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Framing {
    Empty,
    Length(u64),
    Chunked,
    /// The body ends when the connection closes.
    Close,
}

fn framing(head: &Head, otherwise: Framing) -> io::Result<Framing> {
    if head
        .get("transfer-encoding")
        .is_some_and(|te| te.to_ascii_lowercase().contains("chunked"))
    {
        return Ok(Framing::Chunked);
    }
    match head.get("content-length") {
        Some(n) => n
            .trim()
            .parse()
            .map(Framing::Length)
            .map_err(|_| invalid("bad Content-Length")),
        None => Ok(otherwise),
    }
}

pub fn request_framing(head: &Head) -> io::Result<Framing> {
    framing(head, Framing::Empty)
}

pub fn response_framing(method: &str, status: u16, head: &Head) -> io::Result<Framing> {
    if method.eq_ignore_ascii_case("HEAD")
        || (100..200).contains(&status)
        || status == 204
        || status == 304
    {
        return Ok(Framing::Empty);
    }
    framing(head, Framing::Close)
}

/// Copies one body from `r` to `w` byte for byte, framing included, and
/// returns the BLAKE3 hash of its decoded content.
pub fn copy_body<R: BufRead + ?Sized, W: Write + ?Sized>(
    r: &mut R,
    w: &mut W,
    framing: Framing,
) -> io::Result<String> {
    let mut hasher = blake3::Hasher::new();
    let mut buf = vec![0u8; 64 << 10];
    let mut copy = |r: &mut R, w: &mut W, mut left: Option<u64>| -> io::Result<()> {
        loop {
            let want = match left {
                Some(0) => return Ok(()),
                Some(n) => buf.len().min(n as usize),
                None => buf.len(),
            };
            let n = r.read(&mut buf[..want])?;
            if n == 0 {
                return match left {
                    None => Ok(()),
                    Some(_) => Err(io::ErrorKind::UnexpectedEof.into()),
                };
            }
            hasher.update(&buf[..n]);
            w.write_all(&buf[..n])?;
            if let Some(l) = left.as_mut() {
                *l -= n as u64;
            }
        }
    };
    match framing {
        Framing::Empty => {}
        Framing::Length(n) => copy(r, w, Some(n))?,
        Framing::Close => copy(r, w, None)?,
        Framing::Chunked => loop {
            let mut line = Vec::new();
            if r.read_until(b'\n', &mut line)? == 0 {
                return Err(io::ErrorKind::UnexpectedEof.into());
            }
            w.write_all(&line)?;
            let size = std::str::from_utf8(&line)
                .ok()
                .and_then(|l| l.split(';').next())
                .and_then(|s| u64::from_str_radix(s.trim(), 16).ok())
                .ok_or_else(|| invalid("bad chunk size"))?;
            if size == 0 {
                loop {
                    let mut trailer = Vec::new();
                    if r.read_until(b'\n', &mut trailer)? == 0 {
                        break;
                    }
                    w.write_all(&trailer)?;
                    if trailer == b"\r\n" || trailer == b"\n" {
                        break;
                    }
                }
                break;
            }
            copy(r, w, Some(size))?;
            let mut crlf = Vec::new();
            r.read_until(b'\n', &mut crlf)?;
            w.write_all(&crlf)?;
        },
    }
    Ok(hasher.finalize().to_hex().to_string())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Cursor;

    #[test]
    fn heads() {
        let mut r =
            Cursor::new(&b"GET http://x/y HTTP/1.1\r\nHost: x\r\nAccept: */*\r\n\r\nrest"[..]);
        let h = read_head(&mut r).unwrap().unwrap();
        assert_eq!(h.request().unwrap(), ("GET", "http://x/y"));
        assert_eq!(h.get("host"), Some("x"));
        let mut rest = String::new();
        r.read_to_string(&mut rest).unwrap();
        assert_eq!(rest, "rest");

        let mut r = Cursor::new(&b"HTTP/1.1 304 Not Modified\r\nETag: \"a\"\r\n\r\n"[..]);
        let h = read_head_exact(&mut r).unwrap().unwrap();
        assert_eq!(h.status().unwrap(), 304);
        assert_eq!(read_head(&mut Cursor::new(&b""[..])).unwrap(), None);
    }

    #[test]
    fn chunked_bodies_hash_their_content() {
        let raw = b"5\r\nhello\r\n1;ext=1\r\n!\r\n0\r\nX-Trailer: y\r\n\r\n";
        let mut out = Vec::new();
        let hash = copy_body(&mut Cursor::new(&raw[..]), &mut out, Framing::Chunked).unwrap();
        assert_eq!(out, raw);
        assert_eq!(hash, blake3::hash(b"hello!").to_hex().to_string());
        let other = b"6\r\nhello!\r\n0\r\n\r\n";
        let same = copy_body(
            &mut Cursor::new(&other[..]),
            &mut Vec::new(),
            Framing::Chunked,
        )
        .unwrap();
        assert_eq!(hash, same);
    }

    #[test]
    fn framing_rules() {
        let head = |h: &[(&str, &str)]| Head {
            line: "HTTP/1.1 200 OK".into(),
            headers: h
                .iter()
                .map(|(k, v)| (k.to_string(), v.to_string()))
                .collect(),
        };
        assert_eq!(
            response_framing("GET", 200, &head(&[])).unwrap(),
            Framing::Close
        );
        assert_eq!(
            response_framing("GET", 200, &head(&[("Content-Length", "3")])).unwrap(),
            Framing::Length(3)
        );
        assert_eq!(
            response_framing("GET", 200, &head(&[("Transfer-Encoding", "chunked")])).unwrap(),
            Framing::Chunked
        );
        assert_eq!(
            response_framing("HEAD", 200, &head(&[("Content-Length", "3")])).unwrap(),
            Framing::Empty
        );
        assert_eq!(
            response_framing("GET", 304, &head(&[])).unwrap(),
            Framing::Empty
        );
        assert_eq!(request_framing(&head(&[])).unwrap(), Framing::Empty);
        let mut short = Cursor::new(&b"ab"[..]);
        assert!(copy_body(&mut short, &mut Vec::new(), Framing::Length(3)).is_err());
    }
}

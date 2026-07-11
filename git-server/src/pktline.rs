//! pkt-line framing (gitprotocol-common(5)).
//!
//! Every git transport frames its streams in *pkt-lines*: a 4-hex-digit length
//! prefix (including the prefix itself) followed by payload, plus three
//! special zero-length frames — `0000` (flush), `0001` (delimiter, protocol
//! v2) and `0002` (response-end, protocol v2). Maximum payload is 65516 bytes.
//!
//! The parser here is incremental: [`PktParser`] consumes arbitrary byte
//! chunks (however the network delivered them) and yields complete frames,
//! which is what lets receive-pack parse a push while streaming it to R2
//! without buffering the request body.

/// Maximum payload bytes in one pkt-line (65520 minus the 4-byte prefix).
pub const MAX_PKT_PAYLOAD: usize = 65516;

/// One decoded pkt-line frame.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Pkt {
    /// `0000` — flush packet: end of a section or message.
    Flush,
    /// `0001` — delimiter packet (protocol v2).
    Delim,
    /// `0002` — response-end packet (protocol v2 stateless-connect).
    ResponseEnd,
    /// A data packet with its payload.
    Data(Vec<u8>),
}

impl Pkt {
    /// Payload as UTF-8 with any trailing newline removed, for line-oriented
    /// command parsing. Returns `None` for non-data or non-UTF-8 frames.
    pub fn as_text(&self) -> Option<&str> {
        match self {
            Pkt::Data(bytes) => {
                let s = std::str::from_utf8(bytes).ok()?;
                Some(s.strip_suffix('\n').unwrap_or(s))
            }
            _ => None,
        }
    }
}

/// Encode one data pkt-line.
pub fn data_pkt(payload: &[u8]) -> Vec<u8> {
    debug_assert!(payload.len() <= MAX_PKT_PAYLOAD);
    let mut out = Vec::with_capacity(payload.len() + 4);
    out.extend_from_slice(format!("{:04x}", payload.len() + 4).as_bytes());
    out.extend_from_slice(payload);
    out
}

/// Encode a textual pkt-line, appending the conventional trailing `\n`.
pub fn text_pkt(line: &str) -> Vec<u8> {
    let mut payload = Vec::with_capacity(line.len() + 1);
    payload.extend_from_slice(line.as_bytes());
    payload.push(b'\n');
    data_pkt(&payload)
}

/// The `0000` flush packet.
pub fn flush_pkt() -> &'static [u8] {
    b"0000"
}

/// The `0001` delimiter packet.
pub fn delim_pkt() -> &'static [u8] {
    b"0001"
}

/// The `0002` response-end packet.
pub fn response_end_pkt() -> &'static [u8] {
    b"0002"
}

/// Side-band-64k channel numbers (gitprotocol-pack(5)).
pub mod band {
    /// Pack data.
    pub const DATA: u8 = 1;
    /// Progress messages, shown to the user by the client.
    pub const PROGRESS: u8 = 2;
    /// Fatal error message; client aborts.
    pub const ERROR: u8 = 3;
}

/// Append `payload` split across side-band data pkt-lines on `channel`.
pub fn write_band_pkts(out: &mut Vec<u8>, channel: u8, payload: &[u8]) {
    BufPktWriter { buf: out }.band(channel, payload);
}

/// Writable sink for pkt-line framed output.
///
/// Protocol handlers write through this trait so extra channels (progress,
/// debug, timing) can be added without threading raw `Vec<u8>` appends.
/// [`BufPktWriter`] is the in-memory implementation used today; a streaming
/// sink can be added later without changing call sites that take `&mut dyn
/// PktWriter`.
pub trait PktWriter {
    /// Append one already-framed pkt-line (or a flush/delim/response-end).
    fn write_raw(&mut self, framed: &[u8]);

    /// Encode and write one data pkt-line.
    fn data(&mut self, payload: &[u8]) {
        let pkt = data_pkt(payload);
        self.write_raw(&pkt);
    }

    /// Encode and write one textual pkt-line (trailing `\n` added).
    fn text(&mut self, line: &str) {
        let pkt = text_pkt(line);
        self.write_raw(&pkt);
    }

    /// Write a `0000` flush packet.
    fn flush_pkt(&mut self) {
        self.write_raw(flush_pkt());
    }

    /// Write a `0001` delimiter packet.
    fn delim_pkt(&mut self) {
        self.write_raw(delim_pkt());
    }

    /// Write a `0002` response-end packet.
    fn response_end_pkt(&mut self) {
        self.write_raw(response_end_pkt());
    }

    /// Split `payload` across side-band pkt-lines on `channel`.
    fn band(&mut self, channel: u8, payload: &[u8]) {
        for chunk in payload.chunks(MAX_PKT_PAYLOAD - 1) {
            let mut buf = Vec::with_capacity(chunk.len() + 1);
            buf.push(channel);
            buf.extend_from_slice(chunk);
            self.data(&buf);
        }
    }

    /// Side-band PROGRESS (band 2). Appends `\r\n` when `msg` has no newline,
    /// matching git's progress-line convention.
    fn progress(&mut self, msg: &str) {
        let mut payload = Vec::with_capacity(msg.len() + 2);
        payload.extend_from_slice(msg.as_bytes());
        if !msg.ends_with('\n') {
            payload.extend_from_slice(b"\r\n");
        }
        self.band(band::PROGRESS, &payload);
    }

    /// Side-band ERROR (band 3).
    fn error_band(&mut self, msg: &str) {
        self.band(band::ERROR, msg.as_bytes());
    }
}

/// [`PktWriter`] that appends into a byte buffer.
pub struct BufPktWriter<'a> {
    pub buf: &'a mut Vec<u8>,
}

impl BufPktWriter<'_> {
    pub fn new(buf: &mut Vec<u8>) -> BufPktWriter<'_> {
        BufPktWriter { buf }
    }
}

impl PktWriter for BufPktWriter<'_> {
    fn write_raw(&mut self, framed: &[u8]) {
        self.buf.extend_from_slice(framed);
    }
}

impl PktWriter for Vec<u8> {
    fn write_raw(&mut self, framed: &[u8]) {
        self.extend_from_slice(framed);
    }
}

/// Errors from the incremental parser.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PktError {
    /// Length prefix was not 4 hex digits.
    BadLength([u8; 4]),
    /// Length was 4..8, which is reserved/invalid.
    ReservedLength(usize),
}

impl std::fmt::Display for PktError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PktError::BadLength(b) => write!(f, "invalid pkt-line length prefix {:?}", b),
            PktError::ReservedLength(n) => write!(f, "reserved pkt-line length {n}"),
        }
    }
}

impl std::error::Error for PktError {}

/// Incremental pkt-line parser. Feed it byte chunks; poll frames out.
#[derive(Default)]
pub struct PktParser {
    buf: Vec<u8>,
    /// Read cursor into `buf`; consumed bytes are compacted away lazily.
    pos: usize,
}

impl PktParser {
    pub fn new() -> Self {
        Self::default()
    }

    /// Add newly received bytes.
    pub fn feed(&mut self, bytes: &[u8]) {
        // Compact occasionally so a long stream doesn't grow the buffer.
        if self.pos > 0 && self.pos == self.buf.len() {
            self.buf.clear();
            self.pos = 0;
        } else if self.pos > 64 * 1024 {
            self.buf.drain(..self.pos);
            self.pos = 0;
        }
        self.buf.extend_from_slice(bytes);
    }

    /// Try to decode the next complete frame. `Ok(None)` means "need more
    /// bytes".
    pub fn next_pkt(&mut self) -> Result<Option<Pkt>, PktError> {
        let avail = &self.buf[self.pos..];
        if avail.len() < 4 {
            return Ok(None);
        }
        let mut prefix = [0u8; 4];
        prefix.copy_from_slice(&avail[..4]);
        let len = parse_hex4(&prefix).ok_or(PktError::BadLength(prefix))?;
        match len {
            0 => {
                self.pos += 4;
                Ok(Some(Pkt::Flush))
            }
            1 => {
                self.pos += 4;
                Ok(Some(Pkt::Delim))
            }
            2 => {
                self.pos += 4;
                Ok(Some(Pkt::ResponseEnd))
            }
            3 => Err(PktError::ReservedLength(3)),
            n => {
                if avail.len() < n {
                    return Ok(None);
                }
                let payload = avail[4..n].to_vec();
                self.pos += n;
                Ok(Some(Pkt::Data(payload)))
            }
        }
    }

    /// Bytes fed but not yet consumed as frames (e.g. the raw pack stream that
    /// follows the pkt-line command section of a push). Consumes them.
    pub fn take_remainder(&mut self) -> Vec<u8> {
        let rest = self.buf[self.pos..].to_vec();
        self.buf.clear();
        self.pos = 0;
        rest
    }
}

fn parse_hex4(b: &[u8; 4]) -> Option<usize> {
    let mut n = 0usize;
    for &c in b {
        let d = (c as char).to_digit(16)?;
        n = n * 16 + d as usize;
    }
    Some(n)
}

/// Parse a complete pkt-line buffer into frames (convenience for tests and
/// for fully buffered request bodies).
pub fn parse_all(bytes: &[u8]) -> Result<Vec<Pkt>, PktError> {
    let mut p = PktParser::new();
    p.feed(bytes);
    let mut out = Vec::new();
    while let Some(pkt) = p.next_pkt()? {
        out.push(pkt);
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn roundtrip_text() {
        let enc = text_pkt("command=ls-refs");
        assert_eq!(&enc[..4], b"0014");
        let pkts = parse_all(&enc).unwrap();
        assert_eq!(pkts.len(), 1);
        assert_eq!(pkts[0].as_text(), Some("command=ls-refs"));
    }

    #[test]
    fn specials() {
        let mut buf = Vec::new();
        buf.extend_from_slice(flush_pkt());
        buf.extend_from_slice(delim_pkt());
        buf.extend_from_slice(response_end_pkt());
        let pkts = parse_all(&buf).unwrap();
        assert_eq!(pkts, vec![Pkt::Flush, Pkt::Delim, Pkt::ResponseEnd]);
    }

    #[test]
    fn incremental_across_chunk_boundaries() {
        let enc = text_pkt("hello world this is a pkt");
        let mut p = PktParser::new();
        for b in &enc[..enc.len() - 1] {
            p.feed(std::slice::from_ref(b));
            assert_eq!(p.next_pkt().unwrap(), None);
        }
        p.feed(&enc[enc.len() - 1..]);
        assert_eq!(
            p.next_pkt().unwrap().unwrap().as_text(),
            Some("hello world this is a pkt")
        );
    }

    #[test]
    fn bad_prefix_rejected() {
        let mut p = PktParser::new();
        p.feed(b"zzzz");
        assert!(p.next_pkt().is_err());
    }

    #[test]
    fn band_split() {
        let mut out = Vec::new();
        let payload = vec![7u8; MAX_PKT_PAYLOAD + 10];
        write_band_pkts(&mut out, band::DATA, &payload);
        let pkts = parse_all(&out).unwrap();
        assert_eq!(pkts.len(), 2);
        match (&pkts[0], &pkts[1]) {
            (Pkt::Data(a), Pkt::Data(b)) => {
                assert_eq!(a[0], band::DATA);
                assert_eq!(b[0], band::DATA);
                assert_eq!(a.len() - 1 + b.len() - 1, payload.len());
            }
            _ => panic!("expected data pkts"),
        }
    }

    #[test]
    fn pkt_writer_progress() {
        let mut out = Vec::new();
        out.progress("hello");
        let pkts = parse_all(&out).unwrap();
        assert_eq!(pkts.len(), 1);
        match &pkts[0] {
            Pkt::Data(d) => {
                assert_eq!(d[0], band::PROGRESS);
                assert_eq!(&d[1..], b"hello\r\n");
            }
            _ => panic!("expected data"),
        }
    }
}

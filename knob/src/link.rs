//! Frame codec for the UART between the ESP32-S3 and the ESP32-U4WDH.
//!
//! A frame is `0x7E | type | len_le | payload | crc16_le | 0x7F`.
//! CRC-16 covers type, length, and payload. Length is the payload size.
//! The reader resyncs on a bad CRC by scanning for the next start byte.

use crate::crc::crc16;

pub const SOF: u8 = 0x7E;
pub const EOF: u8 = 0x7F;
/// Largest payload. An OTA chunk is a `u16` sequence plus up to 240 bytes,
/// so the frame has to clear that.
pub const MAX_PAYLOAD: usize = 512;
/// SOF + type + length + payload + crc + EOF.
pub const MAX_FRAME: usize = 7 + MAX_PAYLOAD;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BtState {
    Disconnected = 0,
    Discoverable = 1,
    Connecting = 2,
    Connected = 3,
}

impl BtState {
    fn from_u8(v: u8) -> Option<Self> {
        match v {
            0 => Some(Self::Disconnected),
            1 => Some(Self::Discoverable),
            2 => Some(Self::Connecting),
            3 => Some(Self::Connected),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PlayState {
    Unknown = 0,
    Stopped = 1,
    Playing = 2,
    Paused = 3,
}

impl PlayState {
    fn from_u8(v: u8) -> Option<Self> {
        match v {
            0 => Some(Self::Unknown),
            1 => Some(Self::Stopped),
            2 => Some(Self::Playing),
            3 => Some(Self::Paused),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MetaKind {
    Title = 1,
    Artist = 2,
    Album = 3,
}

impl MetaKind {
    fn from_u8(v: u8) -> Option<Self> {
        match v {
            1 => Some(Self::Title),
            2 => Some(Self::Artist),
            3 => Some(Self::Album),
            _ => None,
        }
    }
}

/// One decoded message. Commands travel S3 to companion. Events travel back.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Msg {
    Ping,
    Pong,
    Play,
    Pause,
    Next,
    Prev,
    VolUp,
    VolDown,
    Pair,
    Disconnect,
    Reboot,
    BtState(BtState),
    PlayState(PlayState),
    Meta {
        kind: MetaKind,
        text: String,
    },
    DeviceName(String),
    Knob(i8),
    /// Ask the other chip about the jack. The S3 does not drive I2S.
    /// `release: true` means the companion owns the DAC.
    Jack {
        release: bool,
    },
    /// Play a sine on the jack. `hz == 0` stops it. The companion ignores
    /// this while an A2DP stream is running.
    Tone {
        hz: u16,
    },
    OtaBegin {
        size: u32,
        crc: u32,
    },
    OtaChunk {
        seq: u16,
        data: Vec<u8>,
    },
    OtaFinish,
    OtaAbort,
    OtaAck {
        seq: u16,
        err: u8,
    },
    Ack(u8),
    Error {
        code: u8,
        text: String,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
enum Kind {
    Ping = 0x01,
    Pong = 0x02,
    Play = 0x10,
    Pause = 0x11,
    Next = 0x12,
    Prev = 0x13,
    VolUp = 0x14,
    VolDown = 0x15,
    Pair = 0x16,
    Disconnect = 0x17,
    Reboot = 0x18,
    BtState = 0x20,
    PlayState = 0x21,
    Meta = 0x22,
    DeviceName = 0x23,
    Knob = 0x24,
    Jack = 0x25,
    Tone = 0x26,
    OtaBegin = 0x30,
    OtaChunk = 0x31,
    OtaFinish = 0x32,
    OtaAbort = 0x33,
    OtaAck = 0x34,
    Ack = 0xFE,
    Error = 0xFF,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LinkError {
    TooLong,
    Truncated,
    BadCrc,
    BadType,
    BadPayload,
}

pub fn encode(msg: &Msg) -> Result<Vec<u8>, LinkError> {
    let mut buf = vec![0u8; MAX_FRAME];
    let n = encode_into(msg, &mut buf)?;
    buf.truncate(n);
    Ok(buf)
}

/// Write one frame into `out`. Returns the byte count.
pub fn encode_into(msg: &Msg, out: &mut [u8]) -> Result<usize, LinkError> {
    if out.len() < 7 {
        return Err(LinkError::TooLong);
    }
    let (kind, n) = write_payload(msg, &mut out[4..])?;
    if n > MAX_PAYLOAD {
        return Err(LinkError::TooLong);
    }
    out[0] = SOF;
    out[1] = kind;
    out[2..4].copy_from_slice(&(n as u16).to_le_bytes());
    let crc = crc16(&out[1..4 + n]);
    out[4 + n..6 + n].copy_from_slice(&crc.to_le_bytes());
    out[6 + n] = EOF;
    Ok(7 + n)
}

fn write_payload(msg: &Msg, out: &mut [u8]) -> Result<(u8, usize), LinkError> {
    let put = |src: &[u8], out: &mut [u8]| -> Result<usize, LinkError> {
        if src.len() > out.len() {
            return Err(LinkError::TooLong);
        }
        out[..src.len()].copy_from_slice(src);
        Ok(src.len())
    };
    let (kind, n) = match msg {
        Msg::Ping => (Kind::Ping, 0),
        Msg::Pong => (Kind::Pong, 0),
        Msg::Play => (Kind::Play, 0),
        Msg::Pause => (Kind::Pause, 0),
        Msg::Next => (Kind::Next, 0),
        Msg::Prev => (Kind::Prev, 0),
        Msg::VolUp => (Kind::VolUp, 0),
        Msg::VolDown => (Kind::VolDown, 0),
        Msg::Pair => (Kind::Pair, 0),
        Msg::Disconnect => (Kind::Disconnect, 0),
        Msg::Reboot => (Kind::Reboot, 0),
        Msg::OtaFinish => (Kind::OtaFinish, 0),
        Msg::OtaAbort => (Kind::OtaAbort, 0),
        Msg::BtState(s) => (Kind::BtState, put(&[*s as u8], out)?),
        Msg::PlayState(s) => (Kind::PlayState, put(&[*s as u8], out)?),
        Msg::Knob(delta) => (Kind::Knob, put(&[*delta as u8], out)?),
        Msg::Jack { release } => (Kind::Jack, put(&[u8::from(*release)], out)?),
        Msg::Ack(kind) => (Kind::Ack, put(&[*kind], out)?),
        Msg::Tone { hz } => (Kind::Tone, put(&hz.to_le_bytes(), out)?),
        Msg::OtaBegin { size, crc } => {
            let mut p = [0u8; 8];
            p[..4].copy_from_slice(&size.to_le_bytes());
            p[4..].copy_from_slice(&crc.to_le_bytes());
            (Kind::OtaBegin, put(&p, out)?)
        }
        Msg::OtaAck { seq, err } => {
            let mut p = [0u8; 3];
            p[..2].copy_from_slice(&seq.to_le_bytes());
            p[2] = *err;
            (Kind::OtaAck, put(&p, out)?)
        }
        Msg::OtaChunk { seq, data } => {
            if out.len() < 2 + data.len() {
                return Err(LinkError::TooLong);
            }
            out[..2].copy_from_slice(&seq.to_le_bytes());
            out[2..2 + data.len()].copy_from_slice(data);
            (Kind::OtaChunk, 2 + data.len())
        }
        Msg::Meta { kind, text } => {
            let b = text.as_bytes();
            if out.len() < 1 + b.len() {
                return Err(LinkError::TooLong);
            }
            out[0] = *kind as u8;
            out[1..1 + b.len()].copy_from_slice(b);
            (Kind::Meta, 1 + b.len())
        }
        Msg::DeviceName(text) => (Kind::DeviceName, put(text.as_bytes(), out)?),
        Msg::Error { code, text } => {
            let b = text.as_bytes();
            if out.len() < 1 + b.len() {
                return Err(LinkError::TooLong);
            }
            out[0] = *code;
            out[1..1 + b.len()].copy_from_slice(b);
            (Kind::Error, 1 + b.len())
        }
    };
    Ok((kind as u8, n))
}

pub fn decode(frame: &[u8]) -> Result<Msg, LinkError> {
    if frame.len() < 7 || frame[0] != SOF || *frame.last().unwrap_or(&0) != EOF {
        return Err(LinkError::Truncated);
    }
    let body = &frame[1..frame.len() - 1];
    if body.len() < 5 {
        return Err(LinkError::Truncated);
    }
    let kind = body[0];
    let len = u16::from_le_bytes([body[1], body[2]]) as usize;
    if body.len() != 3 + len + 2 {
        return Err(LinkError::Truncated);
    }
    let payload = &body[3..3 + len];
    let crc = u16::from_le_bytes([body[3 + len], body[4 + len]]);
    if crc16(&body[..3 + len]) != crc {
        return Err(LinkError::BadCrc);
    }
    decode_body(kind, payload)
}

fn decode_body(kind: u8, payload: &[u8]) -> Result<Msg, LinkError> {
    let text = |bytes: &[u8]| String::from_utf8_lossy(bytes).into_owned();
    match kind {
        x if x == Kind::Ping as u8 && payload.is_empty() => Ok(Msg::Ping),
        x if x == Kind::Pong as u8 && payload.is_empty() => Ok(Msg::Pong),
        x if x == Kind::Play as u8 && payload.is_empty() => Ok(Msg::Play),
        x if x == Kind::Pause as u8 && payload.is_empty() => Ok(Msg::Pause),
        x if x == Kind::Next as u8 && payload.is_empty() => Ok(Msg::Next),
        x if x == Kind::Prev as u8 && payload.is_empty() => Ok(Msg::Prev),
        x if x == Kind::VolUp as u8 && payload.is_empty() => Ok(Msg::VolUp),
        x if x == Kind::VolDown as u8 && payload.is_empty() => Ok(Msg::VolDown),
        x if x == Kind::Pair as u8 && payload.is_empty() => Ok(Msg::Pair),
        x if x == Kind::Disconnect as u8 && payload.is_empty() => Ok(Msg::Disconnect),
        x if x == Kind::Reboot as u8 && payload.is_empty() => Ok(Msg::Reboot),
        x if x == Kind::BtState as u8 => {
            let v = payload.first().copied().ok_or(LinkError::BadPayload)?;
            Ok(Msg::BtState(
                BtState::from_u8(v).ok_or(LinkError::BadPayload)?,
            ))
        }
        x if x == Kind::PlayState as u8 => {
            let v = payload.first().copied().ok_or(LinkError::BadPayload)?;
            Ok(Msg::PlayState(
                PlayState::from_u8(v).ok_or(LinkError::BadPayload)?,
            ))
        }
        x if x == Kind::Meta as u8 => {
            let kind_b = payload.first().copied().ok_or(LinkError::BadPayload)?;
            Ok(Msg::Meta {
                kind: MetaKind::from_u8(kind_b).ok_or(LinkError::BadPayload)?,
                text: text(&payload[1..]),
            })
        }
        x if x == Kind::DeviceName as u8 => Ok(Msg::DeviceName(text(payload))),
        x if x == Kind::Knob as u8 => {
            let v = payload.first().copied().ok_or(LinkError::BadPayload)?;
            Ok(Msg::Knob(v as i8))
        }
        x if x == Kind::Jack as u8 && payload.len() == 1 => Ok(Msg::Jack {
            release: payload[0] != 0,
        }),
        x if x == Kind::Tone as u8 && payload.len() == 2 => Ok(Msg::Tone {
            hz: u16::from_le_bytes(payload.try_into().unwrap()),
        }),
        x if x == Kind::OtaBegin as u8 && payload.len() == 8 => Ok(Msg::OtaBegin {
            size: u32::from_le_bytes(payload[0..4].try_into().unwrap()),
            crc: u32::from_le_bytes(payload[4..8].try_into().unwrap()),
        }),
        x if x == Kind::OtaChunk as u8 && payload.len() >= 2 => Ok(Msg::OtaChunk {
            seq: u16::from_le_bytes(payload[0..2].try_into().unwrap()),
            data: payload[2..].to_vec(),
        }),
        x if x == Kind::OtaFinish as u8 && payload.is_empty() => Ok(Msg::OtaFinish),
        x if x == Kind::OtaAbort as u8 && payload.is_empty() => Ok(Msg::OtaAbort),
        x if x == Kind::OtaAck as u8 && payload.len() == 3 => Ok(Msg::OtaAck {
            seq: u16::from_le_bytes(payload[0..2].try_into().unwrap()),
            err: payload[2],
        }),
        x if x == Kind::Ack as u8 && payload.len() == 1 => Ok(Msg::Ack(payload[0])),
        x if x == Kind::Error as u8 && !payload.is_empty() => Ok(Msg::Error {
            code: payload[0],
            text: text(&payload[1..]),
        }),
        _ => Err(LinkError::BadType),
    }
}

/// Byte stream to frames. Drops a frame whose CRC fails and keeps scanning.
#[derive(Clone, Debug, Default)]
pub struct Decoder {
    buf: Vec<u8>,
}

impl Decoder {
    pub fn new() -> Self {
        Self { buf: Vec::new() }
    }

    pub fn push(&mut self, bytes: &[u8]) -> Vec<Result<Msg, LinkError>> {
        let mut out = Vec::new();
        self.drain_into(bytes, &mut out);
        out
    }

    /// Append decoded frames to `out` without allocating a frame buffer.
    pub fn drain_into(&mut self, bytes: &[u8], out: &mut Vec<Result<Msg, LinkError>>) {
        self.buf.extend_from_slice(bytes);
        loop {
            let Some(start) = self.buf.iter().position(|b| *b == SOF) else {
                self.buf.clear();
                break;
            };
            if start > 0 {
                self.buf.drain(..start);
            }
            if self.buf.len() < 7 {
                break;
            }
            let len = u16::from_le_bytes([self.buf[2], self.buf[3]]) as usize;
            if len > MAX_PAYLOAD {
                self.buf.drain(..1);
                out.push(Err(LinkError::TooLong));
                continue;
            }
            let total = 1 + 3 + len + 2 + 1;
            if self.buf.len() < total {
                break;
            }
            let decoded = decode(&self.buf[..total]);
            self.buf.drain(..total);
            out.push(decoded);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn round_trip_commands_and_metadata() {
        let samples = [
            Msg::Ping,
            Msg::Play,
            Msg::VolDown,
            Msg::Reboot,
            Msg::BtState(BtState::Connected),
            Msg::PlayState(PlayState::Playing),
            Msg::Meta {
                kind: MetaKind::Title,
                text: "Side A".into(),
            },
            Msg::Knob(-1),
            Msg::Jack { release: true },
            Msg::Jack { release: false },
            Msg::Tone { hz: 440 },
            Msg::Tone { hz: 0 },
            Msg::OtaBegin {
                size: 128,
                crc: 0x1122_3344,
            },
            Msg::OtaChunk {
                seq: 3,
                data: vec![9, 8, 7],
            },
            Msg::OtaAck { seq: 3, err: 0 },
            Msg::Error {
                code: 2,
                text: "full".into(),
            },
        ];
        for msg in samples {
            let frame = encode(&msg).unwrap();
            assert_eq!(decode(&frame).unwrap(), msg);
        }
    }

    #[test]
    fn decoder_splits_two_frames_and_skips_noise() {
        let a = encode(&Msg::Ping).unwrap();
        let b = encode(&Msg::Pong).unwrap();
        let mut raw = vec![0x00, 0x11];
        raw.extend_from_slice(&a);
        raw.extend_from_slice(&b);
        let mut dec = Decoder::new();
        let got = dec.push(&raw);
        assert_eq!(got, vec![Ok(Msg::Ping), Ok(Msg::Pong)]);
    }

    #[test]
    fn an_ota_chunk_fits_in_one_frame() {
        let msg = Msg::OtaChunk {
            seq: 1,
            data: vec![0; crate::ble::MAX_OTA_CHUNK],
        };
        assert!(encode(&msg).is_ok());
    }

    #[test]
    fn flipped_crc_is_rejected() {
        let mut frame = encode(&Msg::Next).unwrap();
        let n = frame.len();
        frame[n - 2] ^= 0xFF;
        assert_eq!(decode(&frame), Err(LinkError::BadCrc));
    }
}

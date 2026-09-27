//! Small checksums used by the inter-chip link and BLE OTA.

/// CRC-16/IBM (poly 0xA001, init 0xFFFF). Covers type, length, and payload.
pub fn crc16(data: &[u8]) -> u16 {
    let mut crc: u16 = 0xFFFF;
    for byte in data {
        crc ^= u16::from(*byte);
        for _ in 0..8 {
            if crc & 1 == 1 {
                crc = (crc >> 1) ^ 0xA001;
            } else {
                crc >>= 1;
            }
        }
    }
    crc
}

/// CRC-32/ISO-HDLC (poly 0xEDB88320, init 0xFFFFFFFF, xorout 0xFFFFFFFF).
#[derive(Clone, Debug)]
pub struct Crc32 {
    state: u32,
}

impl Default for Crc32 {
    fn default() -> Self {
        Self { state: 0xFFFF_FFFF }
    }
}

impl Crc32 {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn update(&mut self, data: &[u8]) {
        for byte in data {
            self.state ^= u32::from(*byte);
            for _ in 0..8 {
                if self.state & 1 == 1 {
                    self.state = (self.state >> 1) ^ 0xEDB8_8320;
                } else {
                    self.state >>= 1;
                }
            }
        }
    }

    pub fn finish(&self) -> u32 {
        !self.state
    }
}

#[cfg(test)]
pub(crate) fn crc32(data: &[u8]) -> u32 {
    let mut crc = Crc32::new();
    crc.update(data);
    crc.finish()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn crc32_of_empty_and_known_string() {
        assert_eq!(crc32(b""), 0);
        assert_eq!(crc32(b"123456789"), 0xCBF4_3926);
    }

    #[test]
    fn crc16_changes_when_a_byte_changes() {
        assert_ne!(crc16(b"ping"), crc16(b"pong"));
        assert_eq!(crc16(b"ping"), crc16(b"ping"));
    }
}

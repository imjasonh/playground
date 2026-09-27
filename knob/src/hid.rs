//! BLE HID consumer-control usages for the remote app.
//!
//! The report is two little-endian bytes, the USB HID consumer usage.
//! A zero report releases the key.

pub const VOLUME_UP: u16 = 0x00E9;
pub const VOLUME_DOWN: u16 = 0x00EA;
pub const PLAY_PAUSE: u16 = 0x00CD;
pub const NEXT: u16 = 0x00B5;
pub const PREV: u16 = 0x00B6;

pub fn report(usage: u16) -> [u8; 2] {
    usage.to_le_bytes()
}

pub fn release() -> [u8; 2] {
    [0, 0]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn volume_up_is_little_endian() {
        assert_eq!(report(VOLUME_UP), [0xE9, 0x00]);
        assert_eq!(release(), [0, 0]);
    }
}

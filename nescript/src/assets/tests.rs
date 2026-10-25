use super::*;

#[test]
fn nearest_nes_color_black() {
    assert_eq!(palette::nearest_nes_color(0, 0, 0), 0x0D); // NES black
}

#[test]
fn nearest_nes_color_white() {
    let idx = palette::nearest_nes_color(255, 255, 255);
    assert!(idx == 0x20 || idx == 0x30); // near-white colors
}

#[test]
fn nes_color_table_has_64_entries() {
    assert_eq!(palette::NES_COLORS.len(), 64);
}

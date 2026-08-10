//! Waveshare 7.5″ V2 panel geometry (matches the inkbot Worker).

pub const PANEL_WIDTH: u32 = 800;
pub const PANEL_HEIGHT: u32 = 480;
pub const FRAME_BYTES: usize = (PANEL_WIDTH as usize / 8) * PANEL_HEIGHT as usize;

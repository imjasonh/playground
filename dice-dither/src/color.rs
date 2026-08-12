//! Moving between gamma-encoded sRGB and linear light.

/// Decode one sRGB channel (0-1) to linear light.
pub fn srgb_to_linear(c: f32) -> f32 {
    if c <= 0.04045 {
        c / 12.92
    } else {
        ((c + 0.055) / 1.055).powf(2.4)
    }
}

/// Encode one linear-light value (0-1) as sRGB.
pub fn linear_to_srgb(c: f32) -> f32 {
    let c = c.clamp(0.0, 1.0);
    if c <= 0.003_130_8 {
        c * 12.92
    } else {
        1.055 * c.powf(1.0 / 2.4) - 0.055
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_two_conversions_undo_each_other() {
        for step in 0..=255 {
            let c = step as f32 / 255.0;
            assert!((linear_to_srgb(srgb_to_linear(c)) - c).abs() < 1e-4);
        }
    }

    #[test]
    fn mid_srgb_is_about_a_fifth_of_the_light() {
        assert!((srgb_to_linear(0.5) - 0.2140).abs() < 1e-3);
        assert_eq!(srgb_to_linear(0.0), 0.0);
        assert!((srgb_to_linear(1.0) - 1.0).abs() < 1e-6);
    }
}

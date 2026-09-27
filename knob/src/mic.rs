//! PDM microphone window to bar heights.
//!
//! The device reads 16 kHz mono i16 from the PDM mic. `bands` runs a
//! Goertzel filter at each center frequency and maps the magnitude to 0-255.

pub const MIC_RATE: u32 = 16_000;
pub const BANDS: usize = 16;

pub fn bands(samples: &[i16], count: usize) -> Vec<u8> {
    if count == 0 || samples.is_empty() {
        return vec![0; count];
    }
    let mut out = Vec::with_capacity(count);
    for i in 0..count {
        // 250 Hz, 500 Hz, ... so a 1 kHz tone lands on band 3.
        let freq = 250 * (i as u32 + 1);
        let mag = goertzel(samples, MIC_RATE, freq);
        let scaled = (mag / 40.0).clamp(0.0, 255.0) as u8;
        out.push(scaled);
    }
    out
}

fn goertzel(samples: &[i16], rate: u32, freq: u32) -> f32 {
    let n = samples.len() as f32;
    let k = (n * freq as f32 / rate as f32).round();
    let w = 2.0 * std::f32::consts::PI * k / n;
    let coeff = 2.0 * w.cos();
    let mut s0;
    let mut s1 = 0.0;
    let mut s2 = 0.0;
    for sample in samples {
        s0 = f32::from(*sample) + coeff * s1 - s2;
        s2 = s1;
        s1 = s0;
    }
    let power = s1 * s1 + s2 * s2 - coeff * s1 * s2;
    power.sqrt() / n
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_1khz_tone_peaks_near_1khz() {
        let n = 512;
        let mut samples = vec![0i16; n];
        for (i, s) in samples.iter_mut().enumerate() {
            let t = i as f32 / MIC_RATE as f32;
            *s = ((t * 1000.0 * std::f32::consts::TAU).sin() * 8000.0) as i16;
        }
        let got = bands(&samples, BANDS);
        let peak = got.iter().enumerate().max_by_key(|(_, v)| *v).unwrap().0;
        assert_eq!(peak, 3, "peak bin {peak} values {got:?}");
    }
}

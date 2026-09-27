//! PCM helpers for the PCM5100A jack.
//!
//! The panel has no built-in speaker. These samples go out the 3.5 mm jack.
//! Stereo frames are interleaved little-endian i16, left then right.

pub const SAMPLE_RATE: u32 = 44_100;

#[derive(Clone, Debug)]
pub struct Tone {
    phase: f32,
    pub hz: f32,
    pub volume: f32,
}

impl Tone {
    pub fn new(hz: f32) -> Self {
        Self {
            phase: 0.0,
            hz,
            volume: 0.2,
        }
    }

    /// Fill `out` with interleaved stereo samples. `out.len()` must be even.
    pub fn fill(&mut self, out: &mut [i16]) {
        let step = self.hz / SAMPLE_RATE as f32;
        let amp = (self.volume.clamp(0.0, 1.0) * i16::MAX as f32) as i16;
        for frame in out.chunks_exact_mut(2) {
            let s = (self.phase * std::f32::consts::TAU).sin();
            let sample = (s * amp as f32) as i16;
            frame[0] = sample;
            frame[1] = sample;
            self.phase = (self.phase + step).fract();
        }
    }
}

/// Scale a stereo buffer in place. `volume` is 0 to 256, where 256 is unity.
pub fn apply_volume(samples: &mut [i16], volume: u16) {
    let v = u32::from(volume.min(256));
    for s in samples {
        *s = ((*s as i32) * v as i32 / 256) as i16;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sine_crosses_zero_and_is_stereo() {
        let mut tone = Tone::new(440.0);
        let mut buf = [0i16; 200];
        tone.fill(&mut buf);
        assert!(buf.iter().any(|s| *s > 1000));
        assert!(buf.iter().any(|s| *s < -1000));
        assert_eq!(buf[0], buf[1]);
    }

    #[test]
    fn volume_zero_silences() {
        let mut buf = [1000i16, -1000];
        apply_volume(&mut buf, 0);
        assert_eq!(buf, [0, 0]);
    }
}

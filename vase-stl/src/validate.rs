use crate::envelope::{max_layer_step, Contour, Envelope};

/// Result of checking whether an envelope is safe for spiral/vase printing.
#[derive(Debug, Clone, Copy)]
pub struct VaseValidation {
    /// Hard limit used for consecutive |Δr| (usually ≈ line width).
    pub max_step_mm: f32,
    /// Worst consecutive |Δr| found (mm).
    pub worst_step_mm: f32,
    /// Fraction of consecutive (θ, layer) pairs exceeding `max_step_mm`.
    pub frac_over_budget: f32,
    /// Number of band layers.
    pub layers: usize,
    /// Angular samples.
    pub angular_samples: usize,
    /// True when `worst_step_mm ≤ max_step_mm + epsilon`.
    pub ok: bool,
}

/// Validate band-to-band radial steps against a printable line-width budget.
pub fn validate_envelope(envelope: &Envelope, max_step_mm: f32) -> VaseValidation {
    let layers = envelope.contours.len();
    let angular_samples = envelope
        .contours
        .first()
        .map(Contour::sample_count)
        .unwrap_or(0);
    let worst = max_layer_step(&envelope.contours);
    let mut over = 0usize;
    let mut total = 0usize;
    if layers >= 2 && angular_samples > 0 {
        for w in envelope.contours.windows(2) {
            for j in 0..angular_samples {
                total += 1;
                if (w[1].radii[j] - w[0].radii[j]).abs() > max_step_mm + 1e-5 {
                    over += 1;
                }
            }
        }
    }
    let frac = if total == 0 {
        0.0
    } else {
        over as f32 / total as f32
    };
    VaseValidation {
        max_step_mm,
        worst_step_mm: worst,
        frac_over_budget: frac,
        layers,
        angular_samples,
        ok: worst <= max_step_mm + 1e-4 && frac == 0.0,
    }
}

use std::path::PathBuf;
use std::process::ExitCode;

use clap::{Parser, ValueEnum};

use vase_stl::{
    convert, optimize_convert, read_stl, write_3mf, write_stl, ConvertOptions, ShellMode, UpAxis,
};

/// Convert an STL into a vase-mode-printable solid (radial envelope loft).
#[derive(Debug, Parser)]
#[command(name = "vase-stl", version, about)]
struct Cli {
    /// Input STL (binary or ASCII).
    input: PathBuf,

    /// Output path (`.stl` or `.3mf`).
    #[arg(short = 'o', long)]
    output: PathBuf,

    /// Slice / loft layer height in mm (one band thick).
    #[arg(long, default_value_t = 0.15)]
    layer_height: f32,

    /// Angular samples around the print axis.
    #[arg(long, default_value_t = 360)]
    samples: usize,

    /// Minimum radius at every angle (mm).
    #[arg(long, default_value_t = 0.4)]
    min_radius: f32,

    /// Extra radius added everywhere (mm).
    #[arg(long, default_value_t = 0.0)]
    inflate: f32,

    /// Angular smoothing half-width in samples (0 disables).
    #[arg(long, default_value_t = 0)]
    smooth_angular: usize,

    /// Legacy neighbor-blend along Z, 0..1.
    #[arg(long, default_value_t = 0.0)]
    smooth_vertical: f32,

    /// Legacy Gaussian σ along Z in mm (`0` = off). Prefer --couple-weight.
    #[arg(long, default_value_t = 0.0)]
    smooth_vertical_mm: f32,

    /// Legacy bilateral range σ on radius in mm.
    #[arg(long, default_value_t = 0.0)]
    smooth_vertical_range_mm: f32,

    /// Z samples inside each layer band (max radius kept).
    #[arg(long, default_value_t = 5)]
    band_subsamples: usize,

    /// Curvature spring weight (`0`–`1`) — kills stair-steps on round ridges.
    #[arg(long, default_value_t = 0.25)]
    couple_weight: f32,

    /// Max |Δr| between bands (mm); capped at --line-width. Use 0 for auto.
    #[arg(long, default_value_t = 0.35)]
    couple_gap_mm: f32,

    /// Extrusion line width (mm). Hard bonding budget for consecutive walls.
    #[arg(long, default_value_t = 0.42)]
    line_width: f32,

    /// Catmull-Rom subdivisions per band for a smoother STL loft.
    #[arg(long, default_value_t = 3)]
    loft_subdivide: usize,

    /// Force the input axis that becomes print-up. Default: longest AABB edge.
    #[arg(long, value_enum)]
    up: Option<UpAxisArg>,

    /// Output shell style.
    #[arg(long, value_enum, default_value_t = ShellArg::Solid)]
    shell: ShellArg,

    /// Wall thickness in mm when `--shell hollow`.
    #[arg(long, default_value_t = 0.8)]
    wall: f32,

    /// Uniform scale after orientation (ignored when `--height` is set).
    #[arg(long, default_value_t = 1.0)]
    scale: f32,

    /// Scale so the oriented model height becomes this many millimeters.
    #[arg(long)]
    height: Option<f32>,

    /// Exaggerate silhouette relief vs a low-pass baseline (1 = faithful).
    #[arg(long, default_value_t = 1.0)]
    detail_gain: f32,

    /// Sweep couple-weight vs bonding-safe bands; write the best-scoring vase.
    #[arg(long, default_value_t = false)]
    optimize: bool,

    /// Soft choppiness budget (mean |Δr| between layers, mm) for --optimize.
    #[arg(long, default_value_t = 0.12)]
    chop_budget: f32,
}

#[derive(Debug, Clone, Copy, ValueEnum)]
enum UpAxisArg {
    X,
    Y,
    Z,
}

impl From<UpAxisArg> for UpAxis {
    fn from(v: UpAxisArg) -> Self {
        match v {
            UpAxisArg::X => UpAxis::X,
            UpAxisArg::Y => UpAxis::Y,
            UpAxisArg::Z => UpAxis::Z,
        }
    }
}

#[derive(Debug, Clone, Copy, ValueEnum, Default)]
enum ShellArg {
    #[default]
    Solid,
    OpenTop,
    Hollow,
}

fn main() -> ExitCode {
    let cli = Cli::parse();
    if let Err(err) = run(cli) {
        eprintln!("error: {err}");
        return ExitCode::FAILURE;
    }
    ExitCode::SUCCESS
}

fn run(cli: Cli) -> Result<(), String> {
    if cli.layer_height <= 0.0 {
        return Err("--layer-height must be > 0".into());
    }
    if cli.samples < 8 {
        return Err("--samples must be >= 8".into());
    }
    if cli.scale <= 0.0 {
        return Err("--scale must be > 0".into());
    }
    if cli.line_width <= 0.0 {
        return Err("--line-width must be > 0".into());
    }
    if let Some(h) = cli.height {
        if h <= 0.0 {
            return Err("--height must be > 0".into());
        }
    }

    let input = read_stl(&cli.input).map_err(|e| format!("read {}: {e}", cli.input.display()))?;
    eprintln!(
        "read {} ({} triangles)",
        cli.input.display(),
        input.triangle_count()
    );

    let shell = match cli.shell {
        ShellArg::Solid => ShellMode::Solid,
        ShellArg::OpenTop => ShellMode::OpenTop,
        ShellArg::Hollow => ShellMode::hollow(cli.wall),
    };

    let opts = ConvertOptions {
        layer_height: cli.layer_height,
        angular_samples: cli.samples,
        min_radius: cli.min_radius,
        inflate: cli.inflate,
        smooth_angular: cli.smooth_angular,
        smooth_vertical: cli.smooth_vertical,
        smooth_vertical_mm: cli.smooth_vertical_mm,
        smooth_vertical_range_mm: cli.smooth_vertical_range_mm,
        band_subsamples: cli.band_subsamples,
        couple_weight: cli.couple_weight,
        couple_gap_mm: cli.couple_gap_mm,
        line_width_mm: cli.line_width,
        loft_subdivide: cli.loft_subdivide,
        up_axis: cli.up.map(UpAxis::from),
        shell,
        scale: cli.scale,
        target_height_mm: cli.height,
        detail_gain: cli.detail_gain,
    };

    let result = if cli.optimize {
        let (best, trials) = optimize_convert(&input, &opts, cli.chop_budget)?;
        eprintln!(
            "optimize: {} bonding-safe trials  chop_budget={:.3} mm",
            trials.len(),
            cli.chop_budget
        );
        eprintln!("rank,score,mean_abs_r,max_abs_r,d2r,chop,couple_w,gap");
        for (i, t) in trials.iter().take(20).enumerate() {
            let m = &t.metrics;
            eprintln!(
                "{},{:.4},{:.4},{:.4},{:.4},{:.4},{:.2},{:.3}",
                i + 1,
                t.score,
                m.mean_abs_r_err,
                m.max_abs_r_err,
                m.mean_abs_d2r,
                m.mean_abs_dr_dz,
                t.options.couple_weight,
                t.options.couple_gap_mm
            );
        }
        best
    } else {
        convert(&input, &opts)?
    };

    let v = &result.validation;
    eprintln!(
        "vase-check: {}  worst|Δr|={:.3} mm  budget={:.3} mm  over={:.2}%  layers={} samples={}",
        if v.ok { "PASS" } else { "FAIL" },
        v.worst_step_mm,
        v.max_step_mm,
        100.0 * v.frac_over_budget,
        v.layers,
        v.angular_samples
    );

    let out = cli.output;
    let ext = out
        .extension()
        .and_then(|e| e.to_str())
        .unwrap_or("")
        .to_ascii_lowercase();
    if ext == "3mf" {
        write_3mf(&out, &result.mesh, "vase")
            .map_err(|e| format!("write {}: {e}", out.display()))?;
    } else {
        write_stl(&out, &result.mesh).map_err(|e| format!("write {}: {e}", out.display()))?;
    }

    let before = result.bbox_before.size();
    let after = result.bbox_after.size();
    eprintln!(
        "up-axis={}  layers={}  samples={}  tris={}",
        result.up_axis.as_str(),
        result.stats.layers,
        result.stats.angular_samples,
        result.stats.triangles
    );
    eprintln!(
        "input size  {:.2} × {:.2} × {:.2} mm",
        before[0], before[1], before[2]
    );
    eprintln!(
        "output size {:.2} × {:.2} × {:.2} mm  z_min={:.3} → {}",
        after[0],
        after[1],
        after[2],
        result.bbox_after.min[2],
        out.display()
    );
    Ok(())
}

use std::path::PathBuf;
use std::process::ExitCode;

use clap::{Parser, ValueEnum};

use vase_stl::{convert, read_stl, write_stl, ConvertOptions, ShellMode, UpAxis};

/// Convert an STL into a vase-mode-printable solid (radial envelope loft).
#[derive(Debug, Parser)]
#[command(name = "vase-stl", version, about)]
struct Cli {
    /// Input STL (binary or ASCII).
    input: PathBuf,

    /// Output STL path.
    #[arg(short = 'o', long)]
    output: PathBuf,

    /// Slice / loft layer height in mm.
    #[arg(long, default_value_t = 0.2)]
    layer_height: f32,

    /// Angular samples around the print axis.
    #[arg(long, default_value_t = 96)]
    samples: usize,

    /// Minimum radius at every angle (mm).
    #[arg(long, default_value_t = 0.4)]
    min_radius: f32,

    /// Extra radius added everywhere (mm).
    #[arg(long, default_value_t = 0.0)]
    inflate: f32,

    /// Angular smoothing half-width in samples (0 disables).
    #[arg(long, default_value_t = 1)]
    smooth_angular: usize,

    /// Vertical smoothing blend 0..1.
    #[arg(long, default_value_t = 0.25)]
    smooth_vertical: f32,

    /// Force the input axis that becomes print-up. Default: longest AABB edge.
    #[arg(long, value_enum)]
    up: Option<UpAxisArg>,

    /// Output shell style.
    #[arg(long, value_enum, default_value_t = ShellArg::Solid)]
    shell: ShellArg,

    /// Wall thickness in mm when `--shell hollow`.
    #[arg(long, default_value_t = 0.8)]
    wall: f32,
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
        up_axis: cli.up.map(UpAxis::from),
        shell,
    };

    let result = convert(&input, &opts)?;
    write_stl(&cli.output, &result.mesh)
        .map_err(|e| format!("write {}: {e}", cli.output.display()))?;

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
        "output size {:.2} × {:.2} × {:.2} mm → {}",
        after[0],
        after[1],
        after[2],
        cli.output.display()
    );
    Ok(())
}

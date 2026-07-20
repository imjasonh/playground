use std::path::PathBuf;
use std::process::ExitCode;

use clap::Parser;
use rand::Rng;

use life_stl::config::{Config, Pattern, SupportMode};
use life_stl::{format_report, generate_stl};

/// Generate a 3D-printable STL of Conway's Game of Life (Z = time).
///
/// Dimensions can be given in cells (`-x/-y/-z`) or in millimeters
/// (`--width-mm/--height-mm/--depth-mm`) together with `--cell`.
#[derive(Debug, Parser)]
#[command(name = "life-stl", version, about)]
struct Cli {
    /// Grid width (X), in cells. Ignored when `--width-mm` is set.
    #[arg(short = 'x', long, default_value_t = 24)]
    width: usize,

    /// Grid height (Y), in cells. Ignored when `--height-mm` is set.
    #[arg(short = 'y', long, default_value_t = 24)]
    height: usize,

    /// Number of generations stacked on Z (above the base plate).
    /// Ignored when `--depth-mm` is set.
    #[arg(short = 'z', long, default_value_t = 48)]
    depth: usize,

    /// Physical width in millimeters (overrides `-x`). Rounded to a whole
    /// number of `--cell` voxels.
    #[arg(long)]
    width_mm: Option<f32>,

    /// Physical height (Y) in millimeters (overrides `-y`).
    #[arg(long)]
    height_mm: Option<f32>,

    /// Physical total height in millimeters including the base plate
    /// (overrides `-z`). Rounded to a whole number of `--cell` voxels.
    #[arg(long)]
    depth_mm: Option<f32>,

    /// RNG seed for random patterns. Omit to pick one and print it.
    #[arg(short = 's', long)]
    seed: Option<u64>,

    /// Initial fill density for `--pattern random` (0..1).
    #[arg(long, default_value_t = 0.35)]
    density: f64,

    /// Starting pattern.
    #[arg(long, value_enum, default_value_t = Pattern::Random)]
    pattern: Pattern,

    /// Edge length of each voxel in millimeters.
    #[arg(long, default_value_t = 2.0)]
    cell: f32,

    /// Solid base-plate thickness in cell layers.
    #[arg(long, default_value_t = 1)]
    base_layers: usize,

    /// Support strategy.
    #[arg(long, value_enum, default_value_t = SupportMode::Scaffold)]
    mode: SupportMode,

    /// Output STL path.
    #[arg(short = 'o', long, default_value = "life.stl")]
    output: PathBuf,

    /// Print printability metrics to stdout.
    #[arg(long, default_value_t = true)]
    report: bool,

    /// Suppress the metrics report.
    #[arg(long, default_value_t = false)]
    quiet: bool,
}

fn resolve_grid(cli: &Cli) -> Result<(usize, usize, usize), String> {
    let width = match cli.width_mm {
        Some(mm) => Config::cells_from_mm(mm, cli.cell)?,
        None => cli.width,
    };
    let height = match cli.height_mm {
        Some(mm) => Config::cells_from_mm(mm, cli.cell)?,
        None => cli.height,
    };
    let depth = match cli.depth_mm {
        Some(mm) => {
            let total_z = Config::cells_from_mm(mm, cli.cell)?;
            if total_z <= cli.base_layers {
                return Err(format!(
                    "--depth-mm {mm} with --cell {} and --base-layers {} leaves no room for Life generations",
                    cli.cell, cli.base_layers
                ));
            }
            total_z - cli.base_layers
        }
        None => cli.depth,
    };
    if width == 0 || height == 0 || depth == 0 {
        return Err("width, height, and depth must be > 0".into());
    }
    Ok((width, height, depth))
}

fn main() -> ExitCode {
    let cli = Cli::parse();

    if !(0.0..=1.0).contains(&cli.density) {
        eprintln!("error: density must be between 0 and 1");
        return ExitCode::FAILURE;
    }
    if cli.cell <= 0.0 {
        eprintln!("error: --cell must be > 0");
        return ExitCode::FAILURE;
    }

    let (width, height, depth) = match resolve_grid(&cli) {
        Ok(g) => g,
        Err(err) => {
            eprintln!("error: {err}");
            return ExitCode::FAILURE;
        }
    };

    let seed = match cli.seed {
        Some(s) => s,
        None if cli.pattern == Pattern::Random => {
            let s = rand::thread_rng().gen::<u64>();
            eprintln!("using random seed: {s}");
            s
        }
        None => 0,
    };

    let config = Config {
        width,
        height,
        depth,
        seed,
        density: cli.density,
        pattern: cli.pattern,
        cell_mm: cli.cell,
        base_layers: cli.base_layers,
        mode: cli.mode,
    };

    match generate_stl(&config, &cli.output) {
        Ok(report) => {
            if cli.report && !cli.quiet {
                print!("{}", format_report(&config, &report));
            }
            eprintln!("wrote {}", cli.output.display());
            ExitCode::SUCCESS
        }
        Err(err) => {
            eprintln!("error writing {}: {err}", cli.output.display());
            ExitCode::FAILURE
        }
    }
}

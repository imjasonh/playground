use std::path::PathBuf;
use std::process::ExitCode;

use clap::Parser;
use rand::Rng;

use life_stl::config::{Config, Pattern, SupportMode};
use life_stl::{format_report, generate_stl};

/// Generate a 3D-printable STL of Conway's Game of Life (Z = time).
#[derive(Debug, Parser)]
#[command(name = "life-stl", version, about)]
struct Cli {
    /// Grid width (X), in cells.
    #[arg(short = 'x', long, default_value_t = 24)]
    width: usize,

    /// Grid height (Y), in cells.
    #[arg(short = 'y', long, default_value_t = 24)]
    height: usize,

    /// Number of generations stacked on Z.
    #[arg(short = 'z', long, default_value_t = 48)]
    depth: usize,

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

fn main() -> ExitCode {
    let cli = Cli::parse();

    if cli.width == 0 || cli.height == 0 || cli.depth == 0 {
        eprintln!("error: width, height, and depth must be > 0");
        return ExitCode::FAILURE;
    }
    if !(0.0..=1.0).contains(&cli.density) {
        eprintln!("error: density must be between 0 and 1");
        return ExitCode::FAILURE;
    }
    if cli.cell <= 0.0 {
        eprintln!("error: --cell must be > 0");
        return ExitCode::FAILURE;
    }

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
        width: cli.width,
        height: cli.height,
        depth: cli.depth,
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

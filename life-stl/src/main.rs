use std::path::PathBuf;
use std::process::ExitCode;

use clap::Parser;
use rand::Rng;

use life_stl::config::{
    Config, Pattern, SupportMode, SupportParams, SupportStyle, DEFAULT_CELL_MM, MIN_CELL_MM,
};
use life_stl::search::{evaluate_life_only, find_self_supporting};
use life_stl::{format_report, format_unprintable_reason, write_stl_model};

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

    /// Physical width in millimeters (overrides `-x`).
    #[arg(long)]
    width_mm: Option<f32>,

    /// Physical height (Y) in millimeters (overrides `-y`).
    #[arg(long)]
    height_mm: Option<f32>,

    /// Physical total height in millimeters including the base plate.
    #[arg(long)]
    depth_mm: Option<f32>,

    /// RNG seed for random patterns. When omitted, seeds are tried until the
    /// Life geometry is one piece after support removal.
    #[arg(short = 's', long)]
    seed: Option<u64>,

    /// How many seeds to try when `--seed` is omitted.
    #[arg(long, default_value_t = 200)]
    max_seed_attempts: u32,

    /// Fill density for `--pattern random` (still-life coverage) or `soup`.
    #[arg(long, default_value_t = 0.25)]
    density: f64,

    /// Starting pattern.
    #[arg(long, value_enum, default_value_t = Pattern::Random)]
    pattern: Pattern,

    /// Edge length of each voxel in millimeters (min 2.0; default 4.0).
    #[arg(long, default_value_t = DEFAULT_CELL_MM)]
    cell: f32,

    /// Solid base-plate thickness in cell layers.
    #[arg(long, default_value_t = 1)]
    base_layers: usize,

    /// Support strategy: breakaway (default) or raw (no supports).
    #[arg(long, value_enum, default_value_t = SupportMode::Breakaway)]
    mode: SupportMode,

    /// Breakaway support style (`pillar` or `tree`).
    #[arg(long, value_enum, default_value_t = SupportStyle::Tree)]
    support_style: SupportStyle,

    /// Breakaway shaft / branch radius (mm).
    #[arg(long, default_value_t = SupportParams::default().radius_mm)]
    support_radius: f32,

    /// Breakaway tip radius at the model contact (mm) — smaller snaps easier.
    #[arg(long, default_value_t = SupportParams::default().tip_radius_mm)]
    support_tip_radius: f32,

    /// Tip taper length (mm).
    #[arg(long, default_value_t = SupportParams::default().tip_height_mm)]
    support_tip_height: f32,

    /// Tree trunk radius (mm).
    #[arg(long, default_value_t = SupportParams::default().trunk_radius_mm)]
    support_trunk_radius: f32,

    /// Cluster tips within this XY distance (mm) onto one tree trunk.
    #[arg(long, default_value_t = SupportParams::default().cluster_mm)]
    support_cluster: f32,

    /// Offset tip contact from cell center toward +X/+Y (mm) for easier snap.
    #[arg(long, default_value_t = SupportParams::default().tip_offset_mm)]
    support_tip_offset: f32,

    /// Cylinder tessellation segments.
    #[arg(long, default_value_t = SupportParams::default().segments)]
    support_segments: u32,

    /// XY clearance from Life cells (mm). Supports route around obstacles
    /// instead of punching through. `0` uses radius + 0.4 mm.
    #[arg(long, default_value_t = SupportParams::default().clearance_mm)]
    support_clearance: f32,

    /// Max branch lean from vertical (degrees) while dodging Life cells.
    #[arg(long, default_value_t = SupportParams::default().max_branch_angle_deg)]
    support_branch_angle: f32,

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
    if cli.cell < MIN_CELL_MM {
        eprintln!(
            "error: --cell {} mm is below the minimum {} mm \
             (~5× a 0.4 mm nozzle; Bambu A1 Mini stock is 0.4 mm, not 0.04 mm)",
            cli.cell, MIN_CELL_MM
        );
        return ExitCode::FAILURE;
    }
    if cli.support_radius <= 0.0 || cli.support_tip_radius <= 0.0 || cli.support_trunk_radius <= 0.0
    {
        eprintln!("error: support radii must be > 0");
        return ExitCode::FAILURE;
    }
    if cli.support_segments < 3 {
        eprintln!("error: --support-segments must be >= 3");
        return ExitCode::FAILURE;
    }

    let (width, height, depth) = match resolve_grid(&cli) {
        Ok(g) => g,
        Err(err) => {
            eprintln!("error: {err}");
            return ExitCode::FAILURE;
        }
    };

    let seed_was_explicit = cli.seed.is_some();
    let searchable = matches!(cli.pattern, Pattern::Random | Pattern::Soup);
    let start_seed = match cli.seed {
        Some(s) => s,
        None if searchable => {
            let s = rand::thread_rng().gen::<u64>();
            eprintln!(
                "searching for a self-supporting seed (start={s}, max {})…",
                cli.max_seed_attempts
            );
            s
        }
        None => 0,
    };

    if cli.support_clearance < 0.0 {
        eprintln!("error: --support-clearance must be >= 0");
        return ExitCode::FAILURE;
    }
    if !(5.0..=60.0).contains(&cli.support_branch_angle) {
        eprintln!("error: --support-branch-angle must be between 5 and 60 degrees");
        return ExitCode::FAILURE;
    }

    let support = SupportParams {
        style: cli.support_style,
        radius_mm: cli.support_radius,
        tip_radius_mm: cli.support_tip_radius,
        tip_height_mm: cli.support_tip_height,
        trunk_radius_mm: cli.support_trunk_radius,
        cluster_mm: cli.support_cluster,
        tip_offset_mm: cli.support_tip_offset,
        segments: cli.support_segments,
        clearance_mm: cli.support_clearance,
        max_branch_angle_deg: cli.support_branch_angle,
    };

    let base_config = Config {
        width,
        height,
        depth,
        seed: start_seed,
        density: cli.density,
        pattern: cli.pattern,
        cell_mm: cli.cell,
        base_layers: cli.base_layers,
        mode: cli.mode,
        support,
    };

    let outcome = if seed_was_explicit || !searchable {
        let config = base_config;
        let life_report = evaluate_life_only(&config);
        let model = life_stl::search::evaluate(&config);
        life_stl::search::SearchOutcome {
            life_self_supporting: life_report.life_self_supporting(),
            report: model.report.clone(),
            config,
            model,
            attempts: 1,
        }
    } else {
        find_self_supporting(base_config, cli.max_seed_attempts, start_seed)
    };

    if cli.report && !cli.quiet {
        print!("{}", format_report(&outcome.config, &outcome.report));
        if outcome.attempts > 1 {
            println!("seed search attempts: {}", outcome.attempts);
        }
    }

    match write_stl_model(&outcome.model, &cli.output) {
        Ok(()) => eprintln!("wrote {}", cli.output.display()),
        Err(err) => {
            eprintln!("error writing {}: {err}", cli.output.display());
            return ExitCode::FAILURE;
        }
    }

    if outcome.life_self_supporting {
        if !cli.quiet {
            eprintln!(
                "ok: Life is one piece after support removal ({} breakaway tip(s))",
                outcome.model.support_tips
            );
        }
        ExitCode::SUCCESS
    } else if seed_was_explicit || !searchable {
        let life_report = evaluate_life_only(&outcome.config);
        eprintln!(
            "error: {}",
            format_unprintable_reason(&outcome.config, &life_report)
        );
        ExitCode::FAILURE
    } else {
        eprintln!(
            "error: no self-supporting seed in {} attempt(s) starting at {}. {}",
            outcome.attempts,
            start_seed,
            format_unprintable_reason(&outcome.config, &evaluate_life_only(&outcome.config))
        );
        eprintln!(
            "wrote best-effort STL anyway; try --pattern random (still-life garden), \
             lower --density, or a larger --max-seed-attempts"
        );
        ExitCode::FAILURE
    }
}

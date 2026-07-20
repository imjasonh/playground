use std::path::PathBuf;
use std::process::ExitCode;

use clap::{Parser, Subcommand};
use rand::Rng;

use life_stl::config::{
    ComplexityParams, Config, Pattern, PhysicsParams, RemovalParams, SupportMode, SupportParams,
    SupportStyle, DEFAULT_CELL_MM, MIN_CELL_MM,
};
use life_stl::search::{evaluate_life_only, find_self_supporting};
use life_stl::{
    format_boring_reason, format_hard_removal_reason, format_report, format_unprintable_reason,
    write_stl_model,
};

/// Generate a 3D-printable STL of Conway's Game of Life (Z = time).
///
/// Dimensions can be given in cells (`-x/-y/-z`) or in millimeters
/// (`--width-mm/--height-mm/--depth-mm`) together with `--cell`.
#[derive(Debug, Parser)]
#[command(name = "life-stl", version, about)]
struct Cli {
    #[command(subcommand)]
    command: Option<Command>,

    #[command(flatten)]
    generate: GenerateArgs,
}

#[derive(Debug, Subcommand)]
enum Command {
    /// Simulate Life and write an STL (default when no subcommand is given).
    Generate(GenerateArgs),
    /// Package an STL as a Bambu Studio project .3mf with print settings.
    #[command(name = "bambu-3mf")]
    Bambu3mf(BambuArgs),
}

/// Package an STL as a Bambu Studio project .3mf.
///
/// Settings default to the embedded A1 Mini 0.4 nozzle + 0.20mm Standard +
/// Generic PLA presets with the gusset-print overrides from
/// docs/printing-a1mini.md. Point `--profiles` at a Bambu Studio
/// `resources/profiles/BBL` directory to use other presets.
#[derive(Debug, clap::Args)]
struct BambuArgs {
    /// Input binary STL.
    #[arg(long)]
    stl: PathBuf,

    /// Output .3mf path.
    #[arg(short = 'o', long)]
    output: PathBuf,

    /// Bambu Studio resources/profiles/BBL directory (default: embedded
    /// A1 Mini + Generic PLA presets).
    #[arg(long)]
    profiles: Option<PathBuf>,

    /// Printer preset name (with --profiles).
    #[arg(long, default_value = "Bambu Lab A1 mini 0.4 nozzle")]
    printer: String,

    /// Process preset name (with --profiles).
    #[arg(long, default_value = "0.20mm Standard @BBL A1M")]
    process: String,

    /// Filament preset name (with --profiles).
    #[arg(long, default_value = "Generic PLA @BBL A1M")]
    filament: String,

    /// Process-level override KEY=VALUE (repeatable; replaces the default
    /// gusset-print overrides when given).
    #[arg(long = "override", value_name = "KEY=VALUE")]
    overrides: Vec<String>,

    /// Plate type recorded in the project.
    #[arg(long, default_value = "Textured PEI Plate")]
    bed_type: String,

    /// Bed edge length (mm); the model is centered on it.
    #[arg(long, default_value_t = 180.0)]
    bed_size: f32,

    /// Object name shown in the slicer (default: STL file stem).
    #[arg(long)]
    name: Option<String>,
}

#[derive(Debug, clap::Args)]
struct GenerateArgs {
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
    /// model passes the interestingness and printability gates.
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

    /// Base plate covers the whole board instead of shrink-wrapping to the
    /// model footprint (always on in breakaway mode).
    #[arg(long, default_value_t = false)]
    full_base: bool,

    /// Margin (cells) around the model footprint for the shrink-wrapped base.
    #[arg(long, default_value_t = 2)]
    base_margin: usize,

    /// Support strategy: gusset (default; self-supporting causality braces),
    /// breakaway (removable trees/pillars), or raw (no supports).
    #[arg(long, value_enum, default_value_t = SupportMode::Gusset)]
    mode: SupportMode,

    /// Breakaway support style (`pillar` or `tree`).
    #[arg(long, value_enum, default_value_t = SupportStyle::Tree)]
    support_style: SupportStyle,

    /// Breakaway shaft / branch radius (mm).
    #[arg(long, default_value_t = SupportParams::default().radius_mm)]
    support_radius: f32,

    /// Tip radius at model contact (mm). Smaller snaps easier; `0` = needle point.
    #[arg(long, default_value_t = SupportParams::default().tip_radius_mm)]
    support_tip_radius: f32,

    /// Tip taper length (mm) — longer cone = cleaner breakaway.
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

    /// Auto-size / split trunks from the structural model (default on).
    #[arg(long, default_value_t = PhysicsParams::default().auto_size)]
    support_auto_size: bool,

    /// Disable structural auto-sizing (use fixed shaft/trunk radii only).
    #[arg(long, default_value_t = false)]
    no_support_auto_size: bool,

    /// Filament density (g/cm³) for support load estimates. PLA ≈ 1.24.
    #[arg(long, default_value_t = PhysicsParams::default().filament_density_g_cm3)]
    filament_density: f32,

    /// Working allowable stress (MPa) for support shafts.
    #[arg(long, default_value_t = PhysicsParams::default().allow_stress_mpa)]
    allow_stress_mpa: f32,

    /// Young's modulus (MPa) for buckling checks. PLA ≈ 3000.
    #[arg(long, default_value_t = PhysicsParams::default().youngs_modulus_mpa)]
    youngs_modulus_mpa: f32,

    /// Safety factor on dead weight for print dynamics.
    #[arg(long, default_value_t = PhysicsParams::default().safety_factor)]
    support_safety_factor: f32,

    /// Max tips merged onto one trunk before splitting.
    #[arg(long, default_value_t = PhysicsParams::default().max_tips_per_trunk)]
    support_max_tips_per_trunk: u32,

    /// Minimum auto-sized shaft radius (mm).
    #[arg(long, default_value_t = PhysicsParams::default().min_shaft_radius_mm)]
    support_min_shaft_radius: f32,

    /// Maximum auto-sized trunk radius (mm).
    #[arg(long, default_value_t = PhysicsParams::default().max_trunk_radius_mm)]
    support_max_trunk_radius: f32,

    /// Minimum support-removability score (0–100) to accept.
    #[arg(long, default_value_t = RemovalParams::default().min_score)]
    min_removal_score: f32,

    /// Allow unlimited supports that rest on the model.
    #[arg(long, default_value_t = false)]
    allow_rest_on_model: bool,

    /// Max rest-on-model landings before the cleanup gate fails
    /// (double-tapered contacts make a few practical to snap off).
    #[arg(long, default_value_t = RemovalParams::default().max_rest_on_model)]
    max_rest_on_model: usize,

    /// Gusset strut width (mm) for `--mode gusset`.
    #[arg(long, default_value_t = SupportParams::default().gusset_width_mm)]
    gusset_width: f32,

    /// Max fraction of tip contacts allowed in enclosed pockets (0–1).
    #[arg(long, default_value_t = RemovalParams::default().max_inaccessible_tip_fraction)]
    max_inaccessible_tip_fraction: f32,

    /// Max tip contacts per XY cell before density is considered too high.
    #[arg(long, default_value_t = RemovalParams::default().max_tip_density)]
    max_tip_density: f32,

    /// Skip the support-removability gate (still reports the score).
    #[arg(long, default_value_t = false)]
    allow_hard_supports: bool,

    /// Minimum generations before a still life / short oscillator is allowed.
    #[arg(long, default_value_t = ComplexityParams::default().min_active_generations)]
    min_active_generations: usize,

    /// Also require activity for at least this fraction of `--depth` (0–1).
    #[arg(long, default_value_t = ComplexityParams::default().min_active_fraction)]
    min_active_fraction: f32,

    /// Periods ≤ this count as boring once settled (1 = still life, 2 = blinker).
    #[arg(long, default_value_t = ComplexityParams::default().max_boring_period)]
    max_boring_period: usize,

    /// Skip the evolution interestingness gate (still reports quiescence).
    #[arg(long, default_value_t = false)]
    allow_boring: bool,

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

fn resolve_grid(cli: &GenerateArgs) -> Result<(usize, usize, usize), String> {
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
    match cli.command {
        Some(Command::Bambu3mf(args)) => run_bambu(&args),
        Some(Command::Generate(args)) => run_generate(&args),
        None => run_generate(&cli.generate),
    }
}

fn run_bambu(args: &BambuArgs) -> ExitCode {
    let presets = match &args.profiles {
        None => life_stl::bambu::BambuPresets::embedded_a1mini_pla(),
        Some(dir) => {
            match life_stl::bambu::BambuPresets::from_profiles_dir(
                dir,
                &args.printer,
                &args.process,
                &args.filament,
            ) {
                Ok(p) => p,
                Err(err) => {
                    eprintln!("error: {err}");
                    return ExitCode::FAILURE;
                }
            }
        }
    };

    let mut overrides = life_stl::bambu::gusset_print_overrides();
    if !args.overrides.is_empty() {
        overrides.clear();
        for item in &args.overrides {
            let Some((key, value)) = item.split_once('=') else {
                eprintln!("error: --override needs KEY=VALUE, got {item:?}");
                return ExitCode::FAILURE;
            };
            overrides.insert(key.to_string(), value.to_string());
        }
    }

    let stl_bytes = match std::fs::read(&args.stl) {
        Ok(b) => b,
        Err(err) => {
            eprintln!("error reading {}: {err}", args.stl.display());
            return ExitCode::FAILURE;
        }
    };
    let triangles = match life_stl::bambu::read_binary_stl(&stl_bytes) {
        Ok(t) => t,
        Err(err) => {
            eprintln!("error: {err}");
            return ExitCode::FAILURE;
        }
    };

    let object_name = args.name.clone().unwrap_or_else(|| {
        args.stl
            .file_stem()
            .map(|s| s.to_string_lossy().into_owned())
            .unwrap_or_else(|| "life-stl".into())
    });
    let opts = life_stl::bambu::ExportOptions {
        overrides,
        bed_type: args.bed_type.clone(),
        bed_size_mm: args.bed_size,
        object_name,
    };

    match life_stl::bambu::project_3mf_bytes(&triangles, &presets, &opts) {
        Ok(bytes) => match std::fs::write(&args.output, &bytes) {
            Ok(()) => {
                eprintln!(
                    "wrote {} ({} triangles, {:.1} KB)",
                    args.output.display(),
                    triangles.len(),
                    bytes.len() as f64 / 1024.0
                );
                ExitCode::SUCCESS
            }
            Err(err) => {
                eprintln!("error writing {}: {err}", args.output.display());
                ExitCode::FAILURE
            }
        },
        Err(err) => {
            eprintln!("error: {err}");
            ExitCode::FAILURE
        }
    }
}

fn run_generate(cli: &GenerateArgs) -> ExitCode {
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
    if cli.support_radius <= 0.0 || cli.support_trunk_radius <= 0.0 {
        eprintln!("error: --support-radius and --support-trunk-radius must be > 0");
        return ExitCode::FAILURE;
    }
    if cli.support_tip_radius < 0.0 {
        eprintln!("error: --support-tip-radius must be >= 0 (0 = needle point)");
        return ExitCode::FAILURE;
    }
    if cli.support_segments < 3 {
        eprintln!("error: --support-segments must be >= 3");
        return ExitCode::FAILURE;
    }
    if cli.filament_density <= 0.0
        || cli.allow_stress_mpa <= 0.0
        || cli.youngs_modulus_mpa <= 0.0
        || cli.support_safety_factor < 1.0
    {
        eprintln!(
            "error: filament/physics params invalid \
             (density, allow-stress, youngs > 0; safety-factor >= 1)"
        );
        return ExitCode::FAILURE;
    }
    if cli.support_max_tips_per_trunk == 0 {
        eprintln!("error: --support-max-tips-per-trunk must be >= 1");
        return ExitCode::FAILURE;
    }
    if cli.support_min_shaft_radius <= 0.0
        || cli.support_max_trunk_radius < cli.support_min_shaft_radius
    {
        eprintln!("error: shaft radius bounds invalid");
        return ExitCode::FAILURE;
    }
    if !(0.0..=100.0).contains(&cli.min_removal_score) {
        eprintln!("error: --min-removal-score must be between 0 and 100");
        return ExitCode::FAILURE;
    }
    if !(0.0..=1.0).contains(&cli.max_inaccessible_tip_fraction) {
        eprintln!("error: --max-inaccessible-tip-fraction must be between 0 and 1");
        return ExitCode::FAILURE;
    }
    if cli.max_tip_density <= 0.0 {
        eprintln!("error: --max-tip-density must be > 0");
        return ExitCode::FAILURE;
    }
    if cli.gusset_width <= 0.0 {
        eprintln!("error: --gusset-width must be > 0");
        return ExitCode::FAILURE;
    }
    if !(0.0..=1.0).contains(&cli.min_active_fraction) {
        eprintln!("error: --min-active-fraction must be between 0 and 1");
        return ExitCode::FAILURE;
    }
    if cli.max_boring_period == 0 {
        eprintln!("error: --max-boring-period must be >= 1");
        return ExitCode::FAILURE;
    }

    let (width, height, depth) = match resolve_grid(cli) {
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
                "searching for an interesting, printable seed (start={s}, max {})…",
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

    let auto_size = if cli.no_support_auto_size {
        false
    } else {
        cli.support_auto_size
    };
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
        physics: PhysicsParams {
            filament_density_g_cm3: cli.filament_density,
            allow_stress_mpa: cli.allow_stress_mpa,
            youngs_modulus_mpa: cli.youngs_modulus_mpa,
            safety_factor: cli.support_safety_factor,
            auto_size,
            max_tips_per_trunk: cli.support_max_tips_per_trunk,
            min_shaft_radius_mm: cli.support_min_shaft_radius,
            max_trunk_radius_mm: cli.support_max_trunk_radius,
        },
        removal: if cli.allow_hard_supports {
            RemovalParams {
                min_score: 0.0,
                allow_rest_on_model: true,
                max_rest_on_model: usize::MAX,
                max_inaccessible_tip_fraction: 1.0,
                max_tip_density: f32::MAX,
            }
        } else {
            RemovalParams {
                min_score: cli.min_removal_score,
                allow_rest_on_model: cli.allow_rest_on_model,
                max_rest_on_model: cli.max_rest_on_model,
                max_inaccessible_tip_fraction: cli.max_inaccessible_tip_fraction,
                max_tip_density: cli.max_tip_density,
            }
        },
        gusset_width_mm: cli.gusset_width,
    };

    let complexity = if cli.allow_boring {
        ComplexityParams {
            min_active_generations: 0,
            min_active_fraction: 0.0,
            max_boring_period: cli.max_boring_period,
        }
    } else {
        ComplexityParams {
            min_active_generations: cli.min_active_generations,
            min_active_fraction: cli.min_active_fraction,
            max_boring_period: cli.max_boring_period,
        }
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
        // Breakaway supports may land on the bed anywhere → full plate.
        full_base: cli.full_base || cli.mode == SupportMode::Breakaway,
        base_margin: cli.base_margin,
        mode: cli.mode,
        support,
        complexity,
    };

    let outcome = if seed_was_explicit || !searchable {
        let config = base_config;
        let model = life_stl::search::evaluate(&config);
        let removable = model.support_removability.ok || cli.allow_hard_supports;
        let interesting = model.complexity.ok || cli.allow_boring;
        // Gusset reports causal connectivity; other modes face-only.
        life_stl::search::SearchOutcome {
            life_self_supporting: model.report.life_self_supporting(),
            supports_removable: removable,
            interesting,
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

    // Gate 1: evolution stays interesting (soups / named patterns; gardens exempt).
    if !outcome.interesting {
        eprintln!(
            "error: {}",
            format_boring_reason(&outcome.config, &outcome.report)
        );
        if !seed_was_explicit && searchable {
            eprintln!(
                "no sufficiently interesting seed in {} attempt(s); \
                 wrote best-effort STL — try higher --density, larger \
                 --max-seed-attempts, lower --min-active-generations, or --allow-boring",
                outcome.attempts
            );
        }
        return ExitCode::FAILURE;
    }

    // Gate 2: practical support cleanup (breakaway only).
    if cli.mode == SupportMode::Breakaway && !outcome.supports_removable {
        eprintln!(
            "error: {}",
            format_hard_removal_reason(&outcome.config, &outcome.report)
        );
        if !seed_was_explicit && searchable {
            eprintln!(
                "no seed with easy-to-remove supports in {} attempt(s); \
                 wrote best-effort STL — try lower --density, larger \
                 --max-seed-attempts, or relax --min-removal-score",
                outcome.attempts
            );
        }
        return ExitCode::FAILURE;
    }

    // Gate 3: Life is one standing piece (after supports snap off, or through
    // causality braces in gusset mode).
    if outcome.life_self_supporting {
        if !cli.quiet {
            if cli.mode == SupportMode::Gusset {
                eprintln!(
                    "ok: interesting + one self-supporting piece ({} causality brace(s), no supports)",
                    outcome.model.gusset_braces
                );
            } else {
                eprintln!(
                    "ok: interesting + Life is one piece after support removal ({} breakaway tip(s))",
                    outcome.model.support_tips
                );
            }
        }
        return ExitCode::SUCCESS;
    }

    // Breakaway soup search (no explicit seed): interesting + removable
    // supports succeed even when Life orphans remain (multi-piece after cleanup).
    if !seed_was_explicit
        && searchable
        && cli.pattern == Pattern::Soup
        && cli.mode == SupportMode::Breakaway
        && outcome.supports_removable
        && outcome.interesting
    {
        if !cli.quiet {
            eprintln!(
                "ok: interesting (quiescent≥{}) + removable supports (score {:.0}); \
                 Life has orphans (multi-piece after cleanup) — {} tip(s)",
                outcome.model.complexity.required_active_generations,
                outcome.model.support_removability.score,
                outcome.model.support_tips
            );
        }
        return ExitCode::SUCCESS;
    }

    if seed_was_explicit || !searchable {
        eprintln!(
            "error: {}",
            format_unprintable_reason(&outcome.config, &outcome.report)
        );
        ExitCode::FAILURE
    } else {
        eprintln!(
            "error: no acceptable seed in {} attempt(s) starting at {}. {}",
            outcome.attempts,
            start_seed,
            format_unprintable_reason(&outcome.config, &evaluate_life_only(&outcome.config))
        );
        eprintln!(
            "wrote best-effort STL anyway; try lower --density or a larger --max-seed-attempts"
        );
        ExitCode::FAILURE
    }
}

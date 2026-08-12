//! Command line front end: read a picture, write a picture made of dice.

use std::path::PathBuf;
use std::process::ExitCode;

use clap::{Parser, ValueEnum};
use dice_dither::{dice_dither, Dither, Normalize, Options, Palette, TileStyle, ToneSpace};

#[derive(Parser, Debug)]
#[command(
    name = "dice-dither",
    about = "Dither an image into a grid of dice faces",
    version
)]
struct Args {
    /// Image to convert (PNG, JPEG, WebP or BMP).
    input: PathBuf,

    /// Where to write the mosaic; defaults to <input>-dice.png next to it.
    #[arg(short, long)]
    output: Option<PathBuf>,

    /// Dice across the picture.
    #[arg(long, default_value_t = 72)]
    cells: u32,

    /// Dice down the picture; defaults to whatever keeps the aspect ratio.
    #[arg(long)]
    rows: Option<u32>,

    /// Pixels per die in the output.
    #[arg(long, default_value_t = 24)]
    cell_px: u32,

    /// Which dice to build from.
    #[arg(long, value_enum, default_value_t = PaletteArg::Both)]
    palette: PaletteArg,

    /// How the quantisation error is spread.
    #[arg(long, value_enum, default_value_t = DitherArg::Floyd)]
    dither: DitherArg,

    /// Scan every row left to right instead of alternating.
    #[arg(long)]
    no_serpentine: bool,

    /// Also use blank faces (zero pips) as a tone. Not a real die.
    #[arg(long)]
    allow_blank: bool,

    /// Brightness exponent applied before matching; above 1 darkens.
    #[arg(long, default_value_t = 1.0)]
    gamma: f32,

    /// Invert the picture (light becomes dark).
    #[arg(long)]
    invert: bool,

    /// Stretch the source tones to the range the dice can show.
    #[arg(long, value_enum, default_value_t = NormalizeArg::Auto)]
    normalize: NormalizeArg,

    /// Brightness scale to match tones on: `display` looks right on a screen,
    /// `linear` is physically correct for a mosaic you actually build.
    #[arg(long, value_enum, default_value_t = ToneSpaceArg::Display)]
    tone_space: ToneSpaceArg,

    /// Lay every die square instead of turning it randomly.
    #[arg(long)]
    no_rotate: bool,

    /// Seed for the random quarter turns.
    #[arg(long, default_value_t = 0x5EED_D1CE)]
    seed: u64,

    /// Seam between dice, as a fraction of a cell.
    #[arg(long, default_value_t = 0.07)]
    gap: f32,

    /// Grey shown in the seam between dice, 0 (black) to 1 (white).
    #[arg(long, default_value_t = 0.06)]
    seam: f32,

    /// Corner radius of a die, as a fraction of a cell.
    #[arg(long, default_value_t = 0.18)]
    corner: f32,

    /// Pip radius, as a fraction of a cell.
    #[arg(long, default_value_t = 0.088)]
    pip_radius: f32,

    /// Distance from a die's centre to its outer pip rows, as a fraction of a
    /// cell.
    #[arg(long, default_value_t = 0.24)]
    pip_spread: f32,

    /// Also write a plain-text build sheet listing the die in every cell.
    #[arg(long)]
    sheet: Option<PathBuf>,

    /// Print how many dice of each kind the mosaic needs.
    #[arg(long)]
    inventory: bool,
}

#[derive(Copy, Clone, Debug, ValueEnum)]
enum PaletteArg {
    /// White dice with black pips.
    Light,
    /// Black dice with white pips.
    Dark,
    /// Both, the way a real dice mosaic is built.
    Both,
}

#[derive(Copy, Clone, Debug, ValueEnum)]
enum DitherArg {
    None,
    Floyd,
    Atkinson,
    Jarvis,
    SierraLite,
    Bayer,
}

#[derive(Copy, Clone, Debug, ValueEnum)]
enum NormalizeArg {
    Auto,
    On,
    Off,
}

#[derive(Copy, Clone, Debug, ValueEnum)]
enum ToneSpaceArg {
    /// Gamma-encoded brightness: matches how the picture looks on a screen.
    Display,
    /// Physical light: matches how a real tray of dice looks.
    Linear,
}

fn main() -> ExitCode {
    let args = Args::parse();
    match run(args) {
        Ok(()) => ExitCode::SUCCESS,
        Err(err) => {
            eprintln!("dice-dither: {err}");
            ExitCode::FAILURE
        }
    }
}

fn run(args: Args) -> Result<(), String> {
    let source =
        image::open(&args.input).map_err(|e| format!("reading {}: {e}", args.input.display()))?;

    let options = Options {
        cells: args.cells,
        rows: args.rows,
        palette: match args.palette {
            PaletteArg::Light => Palette::Light,
            PaletteArg::Dark => Palette::Dark,
            PaletteArg::Both => Palette::Both,
        },
        dither: match args.dither {
            DitherArg::None => Dither::None,
            DitherArg::Floyd => Dither::Floyd,
            DitherArg::Atkinson => Dither::Atkinson,
            DitherArg::Jarvis => Dither::Jarvis,
            DitherArg::SierraLite => Dither::SierraLite,
            DitherArg::Bayer => Dither::Bayer,
        },
        serpentine: !args.no_serpentine,
        allow_blank: args.allow_blank,
        gamma: args.gamma,
        invert: args.invert,
        normalize: match args.normalize {
            NormalizeArg::Auto => Normalize::Auto,
            NormalizeArg::On => Normalize::On,
            NormalizeArg::Off => Normalize::Off,
        },
        rotate: !args.no_rotate,
        seed: args.seed,
        tone_space: match args.tone_space {
            ToneSpaceArg::Display => ToneSpace::Display,
            ToneSpaceArg::Linear => ToneSpace::Linear,
        },
        style: TileStyle {
            cell_px: args.cell_px,
            gap: args.gap,
            corner: args.corner,
            pip_radius: args.pip_radius,
            pip_spread: args.pip_spread,
            seam_gray: args.seam,
        },
    };

    let mosaic = dice_dither(&source, &options);
    let output = args.output.unwrap_or_else(|| default_output(&args.input));
    mosaic
        .image
        .save(&output)
        .map_err(|e| format!("writing {}: {e}", output.display()))?;

    println!(
        "{} -> {} ({} x {} dice, {} x {} px)",
        args.input.display(),
        output.display(),
        mosaic.cols,
        mosaic.rows,
        mosaic.image.width(),
        mosaic.image.height()
    );

    if let Some(path) = &args.sheet {
        std::fs::write(path, mosaic.build_sheet())
            .map_err(|e| format!("writing {}: {e}", path.display()))?;
        println!("build sheet -> {}", path.display());
    }

    if args.inventory {
        let counts = mosaic.inventory();
        for (index, name) in [(0usize, "black"), (1usize, "white")] {
            let total: usize = counts[index].iter().sum();
            if total == 0 {
                continue;
            }
            let breakdown: Vec<String> = (0..=6)
                .filter(|&pips| counts[index][pips] > 0)
                .map(|pips| format!("{pips}:{}", counts[index][pips]))
                .collect();
            println!("{name} dice: {total} ({})", breakdown.join(" "));
        }
    }
    Ok(())
}

fn default_output(input: &std::path::Path) -> PathBuf {
    let stem = input
        .file_stem()
        .map(|s| s.to_string_lossy().to_string())
        .unwrap_or_else(|| "image".to_string());
    input.with_file_name(format!("{stem}-dice.png"))
}

#[cfg(test)]
mod tests {
    use super::*;
    use clap::CommandFactory;

    #[test]
    fn cli_is_well_formed() {
        Args::command().debug_assert();
    }

    #[test]
    fn output_defaults_next_to_the_input() {
        let path = default_output(std::path::Path::new("/tmp/pics/cat.jpg"));
        assert_eq!(path, PathBuf::from("/tmp/pics/cat-dice.png"));
    }
}

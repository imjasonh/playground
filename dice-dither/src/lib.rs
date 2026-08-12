//! Turn a photograph into a picture built from dice.
//!
//! The picture is divided into a grid of cells, each cell is measured for
//! brightness, and each cell is replaced by the die face whose own brightness
//! comes closest — with the leftover error diffused into neighbouring cells so
//! the mosaic averages out to the original tones. Because a die's brightness
//! comes from how many pips it shows, the result reads as a photo from a
//! distance and as a tray of dice up close.
//!
//! Tones are handled in linear light: sRGB input is decoded before it is
//! averaged or compared, and encoded again on the way out.

pub mod color;
pub mod dither;
pub mod face;
pub mod tile;

use image::{DynamicImage, GenericImageView, GrayImage, Luma};

pub use color::{linear_to_srgb, srgb_to_linear};
pub use dither::Dither;
pub use face::{DieFace, DieStyle, MAX_PIPS};
pub use tile::{TileRenderer, TileStyle, ToneSpace};

/// Which dice are in the box.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Palette {
    /// White dice with black pips only. Six tones, all bright: the pip count
    /// carries the picture, like a newspaper halftone.
    Light,
    /// Black dice with white pips only.
    Dark,
    /// Both colours, the way a real dice mosaic is built. Spans the full
    /// range, and midtones come out as a mix of black and white dice.
    Both,
}

impl Palette {
    fn styles(self) -> &'static [DieStyle] {
        match self {
            Palette::Light => &[DieStyle::Light],
            Palette::Dark => &[DieStyle::Dark],
            Palette::Both => &[DieStyle::Dark, DieStyle::Light],
        }
    }
}

/// Whether the source tones are stretched to fill what the dice can show.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Normalize {
    /// Stretch for single-colour palettes (whose range is narrow), leave the
    /// tones alone for a two-colour palette (which spans black to white).
    Auto,
    On,
    Off,
}

/// Everything the conversion needs to know.
#[derive(Clone, Debug)]
pub struct Options {
    /// Dice across the picture.
    pub cells: u32,
    /// Dice down the picture; `None` keeps the source aspect ratio.
    pub rows: Option<u32>,
    pub palette: Palette,
    pub dither: Dither,
    /// Alternate the scan direction on each row, which hides directional
    /// artefacts from error diffusion.
    pub serpentine: bool,
    /// Allow blank faces (zero pips). Not a real die, but an extra tone.
    pub allow_blank: bool,
    /// Exponent applied to brightness before matching; above 1 darkens.
    pub gamma: f32,
    pub invert: bool,
    pub normalize: Normalize,
    /// Turn each die a random quarter turn, as a hand-laid mosaic would be.
    pub rotate: bool,
    pub seed: u64,
    /// Brightness scale the source and the dice are compared on.
    pub tone_space: ToneSpace,
    pub style: TileStyle,
}

impl Default for Options {
    fn default() -> Self {
        Options {
            cells: 64,
            rows: None,
            palette: Palette::Both,
            dither: Dither::Floyd,
            serpentine: true,
            allow_blank: false,
            gamma: 1.0,
            invert: false,
            normalize: Normalize::Auto,
            rotate: true,
            seed: 0x5EED_D1CE,
            tone_space: ToneSpace::Display,
            style: TileStyle::default(),
        }
    }
}

/// The finished mosaic: which die went where, plus the rendered picture.
pub struct Mosaic {
    pub cols: usize,
    pub rows: usize,
    /// Row-major, one die per cell.
    pub faces: Vec<DieFace>,
    pub image: GrayImage,
}

impl Mosaic {
    pub fn dice(&self) -> usize {
        self.faces.len()
    }

    /// How many dice of each colour and pip count the mosaic uses, indexed as
    /// `[style][pips]` with `style` 0 = black dice, 1 = white dice.
    pub fn inventory(&self) -> [[usize; 7]; 2] {
        let mut counts = [[0usize; 7]; 2];
        for face in &self.faces {
            let style = usize::from(face.style == DieStyle::Light);
            counts[style][face.pips as usize] += 1;
        }
        counts
    }

    /// A plain-text plan for laying the mosaic out by hand: one token per die,
    /// `W3` for a white die showing three pips, `B5` for a black one.
    pub fn build_sheet(&self) -> String {
        let counts = self.inventory();
        let mut out = String::new();
        out.push_str(&format!(
            "# dice-dither build sheet: {} x {} = {} dice\n",
            self.cols,
            self.rows,
            self.dice()
        ));
        for (style, tag) in [(0usize, 'B'), (1usize, 'W')] {
            let total: usize = counts[style].iter().sum();
            if total == 0 {
                continue;
            }
            let breakdown: Vec<String> = (0..=6)
                .filter(|&p| counts[style][p] > 0)
                .map(|p| format!("{p}:{}", counts[style][p]))
                .collect();
            out.push_str(&format!(
                "# {tag} dice: {total} ({})\n",
                breakdown.join(" ")
            ));
        }
        for row in 0..self.rows {
            let line: Vec<String> = (0..self.cols)
                .map(|col| {
                    let face = self.faces[row * self.cols + col];
                    format!("{}{}", face.style.tag(), face.pips)
                })
                .collect();
            out.push_str(&line.join(" "));
            out.push('\n');
        }
        out
    }
}

/// Convert an image into a dice mosaic.
pub fn dice_dither(source: &DynamicImage, options: &Options) -> Mosaic {
    let cols = options.cells.max(1) as usize;
    let (width, height) = source.dimensions();
    let rows = match options.rows {
        Some(r) => r.max(1) as usize,
        None => {
            let aspect = height as f64 / width.max(1) as f64;
            ((cols as f64 * aspect).round() as usize).max(1)
        }
    };

    let mut grid = sample_luminance(source, cols, rows, options.tone_space);
    for value in grid.iter_mut() {
        if options.invert {
            *value = 1.0 - *value;
        }
        if (options.gamma - 1.0).abs() > f32::EPSILON {
            *value = value.max(0.0).powf(options.gamma);
        }
    }

    let mut renderer = TileRenderer::new(options.style);
    let palette = build_palette(&mut renderer, options);
    let levels: Vec<f32> = palette.iter().map(|entry| entry.gray).collect();

    if normalizing(options) {
        let (lo, hi) = (levels[0], levels[levels.len() - 1]);
        for value in grid.iter_mut() {
            *value = lo + value.clamp(0.0, 1.0) * (hi - lo);
        }
    }

    let choices = dither::quantize(
        &grid,
        cols,
        rows,
        &levels,
        options.dither,
        options.serpentine,
    );

    let mut rng = Rng::new(options.seed);
    let faces: Vec<DieFace> = choices
        .iter()
        .map(|&level| {
            let face = palette[level].face;
            if options.rotate {
                face.rotated(rng.next_u32() as u8)
            } else {
                face
            }
        })
        .collect();

    let image = render(&faces, cols, rows, &mut renderer);
    Mosaic {
        cols,
        rows,
        faces,
        image,
    }
}

struct PaletteEntry {
    face: DieFace,
    gray: f32,
}

/// Every face the chosen dice can show, sorted from darkest to brightest.
fn build_palette(renderer: &mut TileRenderer, options: &Options) -> Vec<PaletteEntry> {
    let lowest = if options.allow_blank { 0 } else { 1 };
    let mut palette: Vec<PaletteEntry> = options
        .palette
        .styles()
        .iter()
        .flat_map(|&style| (lowest..=MAX_PIPS).map(move |pips| DieFace::new(style, pips)))
        .map(|face| PaletteEntry {
            gray: renderer.mean_gray(face, options.tone_space),
            face,
        })
        .collect();
    palette.sort_by(|a, b| a.gray.partial_cmp(&b.gray).unwrap());
    palette
}

fn normalizing(options: &Options) -> bool {
    match options.normalize {
        Normalize::On => true,
        Normalize::Off => false,
        Normalize::Auto => options.palette != Palette::Both,
    }
}

/// Average luminance of the source under each grid cell, on `space`'s scale.
fn sample_luminance(source: &DynamicImage, cols: usize, rows: usize, space: ToneSpace) -> Vec<f32> {
    let rgb = source.to_rgb8();
    let (width, height) = rgb.dimensions();
    let mut grid = vec![0.0f32; cols * rows];
    if width == 0 || height == 0 {
        return grid;
    }

    for (row, cell) in grid.chunks_mut(cols).enumerate() {
        let y0 = (row * height as usize / rows).min(height as usize - 1);
        let y1 = (((row + 1) * height as usize).div_ceil(rows)).clamp(y0 + 1, height as usize);
        for (col, out) in cell.iter_mut().enumerate() {
            let x0 = (col * width as usize / cols).min(width as usize - 1);
            let x1 = (((col + 1) * width as usize).div_ceil(cols)).clamp(x0 + 1, width as usize);
            let mut sum = 0.0f64;
            for y in y0..y1 {
                for x in x0..x1 {
                    let p = rgb.get_pixel(x as u32, y as u32).0;
                    sum += f64::from(luminance(p, space));
                }
            }
            *out = (sum / ((x1 - x0) * (y1 - y0)) as f64) as f32;
        }
    }
    grid
}

/// Rec. 709 luminance of an sRGB pixel, on `space`'s scale.
fn luminance(rgb: [u8; 3], space: ToneSpace) -> f32 {
    let [r, g, b] = rgb.map(|c| {
        let c = f32::from(c) / 255.0;
        match space {
            ToneSpace::Linear => srgb_to_linear(c),
            ToneSpace::Display => c,
        }
    });
    0.2126 * r + 0.7152 * g + 0.0722 * b
}

fn render(faces: &[DieFace], cols: usize, rows: usize, renderer: &mut TileRenderer) -> GrayImage {
    let cell = renderer.style().cell_px.max(3);
    let mut image = GrayImage::new(cols as u32 * cell, rows as u32 * cell);
    for (index, &face) in faces.iter().enumerate() {
        let (col, row) = (index % cols, index / cols);
        let tile = renderer.tile(face);
        for y in 0..cell {
            for x in 0..cell {
                let value = tile.pixels[(y * cell + x) as usize];
                let byte = (linear_to_srgb(value) * 255.0).round().clamp(0.0, 255.0) as u8;
                image.put_pixel(col as u32 * cell + x, row as u32 * cell + y, Luma([byte]));
            }
        }
    }
    image
}

/// Tiny deterministic PRNG (SplitMix64) so a given seed always lays the dice
/// down the same way.
struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self {
        Rng(seed.wrapping_add(0x9E37_79B9_7F4A_7C15))
    }

    fn next_u32(&mut self) -> u32 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        ((z ^ (z >> 31)) >> 32) as u32
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use image::{Rgb, RgbImage};

    fn flat(gray: u8, width: u32, height: u32) -> DynamicImage {
        DynamicImage::ImageRgb8(RgbImage::from_pixel(width, height, Rgb([gray, gray, gray])))
    }

    fn gradient(width: u32, height: u32) -> DynamicImage {
        let mut img = RgbImage::new(width, height);
        for (x, _, pixel) in img.enumerate_pixels_mut() {
            let v = (x * 255 / (width - 1)) as u8;
            *pixel = Rgb([v, v, v]);
        }
        DynamicImage::ImageRgb8(img)
    }

    /// Mean tone of a rendered mosaic, measured on `space`'s scale.
    fn mean_tone(image: &GrayImage, space: ToneSpace) -> f32 {
        let sum: f64 = image
            .pixels()
            .map(|p| {
                let v = f32::from(p.0[0]) / 255.0;
                f64::from(match space {
                    ToneSpace::Linear => srgb_to_linear(v),
                    ToneSpace::Display => v,
                })
            })
            .sum();
        (sum / image.pixels().len() as f64) as f32
    }

    fn source_tone(gray: u8, space: ToneSpace) -> f32 {
        let v = f32::from(gray) / 255.0;
        match space {
            ToneSpace::Linear => srgb_to_linear(v),
            ToneSpace::Display => v,
        }
    }

    #[test]
    fn output_is_a_whole_number_of_dice() {
        let options = Options {
            cells: 20,
            style: TileStyle {
                cell_px: 12,
                ..TileStyle::default()
            },
            ..Options::default()
        };
        let mosaic = dice_dither(&flat(128, 400, 200), &options);
        assert_eq!(mosaic.cols, 20);
        assert_eq!(mosaic.rows, 10, "aspect ratio should be preserved");
        assert_eq!(mosaic.image.dimensions(), (240, 120));
        assert_eq!(mosaic.dice(), 200);
    }

    #[test]
    fn explicit_rows_override_the_aspect_ratio() {
        let options = Options {
            cells: 8,
            rows: Some(3),
            ..Options::default()
        };
        let mosaic = dice_dither(&gradient(64, 64), &options);
        assert_eq!((mosaic.cols, mosaic.rows), (8, 3));
    }

    #[test]
    fn real_dice_only_unless_blanks_are_allowed() {
        let base = Options {
            cells: 24,
            ..Options::default()
        };
        let mosaic = dice_dither(&gradient(200, 200), &base);
        assert!(mosaic.faces.iter().all(|f| (1..=6).contains(&f.pips)));

        let with_blanks = dice_dither(
            &gradient(200, 200),
            &Options {
                allow_blank: true,
                ..base
            },
        );
        assert!(with_blanks.faces.iter().any(|f| f.pips == 0));
    }

    #[test]
    fn a_flat_grey_comes_back_out_as_the_same_grey() {
        // Anything inside the range dice can show is reproduced on average by
        // mixing faces, even the midtones no single face can hit — and it is
        // reproduced on whichever scale was used to match it.
        for space in [ToneSpace::Display, ToneSpace::Linear] {
            for gray in [70u8, 130, 190] {
                let options = Options {
                    cells: 40,
                    tone_space: space,
                    style: TileStyle {
                        cell_px: 10,
                        ..TileStyle::default()
                    },
                    ..Options::default()
                };
                let mosaic = dice_dither(&flat(gray, 400, 400), &options);
                let want = source_tone(gray, space);
                let got = mean_tone(&mosaic.image, space);
                assert!(
                    (got - want).abs() < 0.03,
                    "{space:?} grey {gray}: {got} vs {want}"
                );
            }
        }
    }

    #[test]
    fn tones_beyond_what_dice_can_show_saturate_instead_of_smearing() {
        let options = Options {
            cells: 24,
            ..Options::default()
        };
        let darkest = dice_dither(&flat(0, 240, 240), &options);
        assert!(darkest
            .faces
            .iter()
            .all(|f| f.style == DieStyle::Dark && f.pips == 1));

        let brightest = dice_dither(&flat(255, 240, 240), &options);
        assert!(brightest
            .faces
            .iter()
            .all(|f| f.style == DieStyle::Light && f.pips == 1));
    }

    #[test]
    fn a_gradient_stays_a_gradient() {
        let options = Options {
            cells: 48,
            ..Options::default()
        };
        let mosaic = dice_dither(&gradient(480, 480), &options);
        let column_mean = |c: usize| {
            (0..mosaic.rows)
                .map(|r| face_gray(mosaic.faces[r * mosaic.cols + c]))
                .sum::<f32>()
                / mosaic.rows as f32
        };
        let (left, middle, right) = (column_mean(1), column_mean(24), column_mean(46));
        assert!(left < middle && middle < right, "{left} {middle} {right}");
    }

    #[test]
    fn inverting_flips_the_picture() {
        let options = Options {
            cells: 32,
            invert: true,
            ..Options::default()
        };
        let mosaic = dice_dither(&gradient(320, 320), &options);
        let left = face_gray(mosaic.faces[0]);
        let right = face_gray(mosaic.faces[mosaic.cols - 1]);
        assert!(left > right, "inverted gradient: {left} then {right}");
    }

    #[test]
    fn single_colour_palettes_use_only_that_colour_and_still_span_the_range() {
        for (palette, style) in [
            (Palette::Light, DieStyle::Light),
            (Palette::Dark, DieStyle::Dark),
        ] {
            let mosaic = dice_dither(
                &gradient(320, 320),
                &Options {
                    cells: 32,
                    palette,
                    ..Options::default()
                },
            );
            assert!(mosaic.faces.iter().all(|f| f.style == style));
            // Auto-normalising stretched the gradient across all six faces.
            for pips in 1..=MAX_PIPS {
                assert!(
                    mosaic.faces.iter().any(|f| f.pips == pips),
                    "{palette:?} never used a {pips}"
                );
            }
        }
    }

    #[test]
    fn a_two_colour_midtone_mixes_black_and_white_dice() {
        // No single die is this bright or this dark, so the only way to hit
        // the tone is to interleave black and white ones.
        let mosaic = dice_dither(
            &flat(160, 400, 400),
            &Options {
                cells: 40,
                ..Options::default()
            },
        );
        assert!(mosaic.faces.iter().any(|f| f.style == DieStyle::Light));
        assert!(mosaic.faces.iter().any(|f| f.style == DieStyle::Dark));
    }

    #[test]
    fn gamma_darkens() {
        let brighter = dice_dither(
            &flat(160, 200, 200),
            &Options {
                cells: 20,
                gamma: 0.5,
                ..Options::default()
            },
        );
        let darker = dice_dither(
            &flat(160, 200, 200),
            &Options {
                cells: 20,
                gamma: 2.0,
                ..Options::default()
            },
        );
        assert!(
            mean_tone(&darker.image, ToneSpace::Display)
                < mean_tone(&brighter.image, ToneSpace::Display)
        );
    }

    #[test]
    fn rotation_is_deterministic_and_optional() {
        let options = Options {
            cells: 16,
            ..Options::default()
        };
        let a = dice_dither(&gradient(160, 160), &options);
        let b = dice_dither(&gradient(160, 160), &options);
        assert_eq!(a.faces, b.faces);
        assert!(a.faces.iter().any(|f| f.quarter_turns != 0));

        let straight = dice_dither(
            &gradient(160, 160),
            &Options {
                rotate: false,
                ..options.clone()
            },
        );
        assert!(straight.faces.iter().all(|f| f.quarter_turns == 0));
        let different_seed = dice_dither(
            &gradient(160, 160),
            &Options {
                seed: 7,
                ..options.clone()
            },
        );
        assert_ne!(a.faces, different_seed.faces);
        // Only the orientation changed, never which die was chosen.
        for (x, y) in a.faces.iter().zip(different_seed.faces.iter()) {
            assert_eq!((x.style, x.pips), (y.style, y.pips));
        }
    }

    #[test]
    fn build_sheet_lists_every_die() {
        let mosaic = dice_dither(
            &gradient(120, 120),
            &Options {
                cells: 12,
                ..Options::default()
            },
        );
        let sheet = mosaic.build_sheet();
        let rows: Vec<&str> = sheet.lines().filter(|l| !l.starts_with('#')).collect();
        assert_eq!(rows.len(), mosaic.rows);
        for row in &rows {
            assert_eq!(row.split_whitespace().count(), mosaic.cols);
        }
        assert!(sheet.contains("12 x 12 = 144 dice"));

        let counted: usize = mosaic.inventory().iter().flatten().sum();
        assert_eq!(counted, mosaic.dice());
    }

    #[test]
    fn one_cell_pictures_do_not_panic() {
        let mosaic = dice_dither(
            &flat(200, 3, 3),
            &Options {
                cells: 1,
                ..Options::default()
            },
        );
        assert_eq!(mosaic.dice(), 1);
    }

    #[test]
    fn an_empty_source_does_not_panic() {
        let mosaic = dice_dither(
            &DynamicImage::ImageRgb8(RgbImage::new(0, 0)),
            &Options {
                cells: 4,
                rows: Some(4),
                ..Options::default()
            },
        );
        assert_eq!(mosaic.dice(), 16);
    }

    #[test]
    fn more_cells_than_pixels_is_fine() {
        let mosaic = dice_dither(
            &gradient(4, 4),
            &Options {
                cells: 32,
                ..Options::default()
            },
        );
        assert_eq!(mosaic.dice(), 32 * 32);
    }

    fn face_gray(face: DieFace) -> f32 {
        TileRenderer::new(TileStyle::default()).mean_gray(face, ToneSpace::Display)
    }
}

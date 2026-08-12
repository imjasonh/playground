//! End-to-end checks: does the rendered picture actually look like the source,
//! and does it actually look like dice?

use dice_dither::{dice_dither, srgb_to_linear, Dither, Options, Palette, TileStyle, ToneSpace};
use image::{DynamicImage, GenericImageView, GrayImage, Rgb, RgbImage};

/// A photo-ish test image: a bright disc on a dark ground, with a soft edge.
///
/// Its tones stay inside what dice can show (no pure black, no paper white) so
/// that tone comparisons measure the dithering rather than clipping.
fn disc(size: u32) -> DynamicImage {
    let (floor, ceiling) = (70.0f32, 230.0f32);
    let mut img = RgbImage::new(size, size);
    let center = size as f32 / 2.0;
    for (x, y, pixel) in img.enumerate_pixels_mut() {
        let d = ((x as f32 - center).powi(2) + (y as f32 - center).powi(2)).sqrt();
        let t = (1.0 - (d / (size as f32 * 0.42))).clamp(0.0, 1.0);
        let v = (floor + t * (ceiling - floor)) as u8;
        *pixel = Rgb([v, v, v]);
    }
    DynamicImage::ImageRgb8(img)
}

fn tone(value: f32, space: ToneSpace) -> f32 {
    match space {
        ToneSpace::Linear => srgb_to_linear(value),
        ToneSpace::Display => value,
    }
}

fn mean_output_tone(image: &GrayImage, space: ToneSpace) -> f32 {
    let sum: f64 = image
        .pixels()
        .map(|p| f64::from(tone(f32::from(p.0[0]) / 255.0, space)))
        .sum();
    (sum / image.pixels().len() as f64) as f32
}

fn mean_source_tone(image: &DynamicImage, space: ToneSpace) -> f32 {
    let rgb = image.to_rgb8();
    let sum: f64 = rgb
        .pixels()
        .map(|p| f64::from(tone(f32::from(p.0[0]) / 255.0, space)))
        .sum();
    (sum / rgb.pixels().len() as f64) as f32
}

#[test]
fn the_mosaic_holds_the_overall_tone_of_the_source() {
    let source = disc(512);
    for space in [ToneSpace::Display, ToneSpace::Linear] {
        let want = mean_source_tone(&source, space);
        for dither in [
            Dither::Floyd,
            Dither::Atkinson,
            Dither::Jarvis,
            Dither::SierraLite,
            Dither::Bayer,
        ] {
            let mosaic = dice_dither(
                &source,
                &Options {
                    cells: 64,
                    dither,
                    tone_space: space,
                    style: TileStyle {
                        cell_px: 12,
                        ..TileStyle::default()
                    },
                    ..Options::default()
                },
            );
            let got = mean_output_tone(&mosaic.image, space);
            assert!(
                (got - want).abs() < 0.05,
                "{space:?} {dither:?}: {got} vs {want}"
            );
        }
    }
}

#[test]
fn bright_parts_of_the_source_become_bright_dice() {
    let source = disc(512);
    let mosaic = dice_dither(
        &source,
        &Options {
            cells: 48,
            ..Options::default()
        },
    );
    let middle = mosaic.faces[mosaic.rows / 2 * mosaic.cols + mosaic.cols / 2];
    let corner = mosaic.faces[0];
    assert_eq!(middle.style, dice_dither::DieStyle::Light);
    assert_eq!(corner.style, dice_dither::DieStyle::Dark);
}

#[test]
fn every_cell_of_the_output_is_a_die_with_a_seam_around_it() {
    let cell_px = 20;
    let mosaic = dice_dither(
        &disc(256),
        &Options {
            cells: 16,
            style: TileStyle {
                cell_px,
                ..TileStyle::default()
            },
            ..Options::default()
        },
    );
    let seam = (dice_dither::linear_to_srgb(TileStyle::default().seam_gray) * 255.0).round() as u8;
    for row in 0..mosaic.rows as u32 {
        for col in 0..mosaic.cols as u32 {
            let (x, y) = (col * cell_px, row * cell_px);
            let corner = mosaic.image.get_pixel(x, y).0[0];
            assert!(
                corner.abs_diff(seam) <= 1,
                "cell {col},{row} has no seam at its corner: {corner}"
            );
        }
    }
}

#[test]
fn a_die_shows_as_many_blobs_as_it_has_pips() {
    // Render a known face on its own and count connected pip blobs, so the
    // picture really is readable as dice rather than as generic halftone dots.
    for pips in 1..=6u8 {
        let cell_px = 40;
        let source = DynamicImage::ImageRgb8(RgbImage::from_pixel(8, 8, Rgb([0, 0, 0])));
        let mosaic = dice_dither(
            &source,
            &Options {
                cells: 1,
                rows: Some(1),
                palette: Palette::Dark,
                dither: Dither::None,
                rotate: false,
                // Force the tone that maps to this exact face.
                gamma: 1.0,
                normalize: dice_dither::Normalize::Off,
                style: TileStyle {
                    cell_px,
                    ..TileStyle::default()
                },
                ..Options::default()
            },
        );
        // The forced-black source always picks the one-pip black die; render
        // the other faces by asking the tile renderer directly.
        assert_eq!(mosaic.faces[0].pips, 1);

        let mut renderer = dice_dither::TileRenderer::new(TileStyle {
            cell_px,
            ..TileStyle::default()
        });
        let face = dice_dither::DieFace::new(dice_dither::DieStyle::Dark, pips);
        let tile = renderer.tile(face);
        assert_eq!(count_blobs(&tile.pixels, cell_px as usize), pips as usize);
    }
}

/// Count connected regions of bright pixels (the pips on a black die).
fn count_blobs(pixels: &[f32], size: usize) -> usize {
    let mut seen = vec![false; pixels.len()];
    let mut blobs = 0;
    for start in 0..pixels.len() {
        if seen[start] || pixels[start] < 0.5 {
            continue;
        }
        blobs += 1;
        let mut stack = vec![start];
        while let Some(index) = stack.pop() {
            if seen[index] {
                continue;
            }
            seen[index] = true;
            let (x, y) = (index % size, index / size);
            for (dx, dy) in [(1i32, 0i32), (-1, 0), (0, 1), (0, -1)] {
                let (nx, ny) = (x as i32 + dx, y as i32 + dy);
                if nx < 0 || ny < 0 || nx >= size as i32 || ny >= size as i32 {
                    continue;
                }
                let n = ny as usize * size + nx as usize;
                if !seen[n] && pixels[n] >= 0.5 {
                    stack.push(n);
                }
            }
        }
    }
    blobs
}

#[test]
fn the_cli_writes_a_picture_and_a_build_sheet() {
    let dir = tempfile::tempdir().expect("temp dir");
    let input = dir.path().join("source.png");
    disc(128).save(&input).expect("write source");
    let output = dir.path().join("out.png");
    let sheet = dir.path().join("out.txt");

    let status = std::process::Command::new(env!("CARGO_BIN_EXE_dice-dither"))
        .arg(&input)
        .args(["--cells", "24", "--cell-px", "10"])
        .arg("--sheet")
        .arg(&sheet)
        .arg("--inventory")
        .arg("-o")
        .arg(&output)
        .status()
        .expect("run dice-dither");
    assert!(status.success());

    let rendered = image::open(&output).expect("read output");
    assert_eq!(rendered.dimensions(), (240, 240));

    let text = std::fs::read_to_string(&sheet).expect("read sheet");
    let rows: Vec<&str> = text.lines().filter(|l| !l.starts_with('#')).collect();
    assert_eq!(rows.len(), 24);
    assert!(rows.iter().all(|r| r.split_whitespace().count() == 24));
}

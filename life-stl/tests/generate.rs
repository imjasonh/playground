use std::path::PathBuf;

use life_stl::config::{Config, Pattern, SupportMode, SupportStyle, DEFAULT_CELL_MM};
use life_stl::metrics::analyze;
use life_stl::search::evaluate_life_only;
use life_stl::{build_model, build_volume, generate_stl};

#[test]
fn still_garden_is_self_supporting_without_supports() {
    let config = Config {
        width: 24,
        height: 24,
        depth: 48,
        seed: 7,
        density: 0.25,
        pattern: Pattern::Random,
        cell_mm: DEFAULT_CELL_MM,
        base_layers: 1,
        mode: SupportMode::Raw,
        ..Config::default()
    };
    let report = evaluate_life_only(&config);
    assert!(report.life_voxels > 0);
    assert_eq!(report.orphan_life_voxels, 0);
    assert!(report.life_self_supporting());
}

#[test]
fn breakaway_adds_tips_for_soup_overhangs() {
    let config = Config {
        width: 16,
        height: 16,
        depth: 32,
        seed: 7,
        density: 0.35,
        pattern: Pattern::Soup,
        cell_mm: DEFAULT_CELL_MM,
        base_layers: 1,
        mode: SupportMode::Breakaway,
        ..Config::default()
    };
    let model = build_model(&config);
    assert!(model.support_tips > 0);
    assert_eq!(model.report.breakaway_support_tips, model.support_tips);
    assert!(model.triangles.len() > 12);
    let life = evaluate_life_only(&config);
    assert!(!life.life_self_supporting());
}

#[test]
fn soup_raw_has_overhanging_births() {
    let config = Config {
        width: 20,
        height: 20,
        depth: 40,
        seed: 99,
        density: 0.35,
        pattern: Pattern::Soup,
        mode: SupportMode::Raw,
        ..Config::default()
    };
    let volume = build_volume(&config);
    let report = analyze(&volume, config.cell_mm);
    assert_eq!(report.moore_unsupported_voxels, 0);
    assert!(report.strict_floating_voxels > 0);
}

#[test]
fn cells_from_mm_respects_default_cell() {
    assert_eq!(Config::cells_from_mm(100.0, DEFAULT_CELL_MM).unwrap(), 25);
    assert_eq!(Config::cells_from_mm(600.0, DEFAULT_CELL_MM).unwrap(), 150);
}

#[test]
fn writes_nonempty_stl_with_tree_supports() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("out.stl");
    let config = Config {
        width: 12,
        height: 12,
        depth: 16,
        seed: 1,
        pattern: Pattern::Random,
        mode: SupportMode::Breakaway,
        support: life_stl::SupportParams {
            style: SupportStyle::Tree,
            ..life_stl::SupportParams::default()
        },
        ..Config::default()
    };
    generate_stl(&config, &path).unwrap();
    let meta = std::fs::metadata(&path).unwrap();
    assert!(meta.len() > 84);
    let _: PathBuf = path;
}

#[test]
fn glider_is_not_self_supporting_without_braces() {
    // Face-only connectivity (raw/breakaway): a moving glider leaves orphans.
    let config = Config {
        width: 12,
        height: 12,
        depth: 24,
        pattern: Pattern::Glider,
        mode: SupportMode::Breakaway,
        ..Config::default()
    };
    let report = evaluate_life_only(&config);
    assert!(report.life_voxels > 0);
    assert!(report.orphan_life_voxels > 0);
    assert!(!report.life_self_supporting());
}

#[test]
fn gusset_glider_writes_one_piece_stl() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("glider.stl");
    let config = Config {
        width: 12,
        height: 12,
        depth: 24,
        pattern: Pattern::Glider,
        mode: SupportMode::Gusset,
        ..Config::default()
    };
    let report = generate_stl(&config, &path).unwrap();
    assert!(report.life_self_supporting());
    assert!(report.gusset_braces > 0);
    assert_eq!(report.breakaway_support_tips, 0);
    assert!(std::fs::metadata(&path).unwrap().len() > 84);
}

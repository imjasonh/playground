use std::path::PathBuf;

use life_stl::config::{Config, Pattern, SupportMode, DEFAULT_CELL_MM};
use life_stl::metrics::analyze;
use life_stl::search::evaluate_life_only;
use life_stl::{build_volume, generate_stl};

#[test]
fn still_garden_is_self_supporting_without_scaffold() {
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
    };
    let report = evaluate_life_only(&config);
    assert!(report.life_voxels > 0);
    assert_eq!(report.orphan_life_voxels, 0);
    assert!(report.life_self_supporting());
}

#[test]
fn scaffold_mode_clears_print_overhang_for_soup() {
    let config = Config {
        width: 16,
        height: 16,
        depth: 32,
        seed: 7,
        density: 0.35,
        pattern: Pattern::Soup,
        cell_mm: DEFAULT_CELL_MM,
        base_layers: 1,
        mode: SupportMode::Scaffold,
    };
    let volume = build_volume(&config);
    let report = analyze(&volume, config.cell_mm);
    assert_eq!(report.strict_floating_voxels, 0);
    assert!(report.life_voxels > 0);
    assert!(report.scaffold_voxels > 0);
    // Soup Life is not removable-scaffold-safe.
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
        cell_mm: DEFAULT_CELL_MM,
        base_layers: 1,
        mode: SupportMode::Raw,
    };
    let volume = build_volume(&config);
    let report = analyze(&volume, config.cell_mm);
    assert_eq!(report.moore_unsupported_voxels, 0);
    assert!(
        report.strict_floating_voxels > 0,
        "expected overhanging births in raw soup, got 0"
    );
}

#[test]
fn cells_from_mm_respects_default_cell() {
    // 10 cm × 10 cm × 60 cm at 4 mm cells → 25 × 25 × 150
    assert_eq!(Config::cells_from_mm(100.0, DEFAULT_CELL_MM).unwrap(), 25);
    assert_eq!(Config::cells_from_mm(600.0, DEFAULT_CELL_MM).unwrap(), 150);
}

#[test]
fn writes_nonempty_stl() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("out.stl");
    let config = Config {
        width: 12,
        height: 12,
        depth: 16,
        seed: 1,
        pattern: Pattern::Random,
        mode: SupportMode::Scaffold,
        ..Config::default()
    };
    generate_stl(&config, &path).unwrap();
    let meta = std::fs::metadata(&path).unwrap();
    assert!(meta.len() > 84, "STL should be larger than an empty header");
    let _: PathBuf = path;
}

#[test]
fn glider_is_not_self_supporting() {
    let config = Config {
        width: 12,
        height: 12,
        depth: 24,
        pattern: Pattern::Glider,
        mode: SupportMode::Scaffold,
        ..Config::default()
    };
    let report = evaluate_life_only(&config);
    assert!(report.life_voxels > 0);
    assert!(report.orphan_life_voxels > 0);
    assert!(!report.life_self_supporting());
}

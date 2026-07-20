use std::path::PathBuf;

use life_stl::config::{Config, Pattern, SupportMode};
use life_stl::metrics::analyze;
use life_stl::{build_volume, generate_stl};

#[test]
fn scaffold_mode_has_zero_overhang() {
    let config = Config {
        width: 16,
        height: 16,
        depth: 32,
        seed: 7,
        density: 0.35,
        pattern: Pattern::Random,
        cell_mm: 2.0,
        base_layers: 1,
        mode: SupportMode::Scaffold,
    };
    let volume = build_volume(&config);
    let report = analyze(&volume, config.cell_mm);
    assert_eq!(report.strict_floating_voxels, 0);
    assert_eq!(report.moore_unsupported_voxels, 0);
    assert!(report.life_voxels > 0);
    assert!(report.scaffold_voxels > 0);
}

#[test]
fn raw_random_has_overhanging_births() {
    let config = Config {
        width: 20,
        height: 20,
        depth: 40,
        seed: 99,
        density: 0.35,
        pattern: Pattern::Random,
        cell_mm: 2.0,
        base_layers: 1,
        mode: SupportMode::Raw,
    };
    let volume = build_volume(&config);
    let report = analyze(&volume, config.cell_mm);
    // Life is always Moore-supported layer-to-layer…
    assert_eq!(report.moore_unsupported_voxels, 0);
    // …but births commonly have an empty cell directly below.
    assert!(
        report.strict_floating_voxels > 0,
        "expected overhanging births in raw mode, got 0"
    );
}

#[test]
fn writes_nonempty_stl() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("out.stl");
    let config = Config {
        width: 8,
        height: 8,
        depth: 12,
        seed: 1,
        pattern: Pattern::Glider,
        mode: SupportMode::Scaffold,
        ..Config::default()
    };
    generate_stl(&config, &path).unwrap();
    let meta = std::fs::metadata(&path).unwrap();
    assert!(meta.len() > 84, "STL should be larger than an empty header");
    let _: PathBuf = path;
}

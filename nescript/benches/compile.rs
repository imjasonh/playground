//! End-to-end compilation benchmarks.
//!
//! Each `examples/*.ne` file becomes its own Criterion group that
//! times the full `preprocess → parse → analyze → lower →
//! optimize → codegen → peephole → link` pipeline the `nescript
//! build` CLI runs. The goal is to catch compile-time regressions
//! — today every example compiles in well under 100 ms, so a
//! change that doubles that shows up as a large red bar in
//! `cargo bench`'s output.
//!
//! The harness pre-reads every source file into memory before any
//! measurement starts. Criterion's sample iterations then run only
//! the in-memory compile path, so disk I/O never shows up on the
//! hot loop.
//!
//! The bench calls [`nescript::pipeline::compile_source`]
//! directly so it's impossible for it to drift away from the CLI
//! compile path — a 2026-04 regression where a hand-maintained
//! parallel copy of the pipeline missed a new bank-switching step
//! is exactly what this refactor prevents.

use std::fs;
use std::path::{Path, PathBuf};

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};

use nescript::parser;
use nescript::pipeline::{compile_source, CompileOptions};

/// Pre-loaded `.ne` source plus the directory it was read from. The
/// directory matters because sprite `@binary` / `@chr` paths resolve
/// relative to the source file — the current examples all use inline
/// CHR, but resolving relative to the right directory keeps the bench
/// honest if an example later grows an external asset.
struct Example {
    name: String,
    source: String,
    source_dir: PathBuf,
}

/// Scan `examples/*.ne` at the repo root and load every source file
/// into memory. Sorted by file name so the benchmark output is
/// reproducible across runs.
fn load_examples() -> Vec<Example> {
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let examples_dir = manifest_dir.join("examples");

    let mut entries: Vec<PathBuf> = fs::read_dir(&examples_dir)
        .unwrap_or_else(|e| panic!("failed to read {}: {e}", examples_dir.display()))
        .filter_map(Result::ok)
        .map(|e| e.path())
        .filter(|p| p.extension().is_some_and(|ext| ext == "ne"))
        .collect();
    entries.sort();

    entries
        .into_iter()
        .map(|path| {
            let raw = fs::read_to_string(&path)
                .unwrap_or_else(|e| panic!("failed to read {}: {e}", path.display()));
            // Preprocess once up front (include inlining, etc.)
            // so the hot loop never touches the filesystem.
            let source = parser::preprocess_source(&raw, Some(&path))
                .unwrap_or_else(|e| panic!("preprocess failed for {}: {e}", path.display()));
            let name = path
                .file_stem()
                .and_then(|s| s.to_str())
                .unwrap_or("unknown")
                .to_string();
            let source_dir = path
                .parent()
                .map_or_else(|| PathBuf::from("."), Path::to_path_buf);
            Example {
                name,
                source,
                source_dir,
            }
        })
        .collect()
}

/// Run the full compile pipeline on an in-memory source string
/// via the shared library entry point so the bench can't drift
/// away from the CLI build path.
fn compile_pipeline(source: &str, source_dir: &Path) -> Vec<u8> {
    match compile_source(source, source_dir, &CompileOptions::default()) {
        Ok(out) => out.rom,
        Err(e) => panic!("pipeline failed: {e:?}"),
    }
}

/// Criterion entry point. One benchmark group per example so the
/// HTML report groups them sensibly and so individual regressions
/// are easy to spot.
fn bench_compile(c: &mut Criterion) {
    let examples = load_examples();
    assert!(
        !examples.is_empty(),
        "no examples found under examples/*.ne — benchmark would measure nothing"
    );

    for example in &examples {
        let mut group = c.benchmark_group(format!("compile/{}", example.name));
        group.bench_with_input(
            BenchmarkId::from_parameter(&example.name),
            example,
            |b, ex| {
                b.iter(|| compile_pipeline(&ex.source, &ex.source_dir));
            },
        );
        group.finish();
    }
}

criterion_group!(benches, bench_compile);
criterion_main!(benches);

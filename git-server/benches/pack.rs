//! Benchmarks for the hot paths, runnable natively (`cargo bench`).
//!
//! Hand-rolled harness (criterion's current releases need a newer toolchain
//! than this crate pins). Each benchmark reports throughput so regressions in
//! the streaming pack paths — the CPU budget that matters inside a Worker —
//! are visible at a glance.
//!
//! Run: `cargo bench` (add `-- <filter>` to select benchmarks by name).

use futures::executor::block_on;
use git_server::object::ObjType;
use git_server::pack::index::{resolve_pack, NoExternalBases, PackIndex};
use git_server::pack::write::{test_support::build_pack, PackWriter};
use git_server::pack::PackScanner;
use git_server::storage::{MemStore, Store};
use std::time::Instant;

fn bench<F: FnMut()>(name: &str, bytes_per_iter: u64, mut f: F) {
    // Warm up.
    f();
    let mut iters = 0u32;
    let start = Instant::now();
    while start.elapsed().as_millis() < 1000 {
        f();
        iters += 1;
    }
    let elapsed = start.elapsed();
    let per_iter = elapsed / iters;
    let mibps = (bytes_per_iter as f64 * iters as f64) / elapsed.as_secs_f64() / (1024.0 * 1024.0);
    println!("{name:<40} {per_iter:>12.2?}/iter {mibps:>10.1} MiB/s ({iters} iters)");
}

/// A synthetic pack shaped like a real push: text-ish blobs of mixed sizes.
fn synthetic_pack(objects: usize, avg_size: usize) -> Vec<u8> {
    let mut objs = Vec::with_capacity(objects);
    let mut seed = 0x12345678u64;
    for i in 0..objects {
        // Deterministic pseudo-random compressible content.
        let size = avg_size / 2 + (i * 7919) % avg_size;
        let mut data = Vec::with_capacity(size);
        while data.len() < size {
            seed = seed
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            data.extend_from_slice(format!("line {} of object {}\n", seed % 1000, i).as_bytes());
        }
        data.truncate(size);
        objs.push((ObjType::Blob, data));
    }
    build_pack(&objs)
}

fn main() {
    // cargo bench passes flags like `--bench`; the first non-flag argument is
    // our name filter.
    let filter = std::env::args()
        .skip(1)
        .find(|a| !a.starts_with('-'))
        .unwrap_or_default();
    let run = |name: &str| filter.is_empty() || name.contains(&filter);

    println!("git-server benchmarks\n");

    // --- Pack scanning (the receive-pack ingest hot path) ------------------
    let pack_small = synthetic_pack(1_000, 512); // many small objects
    let pack_large = synthetic_pack(20, 512 * 1024); // few large objects
    if run("scan/small-objects") {
        bench(
            "scan/small-objects (1k x 512B)",
            pack_small.len() as u64,
            || {
                let mut s = PackScanner::new();
                for chunk in pack_small.chunks(16 * 1024) {
                    s.feed(chunk).unwrap();
                }
                assert_eq!(s.finish().unwrap().entries.len(), 1_000);
            },
        );
    }
    if run("scan/large-objects") {
        bench(
            "scan/large-objects (20 x 512KiB)",
            pack_large.len() as u64,
            || {
                let mut s = PackScanner::new();
                for chunk in pack_large.chunks(16 * 1024) {
                    s.feed(chunk).unwrap();
                }
                assert_eq!(s.finish().unwrap().entries.len(), 20);
            },
        );
    }

    // --- Delta resolution / indexing ---------------------------------------
    if run("index/resolve") {
        let store = MemStore::new();
        block_on(store.put("p", pack_small.clone())).unwrap();
        let scanned = {
            let mut s = PackScanner::new();
            s.feed(&pack_small).unwrap();
            s.finish().unwrap()
        };
        bench(
            "index/resolve (1k objects)",
            pack_small.len() as u64,
            || {
                let recs = block_on(resolve_pack(&store, "p", &scanned, &NoExternalBases)).unwrap();
                assert_eq!(recs.len(), 1_000);
            },
        );
    }

    // --- GSIX serialization --------------------------------------------
    if run("index/serialize") {
        let store = MemStore::new();
        block_on(store.put("p", pack_small.clone())).unwrap();
        let scanned = {
            let mut s = PackScanner::new();
            s.feed(&pack_small).unwrap();
            s.finish().unwrap()
        };
        let recs = block_on(resolve_pack(&store, "p", &scanned, &NoExternalBases)).unwrap();
        let idx = PackIndex::new(recs);
        let bytes = idx.to_bytes();
        bench(
            "index/serialize+parse (1k records)",
            bytes.len() as u64,
            || {
                let parsed = PackIndex::from_bytes(&idx.to_bytes()).unwrap();
                assert_eq!(parsed.len(), 1_000);
            },
        );
    }

    // --- Pack writing (fetch response hot path) -----------------------------
    if run("write/full-objects") {
        let content = vec![7u8; 64 * 1024];
        bench(
            "write/full-objects (100 x 64KiB)",
            (content.len() * 100) as u64,
            || {
                let mut w = PackWriter::new(100);
                for _ in 0..100 {
                    w.add_full(ObjType::Blob, &content);
                }
                let (out, _) = w.finish();
                assert!(!out.is_empty());
            },
        );
    }
    if run("write/precompressed-copy") {
        let content = vec![7u8; 64 * 1024];
        let z = git_server::pack::write::deflate(&content);
        bench(
            "write/precompressed-copy (100 x 64KiB)",
            (content.len() * 100) as u64,
            || {
                let mut w = PackWriter::new(100);
                for _ in 0..100 {
                    w.add_full_precompressed(3, content.len() as u64, &z);
                }
                let (out, _) = w.finish();
                assert!(!out.is_empty());
            },
        );
    }

    // --- Diff (blame hot path) ----------------------------------------------
    if run("diff/similar-files") {
        let mut old = String::new();
        let mut new = String::new();
        for i in 0..2_000 {
            old.push_str(&format!("line number {i} with some content\n"));
            if i % 50 == 0 {
                new.push_str(&format!("edited line {i}\n"));
            } else {
                new.push_str(&format!("line number {i} with some content\n"));
            }
        }
        bench(
            "diff/similar-files (2k lines, 2% edits)",
            (old.len() + new.len()) as u64,
            || {
                let m = git_server::diff::match_lines(old.as_bytes(), new.as_bytes());
                assert!(m.len() > 1_900);
            },
        );
    }
}

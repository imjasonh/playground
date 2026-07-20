# Browser app feasibility: Life sculpture lab (wasm + three.js)

Assessment for a browser app where users draw the **first generation** on a
grid, watch the resulting Z-stack evolve in 3D, and export STL / Bambu 3MF —
with all geometry work done by this crate compiled to WebAssembly and only a
thin JS shim for UI.

## Verdict: feasible, with the library as-is

The entire pipeline is pure computation — no filesystem, threads, or network:

| Stage | Module | wasm-ready? |
|-------|--------|-------------|
| Life simulation (padded, edge-free) | `life.rs`, `seed.rs`, `generation_windows` | yes |
| Voxelization + shrink-wrapped base | `lib.rs`, `volume.rs` | yes |
| Causality braces + causal orphan check | `gusset.rs` | yes |
| Mesh (cubes + braces) | `mesh.rs` | yes |
| Gates (complexity, removability) | `complexity.rs`, `removal.rs` | yes |
| Binary STL bytes | `write_stl_model` (needs an in-memory variant) | trivial |
| Bambu project 3MF bytes | `bambu.rs` (`project_3mf_bytes`, embedded presets) | yes — already returns `Vec<u8>` |

**Verified:** `cargo build --lib --target wasm32-unknown-unknown` compiles
today. The only change required was enabling getrandom's `js` backend on wasm
(already in `Cargo.toml`). The `zip`/`flate2` stack uses the pure-Rust
miniz_oxide backend, and `stl_io`/`serde_json` are pure Rust.

## Architecture

Per repo conventions this is a **new top-level browser app** (e.g.
`life-lab/`), static-hosted on GitHub Pages — browser apps deploy as-is with
no build step, so the compiled wasm + JS glue are **committed** (vendored),
with the build command documented and hooked into `npm run vendor` for the
daily deps workflow.

```
life-lab/
├── index.html          # UI shell
├── src/                # thin JS: grid editor, three.js viewer, export buttons
├── vendor/             # three.js + built wasm pkg (committed)
├── package.json        # test script (Jest on JS logic), vendor script
└── README.md
```

### Wasm interface (wasm-bindgen, added behind a `wasm` cargo feature)

Small surface, typed arrays across the boundary:

- `simulate(first_row: Uint8Array, w, h, depth) → SimResult`
  - live-cell coordinates per generation as a flat `Uint32Array`
    (x, y, z triples) for a three.js `InstancedMesh` of cubes — the UI never
    re-implements Life
  - gate verdicts (quiescent generation, period) for UI feedback
- `export_stl(...) → Uint8Array` (same inputs; returns binary STL)
- `export_3mf(...) → Uint8Array` (embedded A1 Mini presets; returns project 3MF)

Downloads use a `Blob` + anchor click; no server involved.

### UI (thin JS shim)

- **Editor**: an N×N clickable canvas/table for generation 0 (plus presets:
  soup density slider, methuselah stamps from the pattern catalog).
- **Viewer**: three.js `InstancedMesh` — one instance per voxel, a second
  mesh for braces (or skip braces visually; they're thin). Camera orbit,
  Z-clipping slider to scrub through time.
- **Controls**: board size, generations (N), cell mm, export buttons.

The heavy work (simulate + mesh) for a 44×44×44 board is milliseconds in
wasm; re-simulating live on every edit is fine.

## Sizing

- Wasm binary: this crate compiles to ~300–600 KB optimized (`opt-level=z`,
  `wasm-opt`); the embedded Bambu preset JSON adds ~25 KB. Acceptable for
  Pages.
- three.js vendored: ~600 KB min. Total page weight ≈ 1.5 MB.

## Risks / decisions

1. **clap in the lib**: `config.rs` derives `ValueEnum` (clap) — clap
   compiles to wasm fine, so no restructuring is required; if binary size
   matters, feature-gate the derive later.
2. **Vendored artifacts**: committing the wasm pkg conflicts with the
   "no build artifacts" instinct but matches how this repo deploys browser
   apps (copy as-is, no CI build). Precedent: vendored JS in other apps.
   The `vendor` npm script rebuilds it reproducibly (needs `wasm-pack` or
   `wasm-bindgen-cli` + the `wasm32-unknown-unknown` target).
3. **Feature flag**: add `wasm-bindgen` behind a `wasm` feature so the CLI
   build stays dependency-light; CI's existing Rust job is unaffected.
4. **Gates in the UI**: surface the complexity gate as advice, not a hard
   block — a user drawing their own seed should get the model either way,
   with a "settles at generation N" hint.

## Suggested next steps

1. Add the `wasm` feature + bindings module (`src/wasm.rs`) and an in-memory
   `stl_bytes(model)` helper (the only missing API).
2. Scaffold `life-lab/` with the editor + viewer against the built pkg.
3. Wire `npm run vendor` to rebuild wasm; add Jest tests for the JS shim and
   a Playwright smoke test (draw a glider, expect voxels rendered, export
   produces a non-empty file).

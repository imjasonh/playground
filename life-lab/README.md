# Life Lab

Draw a Game of Life **generation 0** on a grid, watch the evolution stack up
through Z as a 3D tower, and export it as a printable **STL** or a
ready-to-slice **Bambu Studio 3MF** — entirely in the browser.

All the geometry work (edge-free simulation, causality-brace supports, mesh,
STL/3MF export) is the [`life-stl`](../life-stl) Rust crate compiled to
WebAssembly. The JS here is a thin shim: a grid editor, a three.js viewer,
and download buttons.

- **Self-supporting by construction**: every Life birth has three parents
  diagonally below it (B3 → the FDM 45° rule); small braces connect them, so
  even gliders print as one piece with zero slicer supports.
- **Interestingness feedback**: the app tells you when a seed settles into a
  still life partway up (everything above would be a boring extruded tower).
- **Exports**: binary STL, or a Bambu Studio project 3MF with A1 Mini +
  generic PLA settings baked in (slicer supports **off** — the braces are the
  supports).
- **Print quote**: optional “Get quote” button talks to the
  [`life-print`](../life-print) Cloudflare Worker, which parks the STL briefly
  and asks [Slant 3D](https://www.slant3d.com/api) for a farm print price.
  Set the Worker URL in the panel (or `?printApi=https://…workers.dev`). Quote
  only — ordering/checkout is not wired; see `life-print/README.md`.

## Run locally

```bash
npx serve .        # or any static server; wasm needs http(s), not file://
```

## Test

```bash
npm test           # Node tests drive the real wasm module + editor helpers
```

## Rebuilding the wasm module

`vendor/life_stl/` is built from the `../life-stl` crate and committed (this
app deploys as static files, with no build step):

```bash
rustup target add wasm32-unknown-unknown
cargo install wasm-bindgen-cli --version <wasm-bindgen version in ../life-stl/Cargo.lock>
./build-wasm.sh
```

`vendor/three.module.min.js` and `vendor/OrbitControls.js` are vendored from
the [three](https://www.npmjs.com/package/three) npm package (r185).

# Palette swap

This page maps every pixel to the nearest color in a fixed palette, then
compares three implementations of that mapping inside one WebAssembly module.

- Ordinary Go.
- The portable `simd` package from the Go 1.27 experiment.
- Wasm `simd/archsimd` (`Int32x4`).

Squared Euclidean distance in RGB decides the nearest color. Ties keep the
earlier palette entry. The timer covers that loop only. Unpacking the image
and drawing the canvases stay outside it.

Palettes, from shortest to longest:

| Palette | Colors |
| --- | --- |
| Greyscale | 16 steps from 0 to 255 |
| NES | 54 unique entries from the NESdev 2C02 US wiki palette |
| Perler beads | 103 measured sRGB values |
| Embroidery floss | 456 published sRGB approximations of DMC stranded cotton |

A longer palette does more arithmetic per pixel, so the timing difference is
easier to see. Upload an image to start the benchmark. Choosing another
palette runs it again. Uploaded images are scaled so the long edge is at most
320 pixels. After the run, the fastest method is outlined.

## Run

Go 1.27 or newer is required to rebuild the module. The committed
`wasm/palette.wasm` was built with `GOEXPERIMENT=simd`.

```bash
cd palette-swap
python3 -m http.server 8080
```

Open `http://127.0.0.1:8080/`. A `file://` URL cannot load the Wasm module.

## Rebuild

```bash
cd palette-swap
./build-wasm.sh
```

`build-wasm.sh` also copies `wasm_exec.js` from the same toolchain. Keep those
two files paired. On Wasm the portable vector is 4 `int32` lanes, the same
width as `archsimd.Int32x4`.

## Test

```bash
cd palette-swap
go test ./...
GOEXPERIMENT=simd go test ./...
npm test
```

`go test` checks the scalar mapper. With `GOEXPERIMENT=simd`, the portable
mapper is included and must match. `npm test` loads the Wasm module in Node
and checks that scalar, portable, and archsimd produce the same indexes.

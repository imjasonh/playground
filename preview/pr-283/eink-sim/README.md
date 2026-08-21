# E-Ink Display Simulator

A client-side browser app that simulates how an image would look on real
e-ink / e-paper displays. Pick a real device, upload an image (or load a test
pattern), choose a dithering strategy, and preview the result rendered with a
**realistic reflective panel response** — muted inks, lifted blacks, off-white
paper substrate, and optional paper grain.

The goal is fidelity to the *limited* technology: not a pretty filter, but an
honest preview of what a given panel and palette can actually reproduce.

## Try it

Open `index.html` in a browser, or serve the directory:

```bash
cd eink-sim
npm start        # serves on http://localhost:3000
```

No build step — it's plain ES modules, HTML, and CSS.

## What it models

### Real devices

The catalog (see `src/displays.js`) covers the main e-paper technologies with
real resolutions, pixel densities, and refresh estimates:

| Technology | Examples | Palette |
|------------|----------|---------|
| Monochrome (Carta) | Kindle Paperwhite, reMarkable 2, Waveshare mono | 1-bit / 4- / 16-level grayscale |
| Color CFA (Kaleido 3) | Kobo Clara/Libra Colour, Boox Go Color 7 | 4096 muted colors @ 150 ppi |
| Full color (Gallery 3 / ACeP) | E Ink Gallery 3 | wide muted gamut |
| 6-color (Spectra 6 / E6) | Waveshare 4"/7.3"/13.3" E6 | black, white, red, yellow, green, blue |
| 7-color (ACeP) | Waveshare 5.65"/7.3" | + orange |
| ESL (3 & 4 color) | Waveshare tri/four-color | black/white/red(/yellow) |

### Palettes

Two palette kinds power the simulation (`src/dither.js`):

- **List palettes** — snap each pixel to the nearest of a fixed set of pigment
  inks (Spectra 6, ACeP 7-color, tri/four-color ESL). Nearest color uses a
  perceptual "redmean" distance.
- **Channel palettes** — quantize each RGB channel to _N_ evenly spaced levels
  (grayscale Carta panels, and continuous-color CFA/ACeP panels).

### Rendering strategies (dithering)

- None (nearest color)
- Error diffusion: Floyd–Steinberg, Atkinson, Jarvis–Judice–Ninke, Stucki,
  Sierra, Sierra Lite (with optional serpentine scanning)
- Ordered / Bayer: 2×2, 4×4, 8×8

### Realism

Quantization targets *ideal* primaries so dithering makes crisp decisions. A
separate **panel-response** pass then maps those ideals into each panel's
measured-ish reflective appearance:

- off-white paper substrate (not pure `#fff`)
- lifted black point (low contrast ratio)
- desaturated color inks (CFA and ACeP inks are noticeably muted)
- optional paper grain texture and a pixel grid when zoomed in
- **Viewing scale**: when a panel is shown below 1:1 (e.g. "Fit to window" for a
  large panel) the dither is area-averaged the way the eye integrates it at the
  panel's dot pitch; zoom in past 1:1 to inspect the individual ink dots.

Toggle the reflective response off to compare against ideal colors, and use the
**pre-processing** sliders (saturation / contrast / brightness / gamma) to
compensate the way real converters do. "Auto e-paper boost" applies a typical
saturation/contrast bump.

## Layout

```
eink-sim/
├── index.html          # UI
├── styles.css
├── src/
│   ├── color.js        # color math (pure)
│   ├── dither.js       # adjust, quantize, dithering, panel response (pure)
│   ├── displays.js     # device catalog + palettes + responses (pure)
│   └── app.js          # DOM wiring, canvas, upload, samples
└── tests/
    ├── dither.test.js
    └── displays.test.js
```

## Testing

Pure logic (color math, adjustments, dithering, palette/response data) is
covered by the Node test runner — no browser needed:

```bash
cd eink-sim
npm test
```

## Notes

- Everything runs in the browser; images never leave your machine.
- The reflective color values are tuned to *look* like each technology on a
  bright monitor, not to be colorimetrically exact.

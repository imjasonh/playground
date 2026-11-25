import test from "node:test";
import assert from "node:assert/strict";

import {
  createImage,
  adjustImage,
  quantizeImage,
  applyPanelResponse,
  renderPipeline,
  paletteColorCount,
  DITHER_METHODS,
  DIFFUSION_KERNELS,
  BAYER_MATRICES,
} from "../src/dither.js";
import {
  nearestColorIndex,
  colorDistanceSq,
  COLOR_METRICS,
  GRAY_MODES,
  toGray,
  srgbToLinear,
  linearToSrgb,
  rgbToOklab,
  rgbToLab,
  makeColorMatcher,
} from "../src/color.js";
import { BLUE_NOISE_SIZE, getBlueNoiseMatrix } from "../src/bluenoise.js";
import { OSTROMOUKHOV_WEIGHTS } from "../src/ostromoukhov.js";
import { DISPLAYS, getPalette, getResponse } from "../src/displays.js";
import { presetsForPalette, autoBoostForPalette } from "../src/presets.js";

// Build a solid-color RGBA image.
function solid(width, height, [r, g, b, a = 255]) {
  const img = createImage(width, height);
  for (let i = 0; i < img.data.length; i += 4) {
    img.data[i] = r;
    img.data[i + 1] = g;
    img.data[i + 2] = b;
    img.data[i + 3] = a;
  }
  return img;
}

function px(img, x, y) {
  const i = (y * img.width + x) * 4;
  return [img.data[i], img.data[i + 1], img.data[i + 2], img.data[i + 3]];
}

const BW = { kind: "list", colors: [[0, 0, 0], [255, 255, 255]] };
const SPECTRA6 = {
  kind: "list",
  colors: [
    [0, 0, 0],
    [255, 255, 255],
    [255, 0, 0],
    [255, 255, 0],
    [0, 255, 0],
    [0, 0, 255],
  ],
};
const GRAY16 = { kind: "channel", levels: 16, grayscale: true };
const KALEIDO = { kind: "channel", levels: 16, grayscale: false };

test("adjustImage is identity with default options", () => {
  const img = solid(4, 4, [10, 120, 240]);
  const out = adjustImage(img, {});
  assert.deepEqual([...out.data], [...img.data]);
  // returns a copy, not the same buffer
  assert.notEqual(out.data, img.data);
});

test("adjustImage brightness scales channels and clamps", () => {
  const out = adjustImage(solid(1, 1, [100, 200, 250]), { brightness: 1.5 });
  assert.deepEqual(px(out, 0, 0), [150, 255, 255, 255]);
});

test("adjustImage saturation=0 produces neutral gray", () => {
  const out = adjustImage(solid(1, 1, [200, 50, 50]), { saturation: 0 });
  const [r, g, b] = px(out, 0, 0);
  assert.equal(r, g);
  assert.equal(g, b);
});

test("adjustImage preserves alpha", () => {
  const out = adjustImage(solid(1, 1, [10, 20, 30, 128]), { brightness: 2 });
  assert.equal(px(out, 0, 0)[3], 128);
});

test("nearestColorIndex snaps to expected palette entry", () => {
  assert.equal(nearestColorIndex(250, 10, 10, SPECTRA6.colors), 2); // red
  assert.equal(nearestColorIndex(10, 10, 250, SPECTRA6.colors), 5); // blue
  assert.equal(nearestColorIndex(5, 5, 5, SPECTRA6.colors), 0); // black
});

test("colorDistanceSq is zero for identical colors and positive otherwise", () => {
  assert.equal(colorDistanceSq(1, 2, 3, 1, 2, 3), 0);
  assert.ok(colorDistanceSq(0, 0, 0, 255, 255, 255) > 0);
});

test("quantize 'none' maps every pixel to a palette color", () => {
  const img = solid(8, 8, [130, 130, 130]);
  const out = quantizeImage(img, BW, { method: "none" });
  for (let i = 0; i < out.data.length; i += 4) {
    const v = out.data[i];
    assert.ok(v === 0 || v === 255, `value ${v} not in {0,255}`);
    assert.equal(out.data[i + 1], v);
    assert.equal(out.data[i + 2], v);
  }
});

test("solid mid-gray dithered to B/W averages near the input", () => {
  const img = solid(64, 64, [128, 128, 128]);
  const out = quantizeImage(img, BW, { method: "floyd-steinberg" });
  let sum = 0;
  let count = 0;
  for (let i = 0; i < out.data.length; i += 4) {
    sum += out.data[i];
    count++;
  }
  const mean = sum / count;
  assert.ok(Math.abs(mean - 128) < 12, `mean ${mean} too far from 128`);
});

test("every dither method returns only palette colors for spectra6", () => {
  const img = solid(24, 24, [180, 90, 40]);
  for (const method of DITHER_METHODS) {
    const out = quantizeImage(img, SPECTRA6, { method });
    for (let i = 0; i < out.data.length; i += 4) {
      const idx = nearestColorIndex(
        out.data[i],
        out.data[i + 1],
        out.data[i + 2],
        SPECTRA6.colors,
      );
      const c = SPECTRA6.colors[idx];
      assert.deepEqual(
        [out.data[i], out.data[i + 1], out.data[i + 2]],
        c,
        `method ${method} produced non-palette color`,
      );
    }
  }
});

test("grayscale channel palette yields neutral, quantized tones", () => {
  const img = solid(16, 16, [200, 40, 40]);
  const out = quantizeImage(img, GRAY16, { method: "none" });
  for (let i = 0; i < out.data.length; i += 4) {
    assert.equal(out.data[i], out.data[i + 1]);
    assert.equal(out.data[i + 1], out.data[i + 2]);
    // Must be a multiple of 255/15 (17).
    assert.equal(out.data[i] % 17, 0);
  }
});

test("channel color palette quantizes each channel independently", () => {
  const out = quantizeImage(solid(2, 2, [200, 40, 40]), KALEIDO, {
    method: "none",
  });
  const [r, g, b] = px(out, 0, 0);
  assert.equal(r % 17, 0);
  assert.equal(g % 17, 0);
  assert.equal(b % 17, 0);
});

test("quantize preserves dimensions and alpha", () => {
  const img = solid(10, 7, [100, 150, 200, 200]);
  const out = quantizeImage(img, SPECTRA6, { method: "atkinson" });
  assert.equal(out.width, 10);
  assert.equal(out.height, 7);
  assert.equal(out.data[3], 200);
});

test("error diffusion does not smear ink into a far clean-white region", () => {
  // A large saturated region with no exact palette match (magenta) sitting
  // above a white region is the worst case for runaway error accumulation.
  // Every error-diffusion method must leave the far white rows white instead of
  // bleeding colored ink into them.
  const w = 48;
  const h = 48;
  const img = createImage(w, h);
  for (let y = 0; y < h; y++) {
    for (let x = 0; x < w; x++) {
      const i = (y * w + x) * 4;
      const white = y >= (h * 2) / 3;
      img.data[i] = 255;
      img.data[i + 1] = white ? 255 : 0;
      img.data[i + 2] = 255;
      img.data[i + 3] = 255;
    }
  }
  const diffusionMethods = DITHER_METHODS.filter(
    (m) => m !== "none" && !m.startsWith("bayer"),
  );
  for (const method of diffusionMethods) {
    const out = quantizeImage(img, SPECTRA6, { method });
    // The last two rows are far from the edge and were pure white input.
    for (let y = h - 2; y < h; y++) {
      for (let x = 0; x < w; x++) {
        assert.deepEqual(
          px(out, x, y).slice(0, 3),
          [255, 255, 255],
          `${method} bled ink into white at (${x},${y})`,
        );
      }
    }
  }
});

test("unknown dither method throws", () => {
  assert.throws(() => quantizeImage(solid(2, 2, [0, 0, 0]), BW, { method: "nope" }));
});

test("paletteColorCount counts list, gray, and channel palettes", () => {
  assert.equal(paletteColorCount(SPECTRA6), 6);
  assert.equal(paletteColorCount(GRAY16), 16);
  assert.equal(paletteColorCount(KALEIDO), 16 * 16 * 16);
});

test("applyPanelResponse lifts black and lowers white", () => {
  const response = { white: [210, 208, 200], black: [50, 50, 48], saturation: 1 };
  const white = applyPanelResponse(solid(1, 1, [255, 255, 255]), response);
  const black = applyPanelResponse(solid(1, 1, [0, 0, 0]), response);
  assert.deepEqual(px(white, 0, 0).slice(0, 3), [210, 208, 200]);
  assert.deepEqual(px(black, 0, 0).slice(0, 3), [50, 50, 48]);
});

test("applyPanelResponse reduces chroma with saturation < 1", () => {
  const response = { white: [255, 255, 255], black: [0, 0, 0], saturation: 0.5 };
  const out = applyPanelResponse(solid(1, 1, [255, 0, 0]), response);
  const [r, g, b] = px(out, 0, 0);
  assert.ok(r < 255, "red channel should drop");
  assert.ok(g > 0, "green channel should rise toward gray");
  assert.equal(g, b);
});

test("renderPipeline honors realism flag", () => {
  const img = solid(8, 8, [255, 255, 255]);
  const response = { white: [200, 200, 190], black: [40, 40, 38], saturation: 1 };
  const ideal = renderPipeline(img, BW, {
    dither: { method: "none" },
    response,
    realism: false,
  });
  const real = renderPipeline(img, BW, {
    dither: { method: "none" },
    response,
    realism: true,
  });
  assert.equal(px(ideal, 0, 0)[0], 255);
  assert.equal(px(real, 0, 0)[0], 200);
});

test("all diffusion kernels have normalized weights summing to <= divisor", () => {
  for (const [name, kernel] of Object.entries(DIFFUSION_KERNELS)) {
    const sum = kernel.cells.reduce((acc, [, , w]) => acc + w, 0);
    assert.ok(sum <= kernel.divisor, `${name} weights exceed divisor`);
  }
});

test("bayer matrices contain a full permutation of indices", () => {
  for (const [name, matrix] of Object.entries(BAYER_MATRICES)) {
    const n = matrix.length;
    const seen = new Set();
    for (const row of matrix) for (const v of row) seen.add(v);
    assert.equal(seen.size, n * n, `${name} is not a full permutation`);
  }
});

test("blue-noise matrix is 64x64 with uniform 0..255 histogram", () => {
  const mask = getBlueNoiseMatrix();
  assert.equal(mask.length, BLUE_NOISE_SIZE * BLUE_NOISE_SIZE);
  const counts = new Uint32Array(256);
  for (let i = 0; i < mask.length; i++) counts[mask[i]]++;
  for (let v = 0; v < 256; v++) {
    assert.equal(counts[v], 16, `value ${v} appeared ${counts[v]} times`);
  }
});

test("Ostromoukhov weights have 256 normalized triples summing to 1", () => {
  assert.equal(OSTROMOUKHOV_WEIGHTS.length, 256 * 3);
  for (let i = 0; i < 256; i++) {
    const sum =
      OSTROMOUKHOV_WEIGHTS[i * 3] +
      OSTROMOUKHOV_WEIGHTS[i * 3 + 1] +
      OSTROMOUKHOV_WEIGHTS[i * 3 + 2];
    assert.ok(Math.abs(sum - 1) < 1e-5, `level ${i} sum=${sum}`);
  }
});

test("sRGB <-> linear round-trip is accurate across 0..255", () => {
  for (let v = 0; v <= 255; v += 5) {
    const rt = linearToSrgb(srgbToLinear(v));
    assert.ok(Math.abs(rt - v) < 0.02, `v=${v} round-tripped to ${rt}`);
  }
  assert.equal(srgbToLinear(0), 0);
  assert.equal(srgbToLinear(255), 1);
  // sRGB 128 is ~0.216 in linear light (much darker than 0.5)
  assert.ok(Math.abs(srgbToLinear(128) - 0.2158) < 0.01);
});

test("Oklab and CIELAB preserve lightness order from black to white", () => {
  const okB = rgbToOklab(0, 0, 0);
  const okM = rgbToOklab(128, 128, 128);
  const okW = rgbToOklab(255, 255, 255);
  assert.ok(okB[0] < okM[0] && okM[0] < okW[0]);

  const labB = rgbToLab(0, 0, 0);
  const labM = rgbToLab(128, 128, 128);
  const labW = rgbToLab(255, 255, 255);
  assert.ok(labB[0] < labM[0] && labM[0] < labW[0]);
});

test("every color metric snaps exact palette colors to themselves", () => {
  for (const metric of COLOR_METRICS) {
    const match = makeColorMatcher(SPECTRA6.colors, metric);
    SPECTRA6.colors.forEach(([r, g, b], i) => {
      assert.equal(match(r, g, b), i, `metric ${metric} missed palette[${i}]`);
    });
  }
  assert.throws(() => makeColorMatcher(SPECTRA6.colors, "bogus"));
});

test("B&W channel filters weight RGB channels distinctly", () => {
  const redOnRed = toGray(255, 0, 0, "red");
  const redOnBlue = toGray(0, 0, 255, "red");
  const blueOnBlue = toGray(0, 0, 255, "blue");
  assert.ok(redOnRed > redOnBlue * 5);
  assert.ok(blueOnBlue > redOnBlue * 5);
  for (const mode of GRAY_MODES) {
    // Neutral gray stays unchanged under any normalized filter.
    assert.ok(Math.abs(toGray(100, 100, 100, mode) - 100) < 1e-6);
  }
  assert.throws(() => toGray(10, 20, 30, "ultraviolet"));
});

test("new B/W dithering algorithms preserve mid-gray tone average", () => {
  const img = solid(64, 64, [128, 128, 128]);
  for (const method of [
    "ostromoukhov",
    "riemersma",
    "blue-noise",
    "yliluoma",
    "burkes",
  ]) {
    const out = quantizeImage(img, BW, { method });
    let sum = 0;
    for (let i = 0; i < out.data.length; i += 4) {
      const v = out.data[i];
      assert.ok(v === 0 || v === 255, `${method} produced non-binary ${v}`);
      sum += v;
    }
    const mean = sum / (64 * 64);
    assert.ok(Math.abs(mean - 128) < 12, `${method} mean ${mean} far from 128`);
  }
});

test("linear-light dithering matches physical linear reflectance for sRGB 128", () => {
  const img = solid(64, 64, [128, 128, 128]);
  const expected = srgbToLinear(128) * 255; // ~55
  for (const method of ["ostromoukhov", "blue-noise", "riemersma"]) {
    const out = quantizeImage(img, { kind: "channel", levels: 2, grayscale: true }, {
      method,
      linearLight: true,
    });
    let sum = 0;
    for (let i = 0; i < out.data.length; i += 4) sum += out.data[i];
    const mean = sum / (64 * 64);
    assert.ok(
      Math.abs(mean - expected) < 12,
      `${method} linearLight mean ${mean} far from ${expected.toFixed(1)}`,
    );
  }
});

test("all color metrics work with spectra6 across diffusion and ordered methods", () => {
  const img = solid(16, 16, [120, 160, 210]);
  for (const metric of COLOR_METRICS) {
    for (const method of ["atkinson", "ostromoukhov", "yliluoma", "blue-noise"]) {
      const out = quantizeImage(img, SPECTRA6, { method, colorMetric: metric });
      for (let i = 0; i < out.data.length; i += 4) {
        const rgb = [out.data[i], out.data[i + 1], out.data[i + 2]];
        assert.ok(
          SPECTRA6.colors.some(
            (c) => c[0] === rgb[0] && c[1] === rgb[1] && c[2] === rgb[2],
          ),
          `${method}/${metric} produced non-palette color ${rgb}`,
        );
      }
    }
  }
});

test("adjustImage autoLevels stretches narrow tone range and preserves flat images", () => {
  const flat = solid(8, 8, [120, 120, 120]);
  assert.deepEqual([...adjustImage(flat, { autoLevels: true }).data], [...flat.data]);

  const img = createImage(10, 10);
  for (let i = 0; i < 100; i++) {
    const v = 80 + Math.round((i / 99) * 80); // [80..160]
    img.data[i * 4] = v;
    img.data[i * 4 + 1] = v;
    img.data[i * 4 + 2] = v;
    img.data[i * 4 + 3] = 255;
  }
  const stretched = adjustImage(img, { autoLevels: true });
  assert.equal(px(stretched, 0, 0)[0], 0);
  assert.equal(px(stretched, 9, 9)[0], 255);
});

test("adjustImage sharpen increases contrast across an edge and preserves alpha", () => {
  const img = createImage(6, 6);
  for (let y = 0; y < 6; y++) {
    for (let x = 0; x < 6; x++) {
      const v = x < 3 ? 100 : 150;
      const i = (y * 6 + x) * 4;
      img.data[i] = v;
      img.data[i + 1] = v;
      img.data[i + 2] = v;
      img.data[i + 3] = 200;
    }
  }
  const sharp = adjustImage(img, { sharpen: 1.0 });
  assert.ok(px(sharp, 2, 3)[0] < 100, "dark side of edge should darken");
  assert.ok(px(sharp, 3, 3)[0] > 150, "bright side of edge should brighten");
  assert.equal(px(sharp, 3, 3)[3], 200);
});

test("display presets are valid and render cleanly for every display in catalog", () => {
  const sample = solid(12, 12, [140, 100, 180]);
  for (const display of DISPLAYS) {
    const palette = getPalette(display);
    const response = getResponse(display);
    const presets = presetsForPalette(palette);
    assert.ok(presets.length >= 3, `${display.id} should have presets`);
    for (const preset of presets) {
      assert.ok(DITHER_METHODS.includes(preset.dither.method));
      if (preset.dither.colorMetric) {
        assert.ok(COLOR_METRICS.includes(preset.dither.colorMetric));
      }
      if (preset.dither.grayMode) {
        assert.ok(GRAY_MODES.includes(preset.dither.grayMode));
      }
      const out = renderPipeline(sample, palette, {
        adjust: preset.adjust,
        dither: preset.dither,
        response,
        realism: true,
      });
      assert.equal(out.width, 12);
      assert.equal(out.height, 12);
    }
    const boost = autoBoostForPalette(palette);
    assert.equal(typeof boost.sharpen, "number");
  }
});

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
import { nearestColorIndex, colorDistanceSq } from "../src/color.js";

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

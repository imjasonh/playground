import test from "node:test";
import assert from "node:assert/strict";

import {
  compareImages,
  comparisonSize,
  containLayout,
  coverPlacement,
  createImage,
  cropOverlay,
  describeCompare,
  diffAligned,
  fitMaxEdge,
  formatDimensions,
  pixelDistance,
  sampleBilinear,
  sampleCover,
  sourceCropRect,
  tintPixel,
  wasCropped,
} from "../src/diff.js";

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

function splitVertical(width, height, left, right) {
  const img = createImage(width, height);
  const mid = Math.floor(width / 2);
  for (let y = 0; y < height; y += 1) {
    for (let x = 0; x < width; x += 1) {
      const color = x < mid ? left : right;
      const i = (y * width + x) * 4;
      img.data[i] = color[0];
      img.data[i + 1] = color[1];
      img.data[i + 2] = color[2];
      img.data[i + 3] = color[3] ?? 255;
    }
  }
  return img;
}

function px(img, x, y) {
  const i = (y * img.width + x) * 4;
  return [img.data[i], img.data[i + 1], img.data[i + 2], img.data[i + 3]];
}

test("pixelDistance is 0 for identical pixels and 1 for opposite RGBA", () => {
  assert.equal(pixelDistance(10, 20, 30, 40, 10, 20, 30, 40), 0);
  assert.equal(pixelDistance(0, 0, 0, 0, 255, 255, 255, 255), 1);
});

test("tintPixel keeps the base color at 0 and goes red at 1", () => {
  assert.deepEqual(tintPixel(80, 120, 200, 0), [80, 120, 200]);
  assert.deepEqual(tintPixel(80, 120, 200, 1), [255, 0, 0]);
});

test("fitMaxEdge leaves small images alone and shrinks the long edge", () => {
  assert.deepEqual(fitMaxEdge(800, 600, 4096), { width: 800, height: 600 });
  assert.deepEqual(fitMaxEdge(8000, 4000, 2000), { width: 2000, height: 1000 });
});

test("comparisonSize scales same-aspect images to the larger one", () => {
  const size = comparisonSize(
    { width: 100, height: 50 },
    { width: 400, height: 200 },
  );
  assert.equal(size.width, 400);
  assert.equal(size.height, 200);
  assert.equal(size.aspectClose, true);
});

test("comparisonSize uses a compromise canvas when aspects differ", () => {
  const size = comparisonSize(
    { width: 200, height: 100 },
    { width: 100, height: 200 },
  );
  assert.equal(size.aspectClose, false);
  assert.equal(size.width, size.height);
  assert.equal(size.width, 200);
});

test("coverPlacement fills a wide canvas by cropping the tall source", () => {
  const placed = coverPlacement(100, 200, 200, 100);
  assert.equal(placed.scale, 2);
  assert.equal(placed.x, 0);
  assert.equal(placed.y, -150);
});

test("sourceCropRect reports the visible window in source pixels", () => {
  const crop = sourceCropRect(100, 200, 200, 100);
  assert.equal(crop.x, 0);
  assert.equal(crop.y, 75);
  assert.equal(crop.width, 100);
  assert.equal(crop.height, 50);
  assert.equal(wasCropped({ width: 100, height: 200 }, crop), true);
  assert.equal(
    wasCropped({ width: 200, height: 100 }, sourceCropRect(200, 100, 200, 100)),
    false,
  );
});

test("cropOverlay maps a source crop onto an object-fit contain box", () => {
  const laid = containLayout(200, 100, 100, 100);
  assert.equal(laid.width, 100);
  assert.equal(laid.height, 100);
  assert.equal(laid.x, 50);
  assert.equal(laid.y, 0);

  const overlay = cropOverlay(200, 100, 100, 100, {
    x: 10,
    y: 20,
    width: 40,
    height: 40,
  });
  assert.equal(overlay.x, 60);
  assert.equal(overlay.y, 20);
  assert.equal(overlay.width, 40);
  assert.equal(overlay.height, 40);
});

test("sampleBilinear returns a corner pixel exactly", () => {
  const img = solid(2, 2, [12, 34, 56, 78]);
  assert.deepEqual(
    sampleBilinear(img, 0, 0).map((n) => Math.round(n)),
    [12, 34, 56, 78],
  );
});

test("sampleCover upsizes a solid image without changing its color", () => {
  const out = sampleCover(solid(2, 2, [9, 18, 27]), 4, 4);
  assert.equal(out.width, 4);
  assert.equal(out.height, 4);
  assert.deepEqual(px(out, 0, 0), [9, 18, 27, 255]);
  assert.deepEqual(px(out, 3, 3), [9, 18, 27, 255]);
});

test("diffAligned leaves matching pixels alone and tints mismatches red", () => {
  const a = splitVertical(4, 2, [20, 40, 80], [200, 200, 200]);
  const b = splitVertical(4, 2, [20, 40, 80], [0, 0, 0]);
  const { image, differingPixels, totalPixels, meanDiff } = diffAligned(a, b);

  assert.equal(totalPixels, 8);
  assert.equal(differingPixels, 4);
  assert.ok(meanDiff > 0);

  const same = px(image, 0, 0);
  assert.deepEqual(same, [20, 40, 80, 255]);

  const changed = px(image, 3, 0);
  assert.ok(changed[0] > 180);
  assert.ok(changed[1] < 80);
  assert.ok(changed[2] < 80);
});

test("compareImages resizes a smaller same-aspect image before diffing", () => {
  const a = solid(4, 2, [10, 20, 30]);
  const b = solid(8, 4, [10, 20, 30]);
  const result = compareImages(a, b);
  assert.equal(result.width, 8);
  assert.equal(result.height, 4);
  assert.equal(result.differingPixels, 0);
  assert.equal(result.croppedA, false);
  assert.equal(result.croppedB, false);
  assert.equal(result.scaledA, true);
  assert.equal(result.scaledB, false);
});

test("compareImages center-crops different aspect ratios", () => {
  const wide = solid(8, 4, [255, 0, 0]);
  const tall = solid(4, 8, [0, 0, 255]);
  const result = compareImages(wide, tall);
  assert.equal(result.croppedA, true);
  assert.equal(result.croppedB, true);
  assert.equal(result.aspectClose, false);
  assert.equal(result.width, result.height);
  assert.ok(result.differingFraction > 0.9);
});

test("describeCompare names the crop and the match", () => {
  const a = { width: 8, height: 4, name: "a.png" };
  const b = { width: 4, height: 8, name: "b.png" };
  const result = compareImages(solid(8, 4, [1, 2, 3]), solid(4, 8, [9, 8, 7]));
  const text = describeCompare(result, a, b);
  assert.match(text, /A 8\u00d74/);
  assert.match(text, /B 4\u00d78/);
  assert.match(text, /center-cropping both images/);
  assert.match(text, /differ/);
});

test("describeCompare says matching same-size images match", () => {
  const img = solid(3, 3, [50, 60, 70]);
  const result = compareImages(img, solid(3, 3, [50, 60, 70]));
  assert.equal(
    describeCompare(result, { width: 3, height: 3 }, { width: 3, height: 3 }),
    "A 3\u00d73 \u00b7 B 3\u00d73. Compared 3\u00d73. Images match.",
  );
});

test("formatDimensions uses a multiply sign", () => {
  assert.equal(formatDimensions(1920, 1080), "1920\u00d71080");
});

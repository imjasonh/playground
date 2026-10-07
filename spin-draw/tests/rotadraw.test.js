import test from "node:test";
import assert from "node:assert/strict";

import {
  REFERENCE_ANGLE,
  buildDisc,
  paperPolylines,
  polylineLength,
  shufflePieces,
  splitStrokes,
  totalLength,
} from "../src/rotadraw.js";
import { pictureById } from "../src/pictures.js";
import { maskFromRgba, strokesFromMask, traceContours } from "../src/trace.js";

function nearly(a, b, eps = 1e-6) {
  assert.ok(Math.abs(a - b) <= eps, `${a} vs ${b}`);
}

test("splitStrokes cuts a line into equal pieces", () => {
  const line = [
    { x: 0, y: 0 },
    { x: 100, y: 0 },
  ];
  const pieces = splitStrokes([line], 4);
  assert.equal(pieces.length, 4);
  let sum = 0;
  for (const piece of pieces) {
    const len = totalLength(piece);
    nearly(len, 25, 1e-6);
    sum += len;
  }
  nearly(sum, 100, 1e-6);
  nearly(pieces[0][0][0].x, 0);
  nearly(pieces[3][0][pieces[3][0].length - 1].x, 100);
});

test("splitStrokes does not bridge separate strokes", () => {
  const pieces = splitStrokes(
    [
      [
        { x: 0, y: 0 },
        { x: 10, y: 0 },
      ],
      [
        { x: 0, y: 5 },
        { x: 10, y: 5 },
      ],
    ],
    2,
  );
  assert.equal(pieces.length, 2);
  for (const piece of pieces) {
    for (const poly of piece) {
      for (const point of poly) {
        assert.ok(point.y === 0 || point.y === 5);
      }
    }
  }
});

test("turning each piece puts it back on the picture", () => {
  const disc = buildDisc(pictureById("dog").strokes, { steps: 18 });
  assert.equal(disc.steps.length, 18);
  for (const step of disc.steps) {
    const back = paperPolylines(step);
    assert.equal(back.length, step.paper.length);
    for (let p = 0; p < back.length; p += 1) {
      assert.equal(back[p].length, step.paper[p].length);
      for (let i = 0; i < back[p].length; i += 1) {
        nearly(back[p][i].x, step.paper[p][i].x, 1e-6);
        nearly(back[p][i].y, step.paper[p][i].y, 1e-6);
      }
    }
    const aligned = step.labelAngle + step.theta;
    nearly(Math.cos(aligned), Math.cos(REFERENCE_ANGLE), 1e-6);
    nearly(Math.sin(aligned), Math.sin(REFERENCE_ANGLE), 1e-6);
    for (const poly of step.local) {
      for (const point of poly) {
        assert.ok(Math.hypot(point.x, point.y) <= disc.outer + 1e-6);
        assert.ok(Math.hypot(point.x, point.y) >= disc.inner - 1e-6);
      }
    }
    assert.ok(Math.hypot(step.label.x, step.label.y) <= disc.outer + 1e-6);
  }
});

test("piece lengths add up to the fitted picture", () => {
  const disc = buildDisc(pictureById("house").strokes, { steps: 12 });
  let pieceSum = 0;
  for (const step of disc.steps) {
    pieceSum += totalLength(step.paper);
  }
  nearly(pieceSum, totalLength(disc.fitted), 1e-4);
  assert.ok(polylineLength(disc.fitted[0]) > 0);
});

function pieceKey(piece) {
  const point = piece[0][0];
  return `${point.x.toFixed(3)},${point.y.toFixed(3)}`;
}

test("numbered lines are a stable shuffle of the stroke pieces", () => {
  const strokes = pictureById("dog").strokes;
  const disc = buildDisc(strokes, { steps: 16 });
  const again = buildDisc(strokes, { steps: 16 });
  const sequential = splitStrokes(disc.fitted, 16).map(pieceKey);
  const mixed = disc.steps.map((step) => pieceKey(step.paper));
  assert.equal(mixed.length, sequential.length);
  assert.notDeepEqual(mixed, sequential);
  assert.deepEqual([...mixed].sort(), [...sequential].sort());
  assert.deepEqual(
    mixed,
    again.steps.map((step) => pieceKey(step.paper)),
  );
  const forced = shufflePieces(splitStrokes(disc.fitted, 16), 1).map(pieceKey);
  assert.notDeepEqual(forced, sequential);
});

test("an empty picture makes no lines", () => {
  const disc = buildDisc([[{ x: 1, y: 1 }]], { steps: 10 });
  assert.equal(disc.steps.length, 0);
});

test("a dark rectangle traces as one outline", () => {
  const width = 24;
  const height = 16;
  const data = new Uint8ClampedArray(width * height * 4);
  for (let i = 0; i < data.length; i += 4) {
    data[i] = 255;
    data[i + 1] = 255;
    data[i + 2] = 255;
    data[i + 3] = 255;
  }
  for (let y = 4; y <= 11; y += 1) {
    for (let x = 5; x <= 16; x += 1) {
      const o = (y * width + x) * 4;
      data[o] = 0;
      data[o + 1] = 0;
      data[o + 2] = 0;
    }
  }
  const mask = maskFromRgba(data, width, height, 128);
  const contours = traceContours(mask, width, height);
  assert.equal(contours.length, 1);
  for (const point of contours[0]) {
    assert.equal(mask[point.y * width + point.x], 1);
    assert.ok(point.x >= 5 && point.x <= 16);
    assert.ok(point.y >= 4 && point.y <= 11);
  }
  const strokes = strokesFromMask(mask, width, height, { minLength: 8, epsilon: 1.2 });
  assert.equal(strokes.length, 1);
  assert.ok(strokes[0].length < contours[0].length);
  assert.ok(strokes[0].length >= 4);
});

test("transparent pixels are not ink", () => {
  const data = new Uint8ClampedArray(16);
  data[0] = 0;
  data[1] = 0;
  data[2] = 0;
  data[3] = 0;
  const mask = maskFromRgba(data, 2, 2, 200);
  assert.equal(mask[0], 0);
});

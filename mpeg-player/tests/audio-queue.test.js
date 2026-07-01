import test from "node:test";
import assert from "node:assert/strict";

import { PlanarAudioQueue } from "../src/audio-queue.js";

function pull(queue, length) {
  const left = new Float32Array(length);
  const right = new Float32Array(length);
  const rendered = queue.pull(left, right);
  return { left: [...left], right: [...right], rendered };
}

test("queues stereo PCM without changing equal-rate samples", () => {
  const queue = new PlanarAudioQueue(48_000);
  queue.push(
    48_000,
    new Float32Array([0, 1, 2, 3, 4, 5]),
    new Float32Array([10, 11, 12, 13, 14, 15]),
  );

  const output = pull(queue, 4);
  assert.equal(output.rendered, 4);
  assert.deepEqual(output.left, [0, 1, 2, 3]);
  assert.deepEqual(output.right, [10, 11, 12, 13]);
  assert.equal(queue.availableFrames, 2);
});

test("linearly resamples across output frames", () => {
  const queue = new PlanarAudioQueue(48_000);
  queue.push(
    24_000,
    new Float32Array([0, 1, 2, 3]),
    new Float32Array([4, 5, 6, 7]),
  );

  const output = pull(queue, 4);
  assert.deepEqual(output.left, [0, 0.5, 1, 1.5]);
  assert.deepEqual(output.right, [4, 4.5, 5, 5.5]);
});

test("interpolates cleanly across MP2 chunk boundaries", () => {
  const queue = new PlanarAudioQueue(44_100);
  queue.push(
    44_100,
    new Float32Array([0, 1]),
    new Float32Array([10, 11]),
  );
  queue.push(
    44_100,
    new Float32Array([2, 3]),
    new Float32Array([12, 13]),
  );

  const output = pull(queue, 3);
  assert.deepEqual(output.left, [0, 1, 2]);
  assert.deepEqual(output.right, [10, 11, 12]);
});

test("a source sample-rate change discards incompatible queued data", () => {
  const queue = new PlanarAudioQueue(48_000);
  queue.push(
    44_100,
    new Float32Array([1, 2, 3]),
    new Float32Array([1, 2, 3]),
  );
  queue.push(
    48_000,
    new Float32Array([8, 9, 10]),
    new Float32Array([18, 19, 20]),
  );

  const output = pull(queue, 2);
  assert.deepEqual(output.left, [8, 9]);
  assert.deepEqual(output.right, [18, 19]);
});

test("underflow leaves the remainder silent", () => {
  const queue = new PlanarAudioQueue(48_000);
  queue.push(
    48_000,
    new Float32Array([0.25]),
    new Float32Array([0.5]),
  );

  const output = pull(queue, 4);
  assert.equal(output.rendered, 0);
  assert.deepEqual(output.left, [0, 0, 0, 0]);
  assert.deepEqual(output.right, [0, 0, 0, 0]);
  assert.equal(queue.underruns, 1);
});

test("rejects malformed PCM chunks", () => {
  const queue = new PlanarAudioQueue(48_000);
  assert.equal(queue.push(0, new Float32Array(2), new Float32Array(2)), false);
  assert.equal(
    queue.push(48_000, new Float32Array(2), new Float32Array(1)),
    false,
  );
  assert.equal(queue.availableFrames, 0);
});

test("bounds queued PCM and drops the oldest frames", () => {
  const queue = new PlanarAudioQueue(10, 0.3);
  queue.push(
    10,
    new Float32Array([0, 1, 2, 3, 4]),
    new Float32Array([10, 11, 12, 13, 14]),
  );

  assert.equal(queue.availableFrames, 3);
  assert.equal(queue.droppedFrames, 2);
  const output = pull(queue, 2);
  assert.deepEqual(output.left, [2, 3]);
  assert.deepEqual(output.right, [12, 13]);
});

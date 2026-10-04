import test from "node:test";
import assert from "node:assert/strict";

import {
  confidenceFromProbs,
  formatDecision,
  round4,
  softmax,
  tempBucket,
  temperatureScale,
} from "../src/calibration.js";
import { makeQuestion } from "../src/questions.js";

test("softmax is invariant to a constant shift and sums to 1", () => {
  const a = softmax([1, 2, 3]);
  const b = softmax([11, 12, 13]);
  assert.equal(a.length, 3);
  assert.ok(Math.abs(a.reduce((s, v) => s + v, 0) - 1) < 1e-9);
  a.forEach((value, i) => {
    assert.ok(Math.abs(value - b[i]) < 1e-9);
  });
});

test("tempBucket and scale read per-cardinality overrides", () => {
  assert.equal(tempBucket("choice", 2), "choice:2");
  assert.equal(tempBucket("noul", 8), "noul:6-10");
  const calibration = {
    temperature: [2, 3, 4],
    temperatureByOptions: { "choice:3-5": 1.5 },
  };
  assert.equal(temperatureScale(calibration, "choice", 4), 1.5);
  assert.equal(temperatureScale(calibration, "score", 2), 3);
  assert.equal(
    temperatureScale({ temperature: [1, 1, 1], temperature_by_options: { "choice:3-5": 1.25 } }, "choice", 4),
    1.25,
  );
});

test("confidence is 1 for a one-hot pair and 0 for uniform", () => {
  assert.equal(confidenceFromProbs([1, 0], 2), 1);
  const uniform = confidenceFromProbs([0.5, 0.5], 2);
  assert.ok(Math.abs(uniform) < 1e-9);
});

test("formatDecision writes System One answers", () => {
  const choice = makeQuestion("choice", "pick", [
    { label: "billing" },
    { label: "shipping" },
  ]);
  const billed = formatDecision([3, 0], [1, 0], choice);
  assert.equal(billed.choice, "billing");
  assert.ok(billed.probabilities.billing > 0.9);
  assert.equal(billed.confidence, round4(confidenceFromProbs(softmax([3, 0]))));

  const score = makeQuestion("score", "rate", ["low", "high"]);
  const rated = formatDecision(new Float32Array([0, 4]), new Float32Array([1]), score);
  assert.ok(rated.score > 0.9);
  assert.equal(rated.legend["1"], "high");

  const noul = makeQuestion("noul", "yes?");
  const yes = formatDecision([0, 5], [2, 0], noul);
  assert.equal(yes.type, "noul");
  assert.ok(yes.noul > 0.9);
  assert.equal(yes.confidence, round4(Math.max(yes.noul, 1 - yes.noul)));
});

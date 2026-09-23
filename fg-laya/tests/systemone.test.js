import test from "node:test";
import assert from "node:assert/strict";
import { flightQuestions } from "../src/questions.js";
import { askLocal, detectBackend, softmax } from "../src/systemone.js";

test("detectBackend prefers Laya unless a Jev key is set", () => {
  const prevBackend = process.env.SYSTEMONE_BACKEND;
  const prevKey = process.env.OPENROUTER_API_KEY;
  delete process.env.SYSTEMONE_BACKEND;
  delete process.env.OPENROUTER_API_KEY;
  try {
    assert.equal(detectBackend(), "laya");
    process.env.OPENROUTER_API_KEY = "test-key";
    assert.equal(detectBackend(), "jev");
    process.env.SYSTEMONE_BACKEND = "local";
    assert.equal(detectBackend(), "local");
  } finally {
    if (prevBackend == null) {
      delete process.env.SYSTEMONE_BACKEND;
    } else {
      process.env.SYSTEMONE_BACKEND = prevBackend;
    }
    if (prevKey == null) {
      delete process.env.OPENROUTER_API_KEY;
    } else {
      process.env.OPENROUTER_API_KEY = prevKey;
    }
  }
});

test("softmax is a distribution", () => {
  const p = softmax([1, 2, 3]);
  assert.ok(Math.abs(p.reduce((a, b) => a + b, 0) - 1) < 1e-9);
  assert.ok(p[2] > p[1] && p[1] > p[0]);
});

test("local System One turns right when the waypoint is to the right", () => {
  const state = {
    heading_err_deg: 40,
    roll_deg: 0,
    altitude_err_ft: 0,
    airspeed_err_kt: 0,
    airspeed_kt: 100,
    pitch_deg: 2,
    vsi_fpm: 0,
    slip_deg: 0,
    waypoint: { distance_nm: 1.2 },
  };
  const { answers } = askLocal(state, flightQuestions());
  assert.equal(answers.aileron.type, "choice");
  assert.match(answers.aileron.choice, /right/);
  assert.equal(answers.arrived.noul < 0.5, true);
  assert.ok(answers.aileron.confidence > 0.3);
});

test("local System One pitches down when high and slow", () => {
  const state = {
    heading_err_deg: 0,
    roll_deg: 0,
    altitude_err_ft: 600,
    airspeed_err_kt: -18,
    airspeed_kt: 62,
    pitch_deg: 8,
    vsi_fpm: 200,
    slip_deg: 0,
    waypoint: { distance_nm: 2 },
  };
  const { answers } = askLocal(state, flightQuestions());
  assert.match(answers.elevator.choice, /down/);
  assert.ok(answers.throttle.choice === "more" || answers.throttle.choice === "full");
});

import test from "node:test";
import assert from "node:assert/strict";
import {
  buildOverlay,
  formatBanner,
  overlayPropertyWrites,
} from "../src/overlay.js";

test("overlay lists each surface choice and the value written this tick", () => {
  const overlay = buildOverlay({
    ticks: 42,
    backend: "local",
    model: "local-systemone",
    latency_ms: 1,
    answers: {
      aileron: { type: "choice", choice: "left", confidence: 0.8, probabilities: { left: 0.8 } },
      elevator: { type: "choice", choice: "hold", confidence: 0.6, probabilities: { hold: 0.6 } },
      throttle: { type: "choice", choice: "more", confidence: 0.7, probabilities: { more: 0.7 } },
      rudder: { type: "choice", choice: "center", confidence: 0.9, probabilities: { center: 0.9 } },
    },
    controls: { aileron: -0.14, elevator: 0.06, throttle: 0.82, rudder: 0 },
    target: { aileron: -0.16, elevator: 0.06, throttle: 0.85, rudder: 0 },
  });
  assert.equal(overlay.tick, 42);
  assert.equal(overlay.rows.length, 4);
  assert.equal(overlay.rows[0].choice, "left");
  assert.equal(overlay.rows[0].applied, -0.14);
  assert.match(overlay.banner, /tick 42/);
  assert.match(overlay.banner, /AIL left -0.14 80%/);
  assert.match(overlay.banner, /THR more 0.82 70%/);
});

test("overlay property writes feed the FlightGear HUD labels", () => {
  const overlay = buildOverlay({
    ticks: 7,
    answers: { aileron: { type: "choice", choice: "right" } },
    controls: { aileron: 0.2, elevator: 0, throttle: 0.7, rudder: 0 },
  });
  const paths = Object.fromEntries(overlayPropertyWrites(overlay));
  assert.equal(paths["/laya/overlay/tick"], "tick 7");
  assert.match(paths["/laya/overlay/aileron"], /AIL right/);
  assert.ok(paths["/laya/overlay/banner"].startsWith("tick 7"));
});

test("formatBanner stays one line", () => {
  const line = formatBanner(3, [
    { line: "AIL left -0.10 70%" },
    { line: "ELE hold 0.04 50%" },
  ]);
  assert.equal(line.includes("\n"), false);
  assert.match(line, /tick 3/);
});

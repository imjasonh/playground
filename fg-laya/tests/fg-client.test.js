import test from "node:test";
import assert from "node:assert/strict";
import {
  airbornePresets,
  engineProps,
  needsAirborneReset,
  runCgiUrl,
} from "../src/fg-client.js";
import { overlayPropertyWrites } from "../src/overlay.js";

test("run.cgi URL encodes the fgcommand", () => {
  assert.equal(
    runCgiUrl("http://127.0.0.1:9146/", "reposition"),
    "http://127.0.0.1:9146/run.cgi?value=reposition",
  );
});

test("airborne presets put the 172 over the water at cruise", () => {
  const paths = Object.fromEntries(airbornePresets());
  assert.equal(paths["/sim/presets/altitude-ft"], 3500);
  assert.equal(paths["/sim/presets/airspeed-kt"], 105);
  assert.equal(paths["/sim/presets/heading-deg"], 270);
  assert.ok(paths["/sim/presets/latitude-deg"] > 37);
});

test("engine props start magnetos, mixture, and JSBSim running", () => {
  const paths = Object.fromEntries(engineProps());
  assert.equal(paths["/controls/switches/magnetos"], 3);
  assert.equal(paths["/controls/engines/engine/mixture"], 1);
  assert.equal(paths["/fdm/jsbsim/propulsion/set-running"], -1);
  assert.equal(paths["/engines/active-engine/running"], true);
});

test("overlay writes are property pairs the HUD can bind", () => {
  const writes = overlayPropertyWrites({
    tick: 9,
    banner: "tick 9   AIL left -0.10",
    rows: [{ surface: "aileron", line: "AIL left -0.10 80%" }],
  });
  const paths = Object.fromEntries(writes);
  assert.equal(paths["/laya/overlay/tick"], "tick 9");
  assert.equal(paths["/laya/overlay/aileron"], "AIL left -0.10 80%");
});

test("needsAirborneReset fires on a crash or inverted attitude", () => {
  assert.equal(needsAirborneReset({ altitude_ft: 3500, airspeed_kt: 100, roll_deg: 20 }), false);
  assert.equal(needsAirborneReset({ altitude_ft: -1, airspeed_kt: 3, roll_deg: -179 }), true);
  assert.equal(needsAirborneReset({ altitude_ft: 3000, airspeed_kt: 55, roll_deg: 40 }), false);
  assert.equal(needsAirborneReset({ altitude_ft: 3000, airspeed_kt: 90, roll_deg: 95 }), true);
});

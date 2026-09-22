import test from "node:test";
import assert from "node:assert/strict";
import { answersToTargets, arrivedYes, slewControls } from "../src/actuate.js";

test("right aileron choice becomes a positive aileron", () => {
  const targets = answersToTargets(
    {
      aileron: { choice: "right" },
      elevator: { choice: "hold" },
      throttle: { choice: "hold" },
      rudder: { choice: "center" },
    },
    { aileron: 0, elevator: 0, rudder: 0, throttle: 0.7 },
    { heading_err_deg: 20, roll_deg: 0 },
  );
  assert.ok(targets.aileron > 0);
});

test("arrived noul is yes at 0.5", () => {
  assert.equal(arrivedYes({ arrived: { noul: 0.5 } }), true);
  assert.equal(arrivedYes({ arrived: { noul: 0.49 } }), false);
});

test("slew does not overshoot a small step", () => {
  const next = slewControls(
    { aileron: 0, elevator: 0, rudder: 0, throttle: 0.5 },
    { aileron: 0.1, elevator: 0, rudder: 0, throttle: 0.5 },
    0.05,
    2.4,
  );
  assert.ok(next.aileron > 0 && next.aileron <= 0.1);
});

import test from "node:test";
import assert from "node:assert/strict";
import { createAircraft } from "../src/aircraft.js";
import { createPilot, runPilot } from "../src/loop.js";
import { headingErrorDeg } from "../src/geo.js";

test("local System One holds a left-hand circle without losing the airplane", async () => {
  const pilot = createPilot({
    aircraft: createAircraft({ heading_deg: 20, roll_deg: 0 }),
    mission: "circle",
    backend: "local",
    world: "sim",
  });
  const frames = await runPilot(pilot, { seconds: 90, dt: 0.1 });
  const last = frames[frames.length - 1];
  const alts = frames.map((f) => f.aircraft.altitude_ft);
  const speeds = frames.map((f) => f.aircraft.airspeed_kt);
  const banks = frames.map((f) => Math.abs(f.aircraft.roll_deg));
  assert.ok(Math.min(...alts) > 2200, `min alt ${Math.min(...alts)}`);
  assert.ok(Math.max(...alts) < 5200, `max alt ${Math.max(...alts)}`);
  assert.ok(Math.min(...speeds) > 60, `min ias ${Math.min(...speeds)}`);
  assert.ok(Math.max(...banks) < 42, `max bank ${Math.max(...banks)}`);
  const startHdg = frames[0].aircraft.heading_deg;
  const endHdg = last.aircraft.heading_deg;
  let travel = 0;
  let prev = startHdg;
  for (const frame of frames) {
    travel += Math.abs(headingErrorDeg(prev, frame.aircraft.heading_deg));
    prev = frame.aircraft.heading_deg;
  }
  assert.ok(travel > 200, `heading travel ${travel} from ${startHdg} to ${endHdg}`);
  const radiusErrs = frames.slice(300).map((f) => Math.abs((f.nav.distance_nm ?? 0) - f.nav.radius_nm));
  const mean = radiusErrs.reduce((a, b) => a + b, 0) / radiusErrs.length;
  assert.ok(mean < 0.55, `mean radius error ${mean}`);
  assert.equal(last.decision.backend, "local");
  assert.ok(last.decision.answers.aileron.choice);
});

test("random waypoints move the target after an arrival noul", async () => {
  let n = 0;
  const rng = () => {
    n += 1;
    return (n * 0.37) % 1;
  };
  const pilot = createPilot({
    aircraft: createAircraft(),
    mission: "waypoints",
    backend: "local",
    world: "sim",
    rng,
  });
  await runPilot(pilot, { seconds: 80, dt: 0.1 });
  assert.ok(pilot.nav.arrivals >= 1, `arrivals ${pilot.nav.arrivals}`);
  assert.ok(pilot.nav.waypoint_index >= 1);
});

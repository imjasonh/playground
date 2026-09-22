import { answersToTargets, arrivedYes, slewControls } from "./actuate.js";
import { aircraftRaw, applyControls, createAircraft, stepAircraft } from "./aircraft.js";
import { offsetNm } from "./geo.js";
import { createNav, maybeArrive, navSnapshot, updateNav } from "./nav.js";
import { observe } from "./observe.js";
import { flightQuestions } from "./questions.js";
import { askSystemOne, detectBackend } from "./systemone.js";

export function createPilot(options = {}) {
  const aircraft = options.aircraft ?? createAircraft(options.ic);
  const home = options.home ?? { lat: aircraft.lat, lon: aircraft.lon };
  const nav = options.nav ?? createNav({
    mission: options.mission ?? "circle",
    home,
    rng: options.rng,
  });
  if ((options.mission ?? "circle") === "circle" && options.placeOnCircle !== false) {
    const onRing = offsetNm(nav.center, 0, nav.radius_nm);
    aircraft.lat = onRing.lat;
    aircraft.lon = onRing.lon;
    aircraft.heading_deg = 90;
  }
  return {
    aircraft,
    nav,
    questions: options.questions ?? flightQuestions(),
    backend: options.backend ?? detectBackend(),
    ask: options.ask ?? askSystemOne,
    controls: {
      aileron: aircraft.aileron,
      elevator: aircraft.elevator,
      rudder: aircraft.rudder,
      throttle: aircraft.throttle,
    },
    lastDecision: null,
    ticks: 0,
    decideEvery: options.decideEvery ?? 1,
    trail: [],
    world: options.world ?? "sim",
  };
}

export async function tickPilot(pilot, dt, extras = {}) {
  if (extras.raw) {
    overlayRaw(pilot.aircraft, extras.raw);
  }
  const pos = {
    lat: pilot.aircraft.lat,
    lon: pilot.aircraft.lon,
    heading_deg: pilot.aircraft.heading_deg,
  };
  updateNav(pilot.nav, pos);
  const state = observe(aircraftRaw(pilot.aircraft), navSnapshot(pilot.nav));
  let decision = pilot.lastDecision;
  if (!decision || pilot.ticks % pilot.decideEvery === 0) {
    try {
      decision = await pilot.ask(state, pilot.questions, { backend: pilot.backend });
    } catch (err) {
      if (!pilot.lastDecision) {
        throw err;
      }
      decision = {
        ...pilot.lastDecision,
        backend: `${pilot.lastDecision.backend}-stale`,
        error: String(err.message ?? err),
      };
    }
    pilot.lastDecision = decision;
  }
  maybeArrive(pilot.nav, pos, arrivedYes(decision.answers));
  const target = answersToTargets(decision.answers, pilot.controls, state);
  pilot.controls = slewControls(pilot.controls, target, dt);
  applyControls(pilot.aircraft, pilot.controls);
  if (pilot.world === "sim" && !extras.freezePhysics) {
    stepAircraft(pilot.aircraft, dt);
  }
  if (pilot.ticks % 4 === 0) {
    pilot.trail.push({ lat: pilot.aircraft.lat, lon: pilot.aircraft.lon, alt: pilot.aircraft.alt_ft });
    if (pilot.trail.length > 400) {
      pilot.trail.shift();
    }
  }
  pilot.ticks += 1;
  return {
    state,
    decision,
    controls: { ...pilot.controls },
    target,
    nav: navSnapshot(pilot.nav),
    aircraft: aircraftRaw(pilot.aircraft),
  };
}

export async function runPilot(pilot, { seconds, dt = 0.1, onTick } = {}) {
  const steps = Math.round(seconds / dt);
  const frames = [];
  for (let i = 0; i < steps; i++) {
    const frame = await tickPilot(pilot, dt);
    if (onTick) {
      onTick(frame, pilot);
    }
    frames.push(frame);
  }
  return frames;
}

function overlayRaw(ac, raw) {
  ac.lat = raw.lat;
  ac.lon = raw.lon;
  ac.alt_ft = raw.altitude_ft;
  ac.heading_deg = raw.heading_deg;
  ac.pitch_deg = raw.pitch_deg;
  ac.roll_deg = raw.roll_deg;
  ac.airspeed_kt = raw.airspeed_kt;
  ac.vsi_fpm = raw.vsi_fpm;
  ac.slip_deg = raw.slip_deg ?? 0;
  if (Number.isFinite(raw.aileron)) ac.aileron = raw.aileron;
  if (Number.isFinite(raw.elevator)) ac.elevator = raw.elevator;
  if (Number.isFinite(raw.rudder)) ac.rudder = raw.rudder;
  if (Number.isFinite(raw.throttle)) ac.throttle = raw.throttle;
}

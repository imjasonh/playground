#!/usr/bin/env node
import { createAircraft } from "../src/aircraft.js";
import {
  createFgClient,
  fgPrepAirborne,
  fgProbe,
  fgReadSensors,
  fgWriteControls,
  needsAirborneReset,
} from "../src/fg-client.js";
import { createHudServer } from "../src/hud-server.js";
import { createPilot, tickPilot } from "../src/loop.js";
import { DEFAULT_ALT_FT, DEFAULT_HOME, DEFAULT_SPEED_KT } from "../src/nav.js";
import { buildOverlay, overlayPropertyWrites } from "../src/overlay.js";
import { detectBackend } from "../src/systemone.js";

const args = parseArgs(process.argv.slice(2));
const backend = args.backend ?? detectBackend();
const mission = args.mode ?? "circle";
const world = args.world ?? "sim";
const dt = Number(args.dt ?? 0.1);
const hz = 1 / dt;
const seconds = args.seconds != null ? Number(args.seconds) : null;
const port = Number(args.port ?? 8788);

const ac = createAircraft({
  lat: Number(args.lat ?? DEFAULT_HOME.lat),
  lon: Number(args.lon ?? DEFAULT_HOME.lon),
  alt_ft: Number(args.alt ?? DEFAULT_ALT_FT),
  heading_deg: Number(args.heading ?? 0),
  airspeed_kt: Number(args.speed ?? DEFAULT_SPEED_KT),
});

const pilot = createPilot({
  aircraft: ac,
  mission,
  backend,
  world: world === "fg" ? "fg" : "sim",
  decideEvery: Number(args.decideEvery ?? 1),
});

const hud = createHudServer();
await hud.listen(port);
console.log(`hud http://127.0.0.1:${port}  backend=${backend}  world=${world}  mode=${mission}`);

let lastResetAt = 0;
let fg = null;
if (world === "fg" || world === "auto") {
  fg = createFgClient({
    httpBase: args.fgHttp ?? process.env.FG_HTTP,
    telnetPort: Number(args.fgTelnet ?? 5501),
  });
  try {
    const transport = await fgProbe(fg);
    console.log(`flightgear ${transport}`);
    await fgPrepAirborne(fg, {
      lat: ac.lat,
      lon: ac.lon,
      alt_ft: ac.alt_ft,
      heading_deg: ac.heading_deg,
      airspeed_kt: ac.airspeed_kt,
    });
    const raw = await fgReadSensors(fg);
    seedControls(pilot, raw);
    lastResetAt = Date.now();
    pilot.world = "fg";
  } catch (err) {
    if (world === "fg") {
      throw err;
    }
    console.log(`flightgear offline (${err.message}); using built-in kinematics`);
    fg = null;
    pilot.world = "sim";
  }
}

const started = Date.now();
let running = true;
let lastTick = Date.now();
process.on("SIGINT", () => {
  running = false;
});

while (running) {
  const tickStarted = Date.now();
  const wallDt = Math.min(0.4, Math.max(dt, (tickStarted - lastTick) / 1000));
  lastTick = tickStarted;
  const extras = {};
  if (fg) {
    try {
      extras.raw = await fgReadSensors(fg);
      extras.freezePhysics = true;
      if (needsAirborneReset(extras.raw) && Date.now() - lastResetAt > 8000) {
        lastResetAt = Date.now();
        console.log("flightgear reset: airplane left the envelope");
        await fgPrepAirborne(fg, {
          lat: ac.lat,
          lon: ac.lon,
          alt_ft: ac.alt_ft,
          heading_deg: ac.heading_deg,
          airspeed_kt: ac.airspeed_kt,
        });
        extras.raw = await fgReadSensors(fg);
        seedControls(pilot, extras.raw);
        pilot.lastDecision = null;
      }
    } catch (err) {
      console.error("fg read failed", err.message);
    }
  }
  const frame = await tickPilot(pilot, wallDt, extras);
  frame.overlay = buildOverlay({
    ticks: pilot.ticks,
    answers: frame.decision.answers,
    controls: frame.controls,
    target: frame.target,
    backend: frame.decision.backend ?? backend,
    model: frame.decision.model,
    latency_ms: frame.decision.latency_ms ?? 0,
  });
  if (fg) {
    try {
      const choice = [
        frame.decision.answers.aileron?.choice,
        frame.decision.answers.elevator?.choice,
        frame.decision.answers.throttle?.choice,
        frame.decision.answers.rudder?.choice,
      ].join(" ");
      await fgWriteControls(fg, frame.controls, {
        backend: frame.decision.backend ?? backend,
        choice,
        overlayWrites: overlayPropertyWrites(frame.overlay),
      });
    } catch (err) {
      console.error("fg write failed", err.message);
    }
  }
  hud.publish(publicFrame(frame, pilot, backend));
  if (pilot.ticks % Math.round(hz) === 0) {
    const a = frame.aircraft;
    console.log(
      `${a.altitude_ft.toFixed(0)} ft  ${a.airspeed_kt.toFixed(0)} kt  hdg ${a.heading_deg.toFixed(0)}  ` +
        `bank ${a.roll_deg.toFixed(0)}  ${frame.decision.answers.aileron?.choice}/` +
        `${frame.decision.answers.elevator?.choice}/` +
        `${frame.decision.answers.throttle?.choice}  ${frame.decision.backend}`,
    );
  }
  if (seconds != null && (Date.now() - started) / 1000 >= seconds) {
    break;
  }
  const used = Date.now() - tickStarted;
  const wait = Math.max(0, dt * 1000 - used);
  await sleep(wait);
}

await hud.close();

function publicFrame(frame, pilot, backendName) {
  const overlay = frame.overlay ?? buildOverlay({
    ticks: pilot.ticks,
    answers: frame.decision.answers,
    controls: frame.controls,
    target: frame.target,
    backend: frame.decision.backend ?? backendName,
    model: frame.decision.model,
    latency_ms: frame.decision.latency_ms ?? 0,
  });
  return {
    t: Date.now(),
    ticks: pilot.ticks,
    backend: frame.decision.backend ?? backendName,
    model: frame.decision.model,
    world: pilot.world,
    mission: pilot.nav.mission,
    aircraft: frame.aircraft,
    nav: frame.nav,
    state: frame.state,
    answers: frame.decision.answers,
    controls: frame.controls,
    target: frame.target,
    overlay,
    trail: pilot.trail,
    latency_ms: frame.decision.latency_ms ?? 0,
    error: frame.decision.error ?? null,
  };
}

function parseArgs(argv) {
  const out = {};
  for (let i = 0; i < argv.length; i++) {
    const token = argv[i];
    if (!token.startsWith("--")) {
      continue;
    }
    const key = token.slice(2);
    const next = argv[i + 1];
    if (!next || next.startsWith("--")) {
      out[key] = true;
      continue;
    }
    out[key] = next;
    i += 1;
  }
  return out;
}

function seedControls(pilot, raw) {
  if (!raw) {
    return;
  }
  if (Number.isFinite(raw.aileron)) pilot.controls.aileron = raw.aileron;
  if (Number.isFinite(raw.elevator)) pilot.controls.elevator = raw.elevator;
  if (Number.isFinite(raw.rudder)) pilot.controls.rudder = raw.rudder;
  if (Number.isFinite(raw.throttle)) pilot.controls.throttle = raw.throttle;
}

function sleep(ms) {
  return new Promise((resolve) => setTimeout(resolve, ms));
}

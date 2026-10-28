// Plays Keep in jsnes and checks the raycast loop.
//
//   node keep_probe.mjs [outdir]
//
// Three boots of a debug ROM:
//
//   - Start, and the first view has the hall guard in it.
//     Walking toward that guard draws the tall sprite, and
//     shots from the center columns bring its health down.
//   - Standing in front of that guard long enough runs the
//     player out of hearts and lands on the dead screen.
//   - A scripted walk to the exit gate lands on the win screen.
//
// Every frame of those boots must finish before the next NMI
// (peek 0x07FF stays 0) and must stay inside 8 sprites on a
// scanline (peek 0x07FD stays 0). Release builds strip both
// counters, so this probe builds with --debug.

import { execFileSync } from "node:child_process";
import { mkdirSync, readFileSync, writeFileSync } from "node:fs";
import { createRequire } from "node:module";
import { fileURLToPath } from "node:url";
import { createEmulator } from "./emu.mjs";

const require = createRequire(import.meta.url);
const { PNG } = require("pngjs");

const OUT = process.argv[2] || "/tmp/keep-probe";
mkdirSync(OUT, { recursive: true });

const ROOT = fileURLToPath(new URL("../..", import.meta.url));
const NESCRIPT = process.env.NESCRIPT || `${ROOT}/target/release/nescript`;
const SYMS = `${OUT}/keep.mlb`;
execFileSync(NESCRIPT, [
  "build",
  `${ROOT}/examples/keep.ne`,
  "--debug",
  "-o",
  `${OUT}/keep.nes`,
  "--symbols",
  SYMS,
]);
const ROM = readFileSync(`${OUT}/keep.nes`);

const sym = {};
for (const line of readFileSync(SYMS, "utf8").split("\n")) {
  const [kind, addr, name] = line.split(":");
  if (name) sym[`${kind}:${name}`] = parseInt(addr, 16);
}
function ram(name) {
  const a = sym[`R:${name}`];
  if (a === undefined) throw new Error(`no RAM symbol ${name}`);
  return a;
}

// Read LEVEL out of the source so the route and the ROM share
// one map. The const is a flat list of 256 decimal bytes.
const levelSrc = readFileSync(`${ROOT}/examples/keep/constants.ne`, "utf8");
const levelBody = levelSrc.match(/const LEVEL: u8\[256\] = \[([\s\S]*?)\]/);
if (!levelBody) throw new Error("LEVEL const not found in constants.ne");
const LEVEL = levelBody[1]
  .split(",")
  .map((s) => parseInt(s.trim(), 10))
  .filter((n) => !Number.isNaN(n));
if (LEVEL.length !== 256) throw new Error(`LEVEL has ${LEVEL.length} bytes`);

const A = {
  px: ram("px"),
  py: ram("py"),
  ang: ram("ang"),
  health: ram("health"),
  ammo: ram("ammo"),
  phase: ram("phase"),
  rendered: ram("rendered"),
  outcome: ram("outcome"),
  endRow: ram("end_row"),
  gx: ram("gx"),
  gy: ram("gy"),
  ghp: ram("ghp"),
  gseen: ram("gseen"),
  gcol0: ram("gcol0"),
  gcol1: ram("gcol1"),
  gdist: ram("gdist"),
};
const OVERRUN = 0x07ff;
const SPRITE = 0x07fd;
const PH_IDLE = 2;

const UP = 4;
const LEFT = 6;
const RIGHT = 7;
const BTN_A = 0;
const START = 3;

let failures = 0;
function fail(msg) {
  failures++;
  console.log(`FAIL  ${msg}`);
}

function boot() {
  const emu = createEmulator();
  emu.loadRom(ROM);
  const peek = (a) => emu.peek(a);
  function check() {
    const over = peek(OVERRUN);
    const spr = peek(SPRITE);
    if (over !== 0) fail(`frame overrun count ${over}`);
    if (spr !== 0) fail(`sprite overflow count ${spr}`);
  }
  function shot(name) {
    const png = new PNG({ width: 256, height: 240 });
    png.data = emu.pixels();
    writeFileSync(`${OUT}/${name}.png`, PNG.sync.write(png));
  }
  function press(btn) {
    emu.buttonDown(1, btn);
    emu.runFrames(1);
    check();
    emu.buttonUp(1, btn);
    // The edge detector samples the released frame. Without
    // this, the next press is still "held" from the CPU's view.
    emu.runFrames(1);
    check();
  }
  function waitIdle() {
    for (let i = 0; i < 60; i++) {
      if (peek(A.phase) === PH_IDLE) return true;
      if (peek(A.endRow) > 0) return false;
      emu.runFrames(1);
      check();
    }
    fail("phase never returned to idle");
    return false;
  }
  // One press, consumed on an idle frame, then wait until the
  // picture that press started has finished.
  function act(btn) {
    if (!waitIdle()) return;
    const rend = peek(A.rendered);
    press(btn);
    if (peek(A.rendered) !== rend) {
      waitIdle();
    }
  }
  function startGame() {
    emu.runFrames(8);
    check();
    press(START);
    waitIdle();
  }
  return { emu, peek, check, shot, press, waitIdle, act, startGame };
}

function cellOf(x, y) {
  return (y & 0xf0) | (x >> 4);
}

function guardCells(peek) {
  const blocked = new Set();
  for (let i = 0; i < 4; i++) {
    if (peek(A.ghp + i) === 0) continue;
    blocked.add(cellOf(peek(A.gx + i), peek(A.gy + i)));
  }
  return blocked;
}

// First step from the player toward the gate, skipping walls
// and living guards. Returns the neighbor cell, or null.
function nextStep(peek) {
  const start = cellOf(peek(A.px), peek(A.py));
  let goal = -1;
  for (let i = 0; i < 256; i++) {
    if (LEVEL[i] === 4) goal = i;
  }
  const blocked = guardCells(peek);
  blocked.delete(start);
  const prev = new Array(256).fill(-1);
  const q = [start];
  prev[start] = start;
  const dirs = [1, 16, -1, -16];
  while (q.length > 0) {
    const c = q.shift();
    if (c === goal) break;
    for (const d of dirs) {
      const n = c + d;
      if (n < 0 || n > 255 || prev[n] !== -1) continue;
      if ((d === 1 || d === -1) && (n >> 4) !== (c >> 4)) continue;
      if (LEVEL[n] !== 0 && LEVEL[n] !== 4) continue;
      if (blocked.has(n)) continue;
      prev[n] = c;
      q.push(n);
    }
  }
  if (prev[goal] === -1) return null;
  let c = goal;
  while (prev[c] !== start && prev[c] !== c) c = prev[c];
  return c;
}

function dirTo(from, to) {
  if ((to & 15) > (from & 15)) return 0;
  if (to > from) return 16;
  if ((to & 15) < (from & 15)) return 32;
  return 48;
}

function turnButton(ang, want) {
  let d = (want - ang) & 63;
  if (d === 0) return 0;
  if (d > 32) return LEFT;
  return RIGHT;
}

// A guard the gun can hit: alive, in the last cast, and covering
// the center columns. fire() uses the same column test.
function inSights(peek) {
  for (let i = 0; i < 4; i++) {
    if (peek(A.ghp + i) === 0 || peek(A.gseen + i) === 0) continue;
    const c0 = peek(A.gcol0 + i);
    const c1 = peek(A.gcol1 + i);
    if (c0 <= 9 && c1 >= 7) return true;
  }
  return false;
}

// Boot 1. The hall guard is in the opening view. Walk up to
// it, then fire until that guard is down.
function combat() {
  console.log("-- combat");
  const g = boot();
  g.startGame();
  if (g.peek(A.gseen) !== 1) fail("hall guard was not in the first view");
  if (g.peek(A.health) !== 5) fail(`health ${g.peek(A.health)} at the first view`);
  g.shot("first-view");
  const x0 = g.peek(A.px);
  for (let i = 0; i < 12; i++) g.act(UP);
  if (g.peek(A.px) <= x0) fail("walking east did not move the player");
  if (g.peek(A.gdist) > 4) fail(`guard distance ${g.peek(A.gdist)} after the walk`);
  g.shot("close");
  const ammo0 = g.peek(A.ammo);
  let shots = 0;
  while (g.peek(A.ghp) > 0 && shots < 6) {
    g.act(BTN_A);
    shots++;
  }
  if (g.peek(A.ghp) !== 0) fail(`hall guard health ${g.peek(A.ghp)} after ${shots} shots`);
  if (g.peek(A.ammo) >= ammo0) fail("firing did not spend a round");
  g.shot("downed");
  console.log(
    `     walked to (${g.peek(A.px)},${g.peek(A.py)}), ${shots} shots, ammo ${g.peek(A.ammo)}`,
  );
}

// Boot 2. Walk into the hall guard's range and wait. The
// guard's shots have to empty the hearts.
function death() {
  console.log("-- death");
  const g = boot();
  g.startGame();
  for (let i = 0; i < 10; i++) g.act(UP);
  let frames = 0;
  while (g.peek(A.health) > 0 && frames < 4000) {
    g.emu.runFrames(1);
    g.check();
    frames++;
  }
  if (g.peek(A.health) !== 0) fail(`still alive after ${frames} frames in front of the guard`);
  for (let i = 0; i < 30; i++) {
    g.emu.runFrames(1);
    g.check();
  }
  if (g.peek(A.endRow) === 0) fail("death did not reach the end screen");
  if (g.peek(A.outcome) !== 1) fail(`outcome ${g.peek(A.outcome)} on death`);
  g.shot("died");
  console.log(`     hearts empty after ${frames} frames`);
}

// Boot 3. Walk the open cells to the gate.
function escape() {
  console.log("-- escape");
  const g = boot();
  g.startGame();
  let stuck = 0;
  for (let step = 0; step < 400; step++) {
    if (g.peek(A.endRow) > 0) break;
    if (g.peek(A.health) === 0) {
      fail(`died at (${g.peek(A.px)},${g.peek(A.py)}) on the way to the gate`);
      g.shot("escape-died");
      return;
    }
    const here = cellOf(g.peek(A.px), g.peek(A.py));
    if (inSights(g.peek)) {
      g.act(BTN_A);
      continue;
    }
    if (LEVEL[here] === 4) {
      g.act(UP);
      continue;
    }
    const next = nextStep(g.peek);
    if (next === null) {
      if (g.peek(A.gseen) !== 0) g.act(BTN_A);
      else g.emu.runFrames(8);
      stuck++;
      if (stuck > 8) {
        fail(`no path from cell ${here}`);
        g.shot("escape-stuck");
        return;
      }
      continue;
    }
    stuck = 0;
    const want = dirTo(here, next);
    const turn = turnButton(g.peek(A.ang), want);
    const before = g.peek(A.px) | (g.peek(A.py) << 8);
    if (turn !== 0) g.act(turn);
    else g.act(UP);
    const after = g.peek(A.px) | (g.peek(A.py) << 8);
    if (turn === 0 && before === after && g.peek(A.gseen) !== 0) g.act(BTN_A);
  }
  if (g.peek(A.health) === 0 || g.peek(A.outcome) !== 0 || g.peek(A.endRow) === 0) {
    fail(
      `did not escape (health ${g.peek(A.health)} outcome ${g.peek(A.outcome)} end ${g.peek(A.endRow)} at ${g.peek(A.px)},${g.peek(A.py)})`,
    );
  }
  for (let i = 0; i < 24; i++) {
    g.emu.runFrames(1);
    g.check();
  }
  g.shot("escaped");
  console.log(`     gate at (${g.peek(A.px)},${g.peek(A.py)})`);
}

combat();
death();
escape();
if (failures > 0) {
  console.log(`${failures} failure(s)`);
  process.exit(1);
}
console.log("keep probe passed");

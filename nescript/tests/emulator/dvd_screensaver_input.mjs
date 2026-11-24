// Drives examples/dvd_screensaver.nes with both controllers in jsnes and
// checks what the pad does to the logos:
//
//   - With no input the logo is exactly the plain screensaver. The
//     golden and the committed GIF already pin its pixels.
//   - Pushing against an axis's direction holds the logo still on that
//     axis. Pushing with it does nothing.
//   - A corner hit before any input is silent. After input it plays the
//     coin pickup, including a miss of 4 pixels. A miss of 5 does not,
//     and the logo still only reverses when it actually meets a wall.
//   - Player 2's START launches a second logo that never overlaps the
//     first. Meeting it bounces both and plays the bump.
//
// It reads the game's variables from RAM, so the addresses below come
// from `nescript build --memory-map examples/dvd_screensaver.ne`.
//
// Usage: node dvd_screensaver_input.mjs

import { readFileSync } from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { createEmulator } from "./emu.mjs";

const here = path.dirname(fileURLToPath(import.meta.url));
const rom = readFileSync(path.join(here, "..", "..", "examples", "dvd_screensaver.nes"));

const BTN = { A: 0, START: 3, UP: 4, DOWN: 5, LEFT: 6, RIGHT: 7 };
const POS_X = 0x300;
const POS_Y = 0x302;
const RIGHT = 0x304;
const DOWN = 0x306;
const USED = 0x30a;
const TWO_LOGOS = 0x18;
// Logo 0 is 96×43 and logo 1 is 64×28. Both stay inside the 240×224
// picture.
const SIZE = [
  { w: 96, h: 43, rx: 144, ry: 181 },
  { w: 64, h: 28, rx: 176, ry: 196 },
];

let failures = 0;
function check(name, ok, detail = "") {
  console.log(`${ok ? "ok  " : "FAIL"} ${name}${ok ? "" : ` ${detail}`}`);
  if (!ok) failures++;
}

function boot() {
  const emu = createEmulator();
  emu.loadRom(rom);
  const get = (addr, n = 0) => emu.peek(addr + n);
  const logo = (n) => ({
    x: get(POS_X, n),
    y: get(POS_Y, n),
    right: get(RIGHT, n) === 1,
    down: get(DOWN, n) === 1,
  });
  // Audio samples written over `frames` frames, as a peak level.
  const peakOver = (frames, step) => {
    const before = emu.audioWav();
    for (let i = 0; i < frames; i++) step();
    const after = emu.audioWav();
    let peak = 0;
    for (let off = before.length; off < after.length; off += 2) {
      peak = Math.max(peak, Math.abs(after.readInt16LE(off)));
    }
    return peak;
  };
  return { emu, get, logo, peakOver };
}

function overlap(a, b) {
  const [sa, sb] = SIZE;
  return !(
    a.x >= b.x + sb.w ||
    b.x >= a.x + sa.w ||
    a.y >= b.y + sb.h ||
    b.y >= a.y + sa.h
  );
}

// The logo boots heading down and right, so up and left oppose it.
{
  const { emu, get, logo } = boot();
  emu.runFrames(20);
  check("boots heading down and right", logo(0).right && logo(0).down);

  let a = logo(0);
  emu.buttonDown(1, BTN.UP);
  emu.runFrames(20);
  emu.buttonUp(1, BTN.UP);
  let b = logo(0);
  check("up holds a down-right logo's y still", b.y === a.y && b.x > a.x, JSON.stringify({ a, b }));

  a = logo(0);
  emu.buttonDown(1, BTN.LEFT);
  emu.runFrames(20);
  emu.buttonUp(1, BTN.LEFT);
  b = logo(0);
  check("left holds a down-right logo's x still", b.x === a.x && b.y > a.y, JSON.stringify({ a, b }));

  a = logo(0);
  emu.buttonDown(1, BTN.UP);
  emu.buttonDown(1, BTN.LEFT);
  emu.runFrames(20);
  emu.buttonUp(1, BTN.UP);
  emu.buttonUp(1, BTN.LEFT);
  b = logo(0);
  check("up and left hold it still", b.x === a.x && b.y === a.y, JSON.stringify({ a, b }));

  emu.runFrames(2);
  a = logo(0);
  emu.buttonDown(1, BTN.DOWN);
  emu.buttonDown(1, BTN.RIGHT);
  emu.runFrames(20);
  emu.buttonUp(1, BTN.DOWN);
  emu.buttonUp(1, BTN.RIGHT);
  b = logo(0);
  check("down and right change nothing", b.x - a.x === 10 && b.y - a.y === 10, JSON.stringify({ a, b }));
  check("a press marks player 1 as having used the pad", get(USED, 0) === 1);
}

// A tap shorter than a step still counts, because presses are kept
// until the next step spends them.
{
  const { emu, logo } = boot();
  emu.runFrames(20);
  const a = logo(0);
  emu.buttonDown(1, BTN.UP);
  emu.runFrames(1);
  emu.buttonUp(1, BTN.UP);
  emu.runFrames(20);
  const b = logo(0);
  check("a one-frame tap costs one step on that axis", b.x - a.x - (b.y - a.y) === 1, JSON.stringify({ a, b }));
}

// Corners. The logo's first corner hit is the top-right one, 3528 steps
// in, which is about frame 7062 and needs no steering.
{
  const { emu, peakOver } = boot();
  emu.runFrames(2 * 3528 - 40);
  const peak = peakOver(80, () => emu.runFrames(1));
  check("a corner hit with no input is silent", peak === 0, `peak ${peak}`);
}
{
  const { emu, peakOver } = boot();
  emu.runFrames(10);
  emu.buttonDown(1, BTN.START);
  emu.runFrames(2);
  emu.buttonUp(1, BTN.START);
  // The press took twelve frames, so stop that much sooner.
  emu.runFrames(2 * 3528 - 40 - 12);
  const peak = peakOver(80, () => emu.runFrames(1));
  check("a corner hit after input plays the coin", peak > 200, `peak ${peak}`);
}

// From boot the logo heads down and right, and the bottom wall is
// further away than the right one. Holding left stalls x, one step at
// a time, until that difference is `gap`, so the right-wall hit lands
// `gap` pixels short of the corner. The press is released on the step
// that closes the gap, before the next frame can latch it again.
function steeredMiss(gap) {
  const { emu, logo, peakOver } = boot();
  emu.buttonDown(1, BTN.A);
  emu.runFrames(2);
  emu.buttonUp(1, BTN.A);
  const shortBy = (l) => SIZE[0].ry - l.y - (SIZE[0].rx - l.x);
  let guard = 0;
  while ((logo(0).x !== 72 || logo(0).y !== 92) && guard++ < 30) emu.runFrames(1);
  emu.buttonDown(1, BTN.LEFT);
  guard = 0;
  while (shortBy(logo(0)) > gap && guard++ < 80) emu.runFrames(1);
  emu.buttonUp(1, BTN.LEFT);
  let atWall = null;
  let yReversedEarly = false;
  const peak = peakOver(400, () => {
    const before = logo(0);
    emu.runFrames(1);
    const after = logo(0);
    if (!atWall && after.x === SIZE[0].rx && before.x !== SIZE[0].rx) {
      atWall = after;
      if (!after.down) yReversedEarly = true;
    }
  });
  return { atWall, yReversedEarly, peak };
}
{
  const miss4 = steeredMiss(4);
  check(
    "a 4px miss plays the coin",
    miss4.peak > 200 && miss4.atWall && miss4.atWall.y === SIZE[0].ry - 4,
    JSON.stringify(miss4.atWall) + ` peak ${miss4.peak}`,
  );
  check("a 4px miss does not reverse the short axis early", miss4.yReversedEarly === false);
}
{
  const miss5 = steeredMiss(5);
  check(
    "a 5px miss is silent",
    miss5.peak === 0 && miss5.atWall && miss5.atWall.y === SIZE[0].ry - 5,
    JSON.stringify(miss5.atWall) + ` peak ${miss5.peak}`,
  );
}

// Player 2.
{
  const { emu, get, logo } = boot();
  emu.runFrames(60);
  check("one logo until player 2 presses START", get(TWO_LOGOS) === 0);
  emu.buttonDown(2, BTN.START);
  emu.runFrames(2);
  emu.buttonUp(2, BTN.START);
  check("player 2's START launches the second logo", get(TWO_LOGOS) === 1);

  let overlaps = 0;
  let outOfRange = 0;
  let bumps = 0;
  let prev = [logo(0), logo(1)];
  const total = 60 * 60 * 4;
  for (let f = 0; f < total; f++) {
    emu.runFrames(1);
    const cur = [logo(0), logo(1)];
    if (overlap(cur[0], cur[1])) overlaps++;
    for (const n of [0, 1]) {
      if (cur[n].x > SIZE[n].rx || cur[n].y > SIZE[n].ry) outOfRange++;
      const wallX = cur[n].x === 0 || cur[n].x === SIZE[n].rx;
      const wallY = cur[n].y === 0 || cur[n].y === SIZE[n].ry;
      if ((cur[n].right !== prev[n].right && !wallX) || (cur[n].down !== prev[n].down && !wallY)) {
        bumps++;
      }
    }
    prev = cur;
  }
  check("the logos never overlap in four minutes", overlaps === 0, `${overlaps} frames`);
  check("neither logo leaves the picture", outOfRange === 0, `${outOfRange} frames`);
  check("the logos bounce off each other", bumps > 0, `${bumps} bounces`);
}

// The bump is audible, including the first one.
{
  const { emu, logo, peakOver } = boot();
  emu.runFrames(100);
  emu.buttonDown(2, BTN.START);
  emu.runFrames(2);
  emu.buttonUp(2, BTN.START);
  let prev = [logo(0), logo(1)];
  let found = false;
  for (let f = 0; f < 60 * 60 * 2 && !found; f++) {
    emu.runFrames(1);
    const cur = [logo(0), logo(1)];
    for (const n of [0, 1]) {
      const wallX = cur[n].x === 0 || cur[n].x === SIZE[n].rx;
      const wallY = cur[n].y === 0 || cur[n].y === SIZE[n].ry;
      if ((cur[n].right !== prev[n].right && !wallX) || (cur[n].down !== prev[n].down && !wallY)) {
        found = true;
      }
    }
    prev = cur;
  }
  const peak = peakOver(8, () => emu.runFrames(1));
  check("the first collision plays the bump", found && peak > 200, `peak ${peak}`);
}

if (failures) {
  console.error(`${failures} check(s) failed`);
  process.exit(1);
}
console.log("all checks passed");

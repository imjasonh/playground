// Run a ROM in jsnes with scripted input and save screenshots or video.
//
// Usage:
//     node capture.mjs ROM OUT_PREFIX PLAN
//
// PLAN is a list of steps separated by spaces:
//     run:N            advance N frames
//     hold:BUTTONS:N   hold buttons (letters from UDLRABST: up, down,
//                      left, right, A, B, select, start) for N frames
//     shot:NAME        save OUT_PREFIX-NAME.png
//     video:on / video:off   record frames to OUT_PREFIX.mp4 (ffmpeg)
//
// Run from tests/emulator so jsnes and pngjs resolve, or set
// NODE_PATH to that directory's node_modules.

import { spawn } from "node:child_process";
import { promises as fs } from "node:fs";
import { createRequire } from "node:module";
import path from "node:path";

const require = createRequire(path.resolve(process.cwd(), "package.json"));
const loaded = require("jsnes");
const jsnes = loaded.NES ? loaded : globalThis.jsnes;
const { PNG } = require("pngjs");

const [romPath, outPrefix, ...planArgs] = process.argv.slice(2);
const plan = planArgs.join(" ").split(/\s+/).filter(Boolean);

const W = 256;
const H = 240;
const frame = new Uint32Array(W * H);
const nes = new jsnes.NES({
  onFrame(buf) {
    for (let i = 0; i < W * H; i++) frame[i] = buf[i];
  },
  onAudioSample() {},
});
nes.loadROM((await fs.readFile(romPath)).toString("binary"));

const KEYS = {
  U: jsnes.Controller.BUTTON_UP,
  D: jsnes.Controller.BUTTON_DOWN,
  L: jsnes.Controller.BUTTON_LEFT,
  R: jsnes.Controller.BUTTON_RIGHT,
  A: jsnes.Controller.BUTTON_A,
  B: jsnes.Controller.BUTTON_B,
  S: jsnes.Controller.BUTTON_SELECT,
  T: jsnes.Controller.BUTTON_START,
};

function rgba() {
  const out = Buffer.alloc(W * H * 4);
  for (let i = 0; i < W * H; i++) {
    const p = frame[i];
    out[i * 4] = p & 0xff;
    out[i * 4 + 1] = (p >> 8) & 0xff;
    out[i * 4 + 2] = (p >> 16) & 0xff;
    out[i * 4 + 3] = 0xff;
  }
  return out;
}

let video = null;
function step() {
  nes.frame();
  if (video) video.stdin.write(rgba());
}

for (const item of plan) {
  const [op, a, b] = item.split(":");
  if (op === "run") {
    for (let i = 0; i < Number(a); i++) step();
  } else if (op === "hold") {
    for (const k of a) nes.buttonDown(1, KEYS[k]);
    for (let i = 0; i < Number(b); i++) step();
    for (const k of a) nes.buttonUp(1, KEYS[k]);
  } else if (op === "shot") {
    const png = new PNG({ width: W, height: H });
    rgba().copy(png.data);
    await fs.writeFile(`${outPrefix}-${a}.png`, PNG.sync.write(png));
  } else if (op === "video" && a === "on") {
    video = spawn("ffmpeg", [
      "-y", "-loglevel", "error", "-f", "rawvideo", "-pix_fmt", "rgba",
      "-s", `${W}x${H}`, "-r", "60", "-i", "-",
      "-vf", "scale=768:720:flags=neighbor", "-pix_fmt", "yuv420p",
      "-c:v", "libx264", "-crf", "18", `${outPrefix}.mp4`,
    ], { stdio: ["pipe", "inherit", "inherit"] });
  } else if (op === "video" && a === "off") {
    video.stdin.end();
    await new Promise((r) => video.on("close", r));
    video = null;
  } else {
    throw new Error(`unknown step ${item}`);
  }
}
if (video) {
  video.stdin.end();
  await new Promise((r) => video.on("close", r));
}

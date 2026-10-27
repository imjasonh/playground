// Render one frame of an MMC3 ROM as if the console had come out of
// reset with the mapper's bank-select register already set to PRG
// mode 1, and write it to a PNG.
//
// MMC3 hardwires only $E000-$FFFF to the last 8 KB PRG page.
// $C000-$DFFF is the second-to-last page while bit 6 of the
// bank-select register at $8000 is clear, and the switchable R6 page
// while it is set. That register has no defined power-on state, and a
// flash cart hands the game whatever its own loader left behind.
//
// jsnes, like most emulators, maps both halves of $C000-$FFFF to the
// last 16 KB at load time and so never shows the problem. This script
// overrides that mapping before the CPU fetches the reset vector,
// which is what the EverDrive report looks like from the inside.
//
// Usage:
//   node mmc3_power_on_shot.mjs <rom> <out.png> [frames] [r6-page]

import { createRequire } from "node:module";
import { readFileSync, writeFileSync } from "node:fs";

const require = createRequire(import.meta.url);
const loaded = require("jsnes");
const jsnes = loaded.NES ? loaded : globalThis.jsnes;
const { PNG } = require("pngjs");

const [romPath, outPath, frameArg, pageArg] = process.argv.slice(2);
if (!romPath || !outPath) {
  console.error("usage: node mmc3_power_on_shot.mjs <rom> <out.png> [frames] [r6-page]");
  process.exit(2);
}
const frames = Number(frameArg ?? 180);
const r6Page = Number(pageArg ?? 10);

const WIDTH = 256;
const HEIGHT = 240;
const PIXEL_COUNT = WIDTH * HEIGHT;

const pixels = new Uint32Array(PIXEL_COUNT).fill(0xff000000);
const nes = new jsnes.NES({
  onFrame(buf) {
    for (let i = 0; i < PIXEL_COUNT; i++) pixels[i] = 0xff000000 | buf[i];
  },
  onAudioSample() {},
});

nes.loadROM(readFileSync(romPath).toString("binary"));

// Power-on state the loader left: PRG mode 1, R6 = some other page.
// In mode 1 the CPU sees R6 at $C000-$DFFF, so a reset handler
// assembled at $C000 is not there when the vector is followed.
const mapper = nes.mmap;
mapper.prgAddressSelect = 1;
mapper.load8kRomBank(r6Page, 0xc000);
// Re-fetch the reset vector through the mapping above.
nes.cpu.requestIrq(nes.cpu.IRQ_RESET);

// Running into the wrong bank means executing data. jsnes throws on
// an illegal opcode where a real CPU would keep going; either way the
// game is gone, so record it and show whatever the PPU last painted.
let crash = null;
let ran = 0;
for (let i = 0; i < frames; i++) {
  try {
    nes.frame();
  } catch (err) {
    crash = `${err.message} on frame ${i + 1}`;
    break;
  }
  ran++;
}

const png = new PNG({ width: WIDTH, height: HEIGHT });
new Uint32Array(png.data.buffer, png.data.byteOffset, PIXEL_COUNT).set(pixels);
writeFileSync(outPath, PNG.sync.write(png));

const distinct = new Set(pixels).size;
console.log(
  `${romPath} -> ${outPath}: ${ran} frames, ${distinct} distinct colours` +
    (crash ? `, then ${crash}` : ""),
);

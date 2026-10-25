// Record a GIF of a .nes ROM running in jsnes.
//
// Usage:
//     node record_gif.mjs <rom-name> [frames] [stride] [output.gif] [warmup]
//
// Examples:
//     node record_gif.mjs platformer 360 2 docs/platformer.gif
//     node record_gif.mjs war 360 2 docs/war.gif 4
//     node record_gif.mjs pong 360 2 docs/pong.gif 4
//
// The recorder drives `harness.html` via puppeteer, collects one
// canvas frame every `stride` NES frames for `frames` total, and
// encodes the sequence as a paletted GIF via the `gifenc` library.
// At stride=2 we end up with a 30 fps GIF that maps 1:1 to every
// other NES frame (NES runs at ~60 fps), which is the right
// tradeoff between smoothness and file size for a README demo.
//
// `warmup` is the number of NES frames to advance before the first
// captured frame. The default of 30 skips past the reset stall and
// the platformer's auto-Title→Play handoff at frame 20; the war
// recording uses 4 instead because that demo opens on its menu and
// we want the title screen to be the gif's thumbnail.
//
// IMPORTANT: `docs/platformer.gif`, `docs/war.gif`, and
// `docs/pong.gif` are committed and embedded in the README. Any
// change to the compiler, the runtime, the harness, or the
// underlying `.ne` source that alters the gameplay you see in the
// first ~6 seconds of any of the three demos must be followed by
//
//     node tests/emulator/record_gif.mjs platformer 360 2 docs/platformer.gif
//     node tests/emulator/record_gif.mjs war        360 2 docs/war.gif        4
//     node tests/emulator/record_gif.mjs pong       360 2 docs/pong.gif       4
//
// committed alongside the source change. The CI `emulator` job
// regenerates both gifs and fails if the committed copies are stale —
// gifenc + jsnes are deterministic, so the freshly-rendered bytes
// byte-match a valid commit. See `.github/workflows/ci.yml`.

import { promises as fs } from "node:fs";
import path from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";
import puppeteer from "puppeteer";
import gifenc from "gifenc";
const { GIFEncoder, quantize, applyPalette } = gifenc;

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const repoRoot = path.resolve(__dirname, "..", "..");
const harnessUrl = pathToFileURL(path.join(__dirname, "harness.html")).toString();

const WIDTH = 256;
const HEIGHT = 240;

const romName = process.argv[2] ?? "platformer";
const totalFrames = parseInt(process.argv[3] ?? "360", 10);
const stride = parseInt(process.argv[4] ?? "2", 10); // captured every Nth NES frame
const outputPath = path.resolve(repoRoot, process.argv[5] ?? `docs/${romName}.gif`);

const romPath = path.join(repoRoot, "examples", `${romName}.nes`);
const romBytes = await fs.readFile(romPath);
const romB64 = romBytes.toString("base64");

const browser = await puppeteer.launch({
  headless: "new",
  args: [
    "--no-sandbox",
    "--disable-setuid-sandbox",
    "--allow-file-access-from-files",
  ],
});

const page = await browser.newPage();
page.on("pageerror", (e) => console.log("[pageerror]", e.message));
await page.goto(harnessUrl, { waitUntil: "load" });
await page.waitForFunction(
  "window.nesHarness && document.getElementById('info').textContent === 'ready'",
);

await page.evaluate((b) => window.nesHarness.loadRomBase64(b), romB64);

// Warm-up: skip past the reset stall and (optionally) any title
// screen so the first captured frame shows what we want as the
// gif's thumbnail. 30 frames at 60 fps covers ~0.5 s which is
// enough for the platformer example's Title → Playing auto-
// transition at frame 20. The war recording overrides this with
// `4` (positional arg below) so the title menu is the first frame.
// Positional arg wins; `WARMUP=…` env var is honoured for ad-hoc
// experimentation.
const warmupFrames = parseInt(
  process.argv[6] ?? process.env.WARMUP ?? "30",
  10,
);
await page.evaluate((n) => window.nesHarness.runFrames(n), warmupFrames);

console.log(
  `recording ${romName}.nes: ${totalFrames} frames, stride ${stride}, ` +
    `~${Math.round((totalFrames / 60) * 100) / 100}s of gameplay`,
);

const frames = [];
for (let i = 0; i < totalFrames; i += stride) {
  await page.evaluate((n) => window.nesHarness.runFrames(n), stride);
  const pixelsB64 = await page.evaluate(() => window.nesHarness.rawPixelsBase64());
  const rgba = Buffer.from(pixelsB64, "base64");
  // gifenc wants a Uint8Array or Uint8ClampedArray of RGBA pixels.
  frames.push(new Uint8Array(rgba));
  if (i % 20 === 0) process.stdout.write(".");
}
process.stdout.write("\n");
await browser.close();

// Encode. We quantize a representative middle frame to build a
// shared palette — this avoids the dithering / palette-drift
// artifacts you get with per-frame palettes and keeps the file
// size down. The NES only renders out of a fixed master palette
// anyway, so a single shared palette is the right answer.
console.log(`encoding ${frames.length} frames as GIF → ${path.relative(repoRoot, outputPath)}`);
const paletteSource = frames[Math.floor(frames.length / 2)];
const palette = quantize(paletteSource, 256, { format: "rgba4444" });

const gif = GIFEncoder();
for (let i = 0; i < frames.length; i++) {
  const indexed = applyPalette(frames[i], palette, "rgba4444");
  // delay is in milliseconds. stride NES frames at ~60 fps =
  // stride * 16.67 ms per captured frame.
  gif.writeFrame(indexed, WIDTH, HEIGHT, {
    palette,
    delay: Math.round((stride * 1000) / 60),
    transparent: false,
  });
}
gif.finish();

await fs.mkdir(path.dirname(outputPath), { recursive: true });
await fs.writeFile(outputPath, Buffer.from(gif.bytes()));
console.log(`wrote ${outputPath} (${(gif.bytes().length / 1024).toFixed(1)} KB)`);

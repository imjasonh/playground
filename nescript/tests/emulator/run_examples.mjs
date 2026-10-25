// End-to-end smoke test: runs every compiled `.nes` in `examples/`
// through a local `jsnes` (wrapped by `harness.html` in a
// puppeteer-driven headless Chrome), lets it render ~180 frames,
// grabs the raw canvas pixels, and diffs them byte-for-byte against
// a committed golden PNG under `goldens/`. It also hashes the
// audio samples jsnes produced during those frames and compares
// them against a committed `<name>.audio.hash` golden in the same
// directory — a one-line FNV-1a hash of the full int16 stereo
// buffer. Silent programs all hash to the same well-known value;
// audio-producing programs get a distinct hash that will trip as
// soon as the audio driver changes behavior.
//
// The goldens are the whole contract. Any change to the compiler
// (or any regression in jsnes, or any change to this harness that
// affects rendering or audio) will change at least one golden,
// and the diff will fail CI loudly. That's the point — it's the
// only way to catch "silently emits wrong code" bugs without
// writing a full-fat CPU test vector per example.
//
// Updating goldens:
//
//     UPDATE_GOLDENS=1 node run_examples.mjs
//     # or
//     node run_examples.mjs --update-goldens
//
// When a diff is legitimate, rerun with that flag. It rewrites the
// PNGs and audio hashes in `goldens/` from whatever the harness
// just produced. Then check the new files in git — `git diff
// goldens/` lets you eye each change, and the commit message is
// where you document why.
//
// When a diff is not legitimate, the runner writes:
//
//     actual/<name>.png       the actual pixels for this run
//     actual/<name>.diff.png  red-highlighted pixel diff vs. golden
//     actual/<name>.wav       the actual audio samples (stereo PCM)
//
// so you can upload them as CI artifacts or inspect locally. The
// `actual/` directory is gitignored. Video diffs write the PNG +
// diff PNG; audio diffs write the WAV so you can listen to what
// actually came out of the emulator.

import { promises as fs } from "node:fs";
import path from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";
import puppeteer from "puppeteer";
import { PNG } from "pngjs";

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const repoRoot = path.resolve(__dirname, "..", "..");
const examplesDir = path.join(repoRoot, "examples");
const goldensDir = path.join(__dirname, "goldens");
const actualDir = path.join(__dirname, "actual");
const harnessUrl = pathToFileURL(path.join(__dirname, "harness.html")).toString();

const WIDTH = 256;
const HEIGHT = 240;
const BYTES_PER_PIXEL = 4; // RGBA
const PIXEL_BYTES = WIDTH * HEIGHT * BYTES_PER_PIXEL;

const FRAMES_TO_RUN = 180; // ~3 seconds at 60 fps
const SCREENSHOT_FRAME = 180;

const updateGoldens =
  process.env.UPDATE_GOLDENS === "1" ||
  process.env.UPDATE_GOLDENS === "true" ||
  process.argv.includes("--update-goldens");

// ── PNG helpers ────────────────────────────────────────────────

// Decode a PNG file to a raw RGBA Buffer of length PIXEL_BYTES.
// Rejects if the file doesn't exist or has the wrong dimensions.
async function decodeGolden(filePath) {
  const bytes = await fs.readFile(filePath);
  const png = PNG.sync.read(bytes);
  if (png.width !== WIDTH || png.height !== HEIGHT) {
    throw new Error(
      `golden ${filePath} has wrong dimensions ${png.width}x${png.height}, expected ${WIDTH}x${HEIGHT}`,
    );
  }
  // `png.data` is already RGBA in top-left-first row-major order.
  return png.data;
}

// Encode a raw RGBA Buffer to a PNG file.
async function writePng(filePath, rgba) {
  if (rgba.length !== PIXEL_BYTES) {
    throw new Error(
      `writePng: expected ${PIXEL_BYTES} bytes, got ${rgba.length}`,
    );
  }
  const png = new PNG({ width: WIDTH, height: HEIGHT });
  rgba.copy(png.data);
  const buf = PNG.sync.write(png);
  await fs.writeFile(filePath, buf);
}

// Build a diff PNG: mismatching pixels in bright red, matching
// pixels in dim grayscale so you can still see the sprite silhouettes
// for context. First differing pixel is also returned for logs.
function buildDiff(expected, actual) {
  const out = Buffer.alloc(PIXEL_BYTES);
  let mismatched = 0;
  let firstDiff = null;
  for (let i = 0; i < PIXEL_BYTES; i += 4) {
    const eR = expected[i];
    const eG = expected[i + 1];
    const eB = expected[i + 2];
    const aR = actual[i];
    const aG = actual[i + 1];
    const aB = actual[i + 2];
    const same = eR === aR && eG === aG && eB === aB;
    if (same) {
      // Dim grayscale of the expected pixel — 25% brightness,
      // preserves the silhouette without competing with red.
      const gray = Math.round((eR * 0.299 + eG * 0.587 + eB * 0.114) * 0.25);
      out[i] = gray;
      out[i + 1] = gray;
      out[i + 2] = gray;
      out[i + 3] = 0xff;
    } else {
      mismatched++;
      if (firstDiff === null) {
        const px = (i / 4) | 0;
        firstDiff = {
          x: px % WIDTH,
          y: (px / WIDTH) | 0,
          expected: [eR, eG, eB],
          actual: [aR, aG, aB],
        };
      }
      out[i] = 0xff;
      out[i + 1] = 0x00;
      out[i + 2] = 0x00;
      out[i + 3] = 0xff;
    }
  }
  return { mismatched, firstDiff, rgba: out };
}

// ── File helpers ───────────────────────────────────────────────

// True if `filePath` exists and is readable. Used to decide
// whether a golden needs to be created (missing) vs diffed.
async function exists(filePath) {
  try {
    await fs.access(filePath);
    return true;
  } catch {
    return false;
  }
}

// Write an audio golden file. The format is a single line:
//
//     <hex-hash> <sample-count>
//
// chosen to be tiny (under 30 bytes per ROM), trivially diffable
// by git, and human-readable. The sample count is a sanity check
// — it catches the rare case where two runs produce differing
// sample counts but the same hash (practically zero probability
// with FNV-1a, but cheap insurance).
async function writeAudioGolden(filePath, audio) {
  await fs.writeFile(filePath, `${audio.hash} ${audio.samples}\n`);
}

// ── ROM discovery ──────────────────────────────────────────────

async function listRoms() {
  const entries = await fs.readdir(examplesDir);
  return entries
    .filter((f) => f.endsWith(".nes"))
    .sort()
    .map((f) => ({
      name: f.replace(/\.nes$/, ""),
      file: path.join(examplesDir, f),
    }));
}

// ── Harness driver ─────────────────────────────────────────────

async function runRomInHarness(page, rom) {
  const romBytes = await fs.readFile(rom.file);
  const romB64 = romBytes.toString("base64");

  let bootError = null;
  try {
    await page.evaluate((b64) => window.nesHarness.loadRomBase64(b64), romB64);
  } catch (err) {
    bootError = String(err);
    return { bootError, rgba: null, audio: null };
  }

  try {
    // Use runFrames — a single round-trip is much faster than
    // 180 separate `frame()` calls across puppeteer's RPC.
    await page.evaluate(
      (n) => window.nesHarness.runFrames(n),
      FRAMES_TO_RUN,
    );
  } catch (err) {
    return { bootError: String(err), rgba: null, audio: null };
  }
  // Frame count here is a no-op marker kept for readability.
  void SCREENSHOT_FRAME;

  const pixelsB64 = await page.evaluate(() => window.nesHarness.rawPixelsBase64());
  const rgba = Buffer.from(pixelsB64, "base64");
  if (rgba.length !== PIXEL_BYTES) {
    return {
      bootError: `harness returned ${rgba.length} pixel bytes, expected ${PIXEL_BYTES}`,
      rgba: null,
      audio: null,
    };
  }
  // Pull the audio hash (tiny — just a hex string + sample count).
  // The WAV bytes themselves are only fetched on diff failure to
  // keep the happy-path fast.
  const audio = await page.evaluate(() => window.nesHarness.audioHash());
  return { bootError: null, rgba, audio };
}

/// Read the full WAV bytes from the harness. Only called when an
/// audio diff fails — we don't want to pay the round-trip cost on
/// every ROM.
async function fetchAudioWav(page) {
  const wavB64 = await page.evaluate(() => window.nesHarness.audioWavBase64());
  return Buffer.from(wavB64, "base64");
}

// ── Main ───────────────────────────────────────────────────────

async function main() {
  await fs.mkdir(goldensDir, { recursive: true });
  // Wipe and recreate `actual/` so each run starts clean. This
  // directory is gitignored, so it only exists to give the CI job
  // something to upload when diffs fail.
  await fs.rm(actualDir, { recursive: true, force: true });
  await fs.mkdir(actualDir, { recursive: true });

  const roms = await listRoms();
  if (roms.length === 0) {
    console.error("no .nes files found in examples/ — build them first");
    process.exit(1);
  }

  const browser = await puppeteer.launch({
    headless: "new",
    args: ["--no-sandbox", "--disable-setuid-sandbox", "--allow-file-access-from-files"],
  });

  /** @type {Array<{name: string, status: string, reason: string | null}>} */
  const results = [];
  let failures = 0;

  try {
    for (const rom of roms) {
      const page = await browser.newPage();
      const consoleErrors = [];
      page.on("pageerror", (err) => consoleErrors.push(String(err)));
      page.on("console", (msg) => {
        if (msg.type() === "error") consoleErrors.push(msg.text());
      });

      await page.goto(harnessUrl, { waitUntil: "load" });
      await page.waitForFunction(
        "window.nesHarness && document.getElementById('info').textContent === 'ready'",
      );

      const { bootError, rgba, audio } = await runRomInHarness(page, rom);

      if (bootError || !rgba) {
        await page.close();
        failures++;
        const reason = `boot error: ${bootError ?? "no pixels"}`;
        results.push({ name: rom.name, status: "FAIL", reason });
        console.log(`FAIL  ${rom.name.padEnd(28)} ${reason}`);
        for (const e of consoleErrors) console.log("    console:", e);
        continue;
      }

      const goldenPngPath = path.join(goldensDir, `${rom.name}.png`);
      const goldenAudioPath = path.join(goldensDir, `${rom.name}.audio.hash`);

      const pngExists = await exists(goldenPngPath);
      const audioExists = await exists(goldenAudioPath);

      // ── Update mode ──────────────────────────────────────
      if (updateGoldens) {
        await writePng(goldenPngPath, rgba);
        await writeAudioGolden(goldenAudioPath, audio);
        results.push({ name: rom.name, status: "UPDATED", reason: null });
        console.log(
          `UPD   ${rom.name.padEnd(28)} wrote png + audio (hash=${audio.hash}, n=${audio.samples})`,
        );
        await page.close();
        continue;
      }

      // ── Missing goldens ─────────────────────────────────
      // We treat either missing PNG or missing audio hash as a
      // failure — both are part of the committed contract. The
      // user fixes both in one shot with UPDATE_GOLDENS=1.
      if (!pngExists || !audioExists) {
        failures++;
        await writePng(path.join(actualDir, `${rom.name}.png`), rgba);
        const wavBytes = await fetchAudioWav(page);
        await fs.writeFile(path.join(actualDir, `${rom.name}.wav`), wavBytes);
        const missing = [];
        if (!pngExists) missing.push("png");
        if (!audioExists) missing.push("audio");
        const reason = `missing golden(s): ${missing.join(", ")} — run with UPDATE_GOLDENS=1 to create`;
        results.push({ name: rom.name, status: "MISSING", reason });
        console.log(`MISS  ${rom.name.padEnd(28)} ${reason}`);
        await page.close();
        continue;
      }

      // ── PNG byte-for-byte diff ──────────────────────────
      let golden;
      try {
        golden = await decodeGolden(goldenPngPath);
      } catch (err) {
        await page.close();
        failures++;
        const reason = `failed to decode golden: ${err.message}`;
        results.push({ name: rom.name, status: "FAIL", reason });
        console.log(`FAIL  ${rom.name.padEnd(28)} ${reason}`);
        continue;
      }

      const pixelsMatch = rgba.equals(golden);

      // ── Audio hash diff ─────────────────────────────────
      const expectedAudio = (await fs.readFile(goldenAudioPath, "utf8")).trim();
      const actualAudioLine = `${audio.hash} ${audio.samples}`;
      const audioMatch = expectedAudio === actualAudioLine;

      if (pixelsMatch && audioMatch) {
        results.push({ name: rom.name, status: "OK", reason: null });
        console.log(`OK    ${rom.name.padEnd(28)} exact video + audio match`);
        await page.close();
        continue;
      }

      // Something mismatched — collect details for both diffs
      // and write the actual artifacts.
      const reasons = [];
      const actualPngPath = path.join(actualDir, `${rom.name}.png`);
      const actualWavPath = path.join(actualDir, `${rom.name}.wav`);
      if (!pixelsMatch) {
        const { mismatched, firstDiff, rgba: diffRgba } = buildDiff(golden, rgba);
        const diffPath = path.join(actualDir, `${rom.name}.diff.png`);
        await writePng(actualPngPath, rgba);
        await writePng(diffPath, diffRgba);
        reasons.push(
          `${mismatched}/${WIDTH * HEIGHT} px differ; first at ` +
            `(${firstDiff.x},${firstDiff.y}) expected [${firstDiff.expected.join(",")}] ` +
            `got [${firstDiff.actual.join(",")}]`,
        );
      }
      if (!audioMatch) {
        const wavBytes = await fetchAudioWav(page);
        await fs.writeFile(actualWavPath, wavBytes);
        reasons.push(`audio hash ${expectedAudio} -> ${actualAudioLine}`);
      }

      failures++;
      const reason = reasons.join("; ");
      results.push({ name: rom.name, status: "DIFF", reason });
      console.log(`DIFF  ${rom.name.padEnd(28)} ${reason}`);
      if (!pixelsMatch) {
        console.log(`        actual png:  ${path.relative(repoRoot, actualPngPath)}`);
        console.log(`        diff png:    ${path.relative(repoRoot, path.join(actualDir, `${rom.name}.diff.png`))}`);
      }
      if (!audioMatch) {
        console.log(`        actual wav:  ${path.relative(repoRoot, actualWavPath)}`);
      }
      await page.close();
    }
  } finally {
    await browser.close();
  }

  const reportPath = path.join(__dirname, "report.json");
  await fs.writeFile(
    reportPath,
    JSON.stringify({ generatedAt: new Date().toISOString(), updateGoldens, results }, null, 2),
  );

  console.log("");
  console.log(`report written to ${path.relative(repoRoot, reportPath)}`);
  if (updateGoldens) {
    console.log(`${results.length} goldens updated`);
    console.log("review the changes with `git diff tests/emulator/goldens/` before committing");
  } else {
    console.log(`${results.length - failures}/${results.length} ROMs match their goldens`);
    if (failures > 0) {
      console.log("rerun with UPDATE_GOLDENS=1 if the new output is intentional");
    }
  }

  if (failures > 0) process.exit(1);
}

main().catch((err) => {
  console.error(err);
  process.exit(1);
});

#!/usr/bin/env node
// Collect NYT crossword stats for the browser app.
//
// The puzzle list does not include solve time. Solve time is playTimeSeconds
// on the crossword state endpoint, 30 puzzles at a time. The per-puzzle
// v6 game URL returns 404 for these solves, so this script does not call it.
// A solved puzzle that already has a time is not requested again. An open
// puzzle is requested only when it is new or the list shows a change.
// Published JSON is written to the gh-pages branch (see the workflow),
// not to main.
//
// Usage: node scripts/scrape.js [dataDir]
//   NYT_COOKIE   NYT-S cookie value (required)
//   NYT_START    first print date (default 2014-01-01)
//   NYT_END      last print date (default today in America/New_York)
//   dataDir      defaults to $NYT_DATA_DIR or ./data

import { mkdir, readFile, writeFile } from "node:fs/promises";
import { dirname, join, resolve } from "node:path";
import { fileURLToPath } from "node:url";

import {
  DEFAULT_START,
  applyPlayTime,
  chunksNeedingList,
  cookieHeader,
  cookieValue,
  dateChunks,
  gameDataOf,
  idBatches,
  isFinished,
  isIsoDate,
  listUrl,
  mergeListed,
  normalizeDoc,
  puzzlesEqual,
  serializeStats,
  stateUrl,
  todayInNewYork,
} from "../src/scrape-lib.js";

const __dirname = dirname(fileURLToPath(import.meta.url));
const APP_DIR = resolve(__dirname, "..");
const UA = "nyt-crossword (github.com/imjasonh/playground)";
// Node's HTTP client can throw assert(!this.paused) off the request promise
// when a socket ends early. That must not abort the rest of the run.
const INTERVAL_MS = 100;

function isParserCrash(err) {
  return Boolean(err && err.code === "ERR_ASSERTION" && String(err.message).includes("paused"));
}

process.on("uncaughtException", (err) => {
  if (isParserCrash(err)) {
    console.error("HTTP parser glitch; continuing with the other game requests.");
    return;
  }
  console.error(err && err.stack ? err.stack : err);
  process.exit(1);
});

function withTimeout(promise, ms) {
  return new Promise((resolve, reject) => {
    const timer = setTimeout(() => {
      reject(new Error(`Timed out after ${ms}ms`));
    }, ms);
    promise.then(
      (value) => {
        clearTimeout(timer);
        resolve(value);
      },
      (err) => {
        clearTimeout(timer);
        reject(err);
      },
    );
  });
}

function requireDate(value, label) {
  if (!isIsoDate(value)) {
    throw new Error(`${label} must be YYYY-MM-DD, got ${value || "(empty)"}`);
  }
  return value;
}

function sleep(ms) {
  return new Promise((resolvePromise) => {
    setTimeout(resolvePromise, ms);
  });
}

function createPacer(intervalMs) {
  let next = 0;
  return async function pace() {
    const now = Date.now();
    const at = Math.max(now, next);
    next = at + intervalMs;
    const wait = at - now;
    if (wait > 0) await sleep(wait);
  };
}

const pace = createPacer(INTERVAL_MS);

async function fetchJson(url) {
  let lastStatus = 0;
  for (let attempt = 1; attempt <= 5; attempt += 1) {
    await pace();
    // Do not abort the socket. Aborting while the parser is paused is what
    // crashed the first run. Connection: close keeps one game's 404 off the
    // next game's connection. The body is read before we start another.
    const response = await withTimeout(
      fetch(url, {
        headers: {
          Accept: "application/json",
          Connection: "close",
          Cookie: cookieHeader(process.env.NYT_COOKIE),
          "User-Agent": UA,
        },
      }),
      30000,
    );
    const text = await withTimeout(response.text(), 30000);
    if (response.status === 401 || response.status === 403) {
      throw new Error(
        `NYT rejected NYT_COOKIE (HTTP ${response.status}). Update the Actions secret.`,
      );
    }
    if (response.ok) {
      try {
        return JSON.parse(text);
      } catch (err) {
        throw new Error(`Bad JSON for ${url.pathname}`, { cause: err });
      }
    }
    if (response.status !== 429 && response.status < 500) {
      const snippet = text.replace(/\s+/g, " ").trim().slice(0, 180);
      throw new Error(`HTTP ${response.status} for ${url.pathname}${snippet ? `: ${snippet}` : ""}`);
    }
    lastStatus = response.status;
    await sleep(500 * attempt * attempt);
  }
  throw new Error(`HTTP ${lastStatus} for ${url.pathname}`);
}

async function readPrevious(path) {
  try {
    const raw = await readFile(path, "utf8");
    return { doc: normalizeDoc(JSON.parse(raw)), raw };
  } catch (err) {
    if (err && err.code === "ENOENT") return { doc: normalizeDoc(null), raw: "" };
    throw err;
  }
}

async function main() {
  const cookie = cookieValue(process.env.NYT_COOKIE);
  if (!cookie) {
    console.error("NYT_COOKIE is empty. Add the NYT-S cookie as the NYT_COOKIE Actions secret.");
    process.exitCode = 1;
    return;
  }
  const start = requireDate(process.env.NYT_START || DEFAULT_START, "NYT_START");
  const end = requireDate(process.env.NYT_END || todayInNewYork(), "NYT_END");
  if (start > end) throw new Error(`NYT_START ${start} is after NYT_END ${end}`);

  const dataDir = resolve(process.argv[2] || process.env.NYT_DATA_DIR || join(APP_DIR, "data"));
  const outPath = join(dataDir, "stats.json");
  const { doc: previous, raw } = await readPrevious(outPath);

  const listed = [];
  const allChunks = dateChunks(start, end);
  const chunks = chunksNeedingList(allChunks, previous.puzzles);
  const skippedChunks = allChunks.length - chunks.length;
  console.log(
    `Listing puzzles ${start} through ${end} (${chunks.length} requests, ${skippedChunks} solved windows skipped)`,
  );
  for (const [chunkStart, chunkEnd] of chunks) {
    const body = await fetchJson(listUrl(chunkStart, chunkEnd));
    const results = body && Array.isArray(body.results) ? body.results : [];
    listed.push(...results);
    console.log(`  ${chunkStart}..${chunkEnd}: ${results.length}`);
  }
  const inRange = previous.puzzles.some((puzzle) => puzzle.date >= start && puzzle.date <= end);
  if (chunks.length > 0 && listed.length === 0 && inRange) {
    throw new Error("NYT returned no puzzles. Leaving the published file unchanged.");
  }

  const { puzzles, fetchList } = mergeListed(previous.puzzles, listed, { start, end }, chunks);
  const pending = fetchList.filter((puzzle) => !isFinished(puzzle));
  const storedSolved = puzzles.filter(
    (puzzle) => puzzle.date >= start && puzzle.date <= end && isFinished(puzzle),
  ).length;
  console.log(`Not requesting ${storedSolved} solved puzzles that already have a time`);
  const batches = idBatches(pending.map((puzzle) => puzzle.id));
  const byId = new Map(pending.map((puzzle) => [puzzle.id, puzzle]));
  console.log(`Fetching solve times for ${pending.length} puzzles (${batches.length} requests)`);
  let failed = 0;
  const timedIds = new Set();
  for (let index = 0; index < batches.length; index += 1) {
    const ids = batches[index];
    try {
      const body = await fetchJson(stateUrl(ids));
      const states = body && Array.isArray(body.states) ? body.states : null;
      if (!states) throw new Error(`State response had no states array for ${ids.length} puzzles`);
      for (const state of states) {
        const id = Number(state && state.puzzle_id);
        const puzzle = byId.get(id);
        const data = gameDataOf(state);
        if (!puzzle || !data) continue;
        Object.assign(puzzle, applyPlayTime(puzzle, data));
        if (puzzle.seconds > 0) timedIds.add(puzzle.id);
      }
    } catch (err) {
      failed += 1;
      console.error(`State batch ${index + 1}/${batches.length}: ${err.message}`);
    }
    if ((index + 1) % 10 === 0 || index + 1 === batches.length) {
      console.log(`  states ${index + 1}/${batches.length}`);
    }
  }

  const timed = timedIds.size;
  const solvedAsked = pending.filter((puzzle) => puzzle.solved === true).length;
  if (solvedAsked > 0 && timed === 0) {
    console.error(`No solve times for ${solvedAsked} solved puzzles.`);
    process.exitCode = 1;
  }

  const generatedAt = puzzlesEqual(previous.puzzles, puzzles)
    ? previous.generatedAt
    : new Date().toISOString();
  const text = serializeStats({ generatedAt, puzzles });
  if (text === raw) {
    console.log("No puzzle changes.");
    return;
  }
  await mkdir(dataDir, { recursive: true });
  await writeFile(outPath, text);
  const solved = puzzles.filter((puzzle) => puzzle.solved && puzzle.seconds > 0).length;
  const partial = puzzles.filter((puzzle) => !puzzle.solved && puzzle.percentFilled > 0).length;
  console.log(
    `Wrote ${outPath}: ${solved} solved, ${partial} partial, ${timed} new times, ${failed} state errors`,
  );
}

main().catch((err) => {
  console.error(err.message || err);
  process.exitCode = 1;
});

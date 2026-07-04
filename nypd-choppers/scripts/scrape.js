#!/usr/bin/env node
// Hourly scraper for the NYPD helicopter tracker.
//
// Queries a public ADS-B aggregator (adsb.lol, with fallbacks) for the current
// position of every aircraft in the NYPD Aviation Unit fleet and appends the
// airborne snapshots to per-day JSON files. Run from GitHub Actions on a
// schedule; the resulting files are published alongside the app so the browser
// can render daily flight paths and estimates without hitting any API itself
// (which is blocked by CORS and only exposes live, not historical, data).
//
// Usage: node scripts/scrape.js [dataDir]
//   dataDir defaults to $NYPD_DATA_DIR or ./data (relative to this app).

import { mkdir, readFile, writeFile } from "node:fs/promises";
import { existsSync } from "node:fs";
import { dirname, join, resolve } from "node:path";
import { fileURLToPath } from "node:url";

import { FLEET_HEXES } from "../src/fleet.js";
import {
  buildSnapshot,
  localDateString,
  mergeDay,
  updateIndex,
} from "../src/scrape-lib.js";

const __dirname = dirname(fileURLToPath(import.meta.url));
const APP_DIR = resolve(__dirname, "..");

// ADS-B aggregators exposing an ADSBExchange-compatible /v2/hex/ endpoint.
const ENDPOINTS = [
  (hexes) => `https://api.adsb.lol/v2/hex/${hexes}`,
  (hexes) => `https://opendata.adsb.fi/api/v2/hex/${hexes}`,
  (hexes) => `https://api.airplanes.live/v2/hex/${hexes}`,
];

async function fetchSnapshot() {
  let lastError = null;
  for (const build of ENDPOINTS) {
    const url = build(FLEET_HEXES);
    try {
      const res = await fetch(url, {
        headers: { "User-Agent": "nypd-choppers-tracker (github playground)" },
        signal: AbortSignal.timeout(30000),
      });
      if (!res.ok) throw new Error(`HTTP ${res.status} from ${url}`);
      const body = await res.json();
      console.log(`Fetched ${body?.ac?.length ?? 0} aircraft from ${url}`);
      return buildSnapshot(body);
    } catch (err) {
      lastError = err;
      console.warn(`Fetch failed for ${url}: ${err.message}`);
    }
  }
  throw new Error(`All ADS-B endpoints failed: ${lastError?.message}`);
}

async function readJson(path) {
  if (!existsSync(path)) return null;
  try {
    return JSON.parse(await readFile(path, "utf8"));
  } catch (err) {
    console.warn(`Could not parse ${path}: ${err.message}`);
    return null;
  }
}

async function main() {
  const dataDir = resolve(
    process.argv[2] || process.env.NYPD_DATA_DIR || join(APP_DIR, "data"),
  );
  await mkdir(dataDir, { recursive: true });

  const snapshot = await fetchSnapshot();
  const nowMs = snapshot.t * 1000;
  const date = localDateString(nowMs);

  const airborneOrTracked = snapshot.samples; // store all tracked; analysis filters
  console.log(
    `Snapshot @ ${new Date(nowMs).toISOString()} (${date} NY): ` +
      `${airborneOrTracked.length} positioned aircraft`,
  );

  const dayPath = join(dataDir, `${date}.json`);
  const indexPath = join(dataDir, "index.json");

  const existingDay = await readJson(dayPath);
  const { day, added } = mergeDay(existingDay, airborneOrTracked, date);

  if (added === 0) {
    // Nothing new to record (no fleet aircraft tracked this run). Leave the
    // published files untouched so the hourly job produces no empty commits.
    console.log(`No new samples for ${date}; leaving data files unchanged.`);
    return;
  }

  await writeFile(dayPath, JSON.stringify(day) + "\n");

  const existingIndex = await readJson(indexPath);
  const index = updateIndex(existingIndex, date, day.samples.length);
  await writeFile(indexPath, JSON.stringify(index, null, 2) + "\n");

  console.log(
    `Wrote ${dayPath}: +${added} new sample(s), ${day.samples.length} total for ${date}.`,
  );
}

main().catch((err) => {
  console.error(err);
  process.exit(1);
});

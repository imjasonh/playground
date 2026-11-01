#!/usr/bin/env node
// Data collector for the NYPD helicopter tracker.
//
// Free ADS-B APIs can't be called from the browser (CORS) and their live
// endpoints only return an aircraft's *current* position — far too sparse to
// reconstruct flight paths or airborne time. Instead we fetch each fleet
// aircraft's full-day **trace** (readsb/tar1090 format), which holds the whole
// UTC day's positions at ~30s resolution. Running this hourly and merging
// (de-duplicated) accumulates the complete day even though each file only
// covers the current UTC day and GitHub's scheduler is best-effort.
//
// The live /v2/hex snapshot is kept as a graceful fallback so a run still
// records *something* if trace hosts are unavailable.
//
// Usage: node scripts/scrape.js [dataDir]
//   dataDir defaults to $NYPD_DATA_DIR or ./data (relative to this app).

import { mkdir, readFile, writeFile } from "node:fs/promises";
import { existsSync } from "node:fs";
import { gunzipSync } from "node:zlib";
import { dirname, join, resolve } from "node:path";
import { fileURLToPath } from "node:url";

import { FLEET, FLEET_HEXES } from "../src/fleet.js";
import { parseTrace, traceFullPath } from "../src/trace.js";
import {
  buildSnapshot,
  groupByLocalDate,
  mergeDay,
  updateIndex,
} from "../src/scrape-lib.js";

const __dirname = dirname(fileURLToPath(import.meta.url));
const APP_DIR = resolve(__dirname, "..");

// Hosts that serve readsb full-day trace files at /data/traces/<xx>/... .
const TRACE_HOSTS = (
  process.env.NYPD_TRACE_HOSTS ||
  "https://globe.adsb.lol,https://adsb.lol,https://globe.airplanes.live"
)
  .split(",")
  .map((h) => h.trim().replace(/\/$/, ""))
  .filter(Boolean);

// Live snapshot endpoints (ADSBExchange-compatible), used only as a fallback.
const SNAPSHOT_ENDPOINTS = [
  (hexes) => `https://api.adsb.lol/v2/hex/${hexes}`,
  (hexes) => `https://opendata.adsb.fi/api/v2/hex/${hexes}`,
  (hexes) => `https://api.airplanes.live/v2/hex/${hexes}`,
];

const UA = "nypd-choppers-tracker (github playground)";

async function fetchJsonMaybeGzip(url) {
  const res = await fetch(url, {
    headers: { "User-Agent": UA, Accept: "application/json" },
    signal: AbortSignal.timeout(30000),
  });
  if (res.status === 404) return { notFound: true };
  if (!res.ok) throw new Error(`HTTP ${res.status}`);
  const buf = Buffer.from(await res.arrayBuffer());
  // fetch() transparently decodes Content-Encoding: gzip; but some hosts serve
  // the pre-gzipped file as an opaque body, so gunzip on parse failure.
  try {
    return { data: JSON.parse(buf.toString("utf8")) };
  } catch {
    return { data: JSON.parse(gunzipSync(buf).toString("utf8")) };
  }
}

// Fetch every fleet aircraft's full-day trace. Returns {samples, host} or null
// if no host served any usable trace.
async function collectTraces() {
  for (const host of TRACE_HOSTS) {
    const samples = [];
    let ok = 0;
    let hostReachable = false;
    for (const ac of FLEET) {
      const url = `${host}/${traceFullPath(ac.hex)}`;
      try {
        const { data, notFound } = await fetchJsonMaybeGzip(url);
        hostReachable = true;
        if (notFound) continue; // aircraft simply hasn't flown recently
        const parsed = parseTrace(data);
        samples.push(...parsed);
        if (parsed.length) ok += 1;
      } catch (err) {
        console.warn(`Trace fetch failed for ${ac.tail} at ${host}: ${err.message}`);
      }
    }
    if (hostReachable) {
      console.log(`Trace host ${host}: ${ok} aircraft with data, ${samples.length} points.`);
      return { samples, host };
    }
  }
  return null;
}

async function fetchSnapshot() {
  let lastError = null;
  for (const build of SNAPSHOT_ENDPOINTS) {
    const url = build(FLEET_HEXES);
    try {
      const res = await fetch(url, {
        headers: { "User-Agent": UA },
        signal: AbortSignal.timeout(30000),
      });
      if (!res.ok) throw new Error(`HTTP ${res.status}`);
      const body = await res.json();
      console.log(`Snapshot fallback: ${body?.ac?.length ?? 0} aircraft from ${url}`);
      return buildSnapshot(body).samples;
    } catch (err) {
      lastError = err;
      console.warn(`Snapshot fetch failed for ${url}: ${err.message}`);
    }
  }
  throw new Error(`All snapshot endpoints failed: ${lastError?.message}`);
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

  let samples;
  const traces = await collectTraces();
  if (traces && traces.samples.length) {
    samples = traces.samples;
    console.log(`Using ${samples.length} trace points from ${traces.host}.`);
  } else {
    console.log("No trace data available; falling back to live snapshot.");
    samples = await fetchSnapshot();
  }

  if (!samples.length) {
    console.log("No positions collected this run; nothing to write.");
    return;
  }

  // Route points to their New York calendar date; a full UTC-day trace can
  // straddle two local dates.
  const byDate = groupByLocalDate(samples);
  const indexPath = join(dataDir, "index.json");
  let index = await readJson(indexPath);
  let totalAdded = 0;

  for (const [date, daySamples] of byDate) {
    const dayPath = join(dataDir, `${date}.json`);
    const existing = await readJson(dayPath);
    const { day, added } = mergeDay(existing, daySamples, date);
    if (added === 0) {
      console.log(`${date}: no new points.`);
      continue;
    }
    await writeFile(dayPath, JSON.stringify(day) + "\n");
    index = updateIndex(index, date, day.samples.length);
    totalAdded += added;
    console.log(`${date}: +${added} new point(s), ${day.samples.length} total.`);
  }

  if (totalAdded > 0) {
    await writeFile(indexPath, JSON.stringify(index, null, 2) + "\n");
    console.log(`Updated ${indexPath} across ${byDate.size} date(s).`);
  } else {
    console.log("No new points across any date; data files unchanged.");
  }
}

main().catch((err) => {
  console.error(err);
  process.exit(1);
});

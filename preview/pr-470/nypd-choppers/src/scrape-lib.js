// Pure helpers for turning an adsb.lol API response into stored samples and
// merging them into per-day data files. Kept free of network and filesystem
// access so the transformation logic can be unit-tested.

// adsb.lol / ADSBExchange-compatible aircraft record -> our compact sample.
// Returns null when the record has no usable position.
export function normalizeAircraft(ac, nowSec) {
  if (!ac || typeof ac !== "object") return null;
  const lat = num(ac.lat);
  const lon = num(ac.lon);
  if (lat == null || lon == null) return null;

  const ground = ac.alt_baro === "ground";
  const alt = typeof ac.alt_baro === "number" ? ac.alt_baro : null;
  const seenPos = num(ac.seen_pos);
  const t = Math.round(nowSec - (seenPos != null ? seenPos : 0));

  return {
    hex: String(ac.hex || "").toUpperCase(),
    r: ac.r ? String(ac.r).trim() : null,
    flight: ac.flight ? String(ac.flight).trim() : null,
    t,
    lat,
    lon,
    alt,
    gs: num(ac.gs),
    track: num(ac.track),
    ground,
  };
}

// Build a snapshot {t, samples[]} from a raw adsb.lol response body.
export function buildSnapshot(body, fallbackNowMs = Date.now()) {
  const nowMs = typeof body?.now === "number" ? body.now : fallbackNowMs;
  const nowSec = Math.round(nowMs / 1000);
  const ac = Array.isArray(body?.ac) ? body.ac : [];
  const samples = ac
    .map((a) => normalizeAircraft(a, nowSec))
    .filter((s) => s !== null);
  return { t: nowSec, samples };
}

// Group samples by their local calendar date (default US Eastern). A single
// full-day UTC trace can straddle two New York dates, so route each point to
// the day it belongs to. Returns a Map of "YYYY-MM-DD" -> samples[].
export function groupByLocalDate(samples, timeZone = "America/New_York") {
  const byDate = new Map();
  for (const s of samples) {
    const date = localDateString(s.t * 1000, timeZone);
    if (!byDate.has(date)) byDate.set(date, []);
    byDate.get(date).push(s);
  }
  return byDate;
}

// "YYYY-MM-DD" for the given epoch-ms in a timezone (default US Eastern).
export function localDateString(ms, timeZone = "America/New_York") {
  // en-CA formats as YYYY-MM-DD.
  return new Intl.DateTimeFormat("en-CA", {
    timeZone,
    year: "numeric",
    month: "2-digit",
    day: "2-digit",
  }).format(new Date(ms));
}

// Merge new samples into an existing day file object, de-duplicating on
// hex+timestamp and keeping samples sorted by time.
export function mergeDay(existing, newSamples, date, timeZone = "America/New_York") {
  const base =
    existing && Array.isArray(existing.samples)
      ? existing
      : { date, tz: timeZone, samples: [] };
  const seen = new Set(base.samples.map((s) => `${s.hex}|${s.t}`));
  const merged = base.samples.slice();
  let added = 0;
  for (const s of newSamples) {
    const key = `${s.hex}|${s.t}`;
    if (seen.has(key)) continue;
    seen.add(key);
    merged.push(s);
    added += 1;
  }
  merged.sort((a, b) => a.t - b.t || a.hex.localeCompare(b.hex));
  return {
    day: { date, tz: timeZone, updated: Math.round(Date.now() / 1000), samples: merged },
    added,
  };
}

// Update the index of available days.
export function updateIndex(existing, date, sampleCount) {
  const base =
    existing && Array.isArray(existing.days)
      ? existing
      : { generator: "nypd-choppers scraper", days: [] };
  const days = base.days.filter((d) => d.date !== date);
  days.push({ date, samples: sampleCount });
  days.sort((a, b) => a.date.localeCompare(b.date));
  return {
    generator: base.generator || "nypd-choppers scraper",
    updated: Math.round(Date.now() / 1000),
    days,
  };
}

function num(v) {
  return typeof v === "number" && Number.isFinite(v) ? v : null;
}

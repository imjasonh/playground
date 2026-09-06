// Parse a readsb / tar1090 "trace" file into our compact sample format.
//
// Unlike the live /v2/hex snapshot (which is only the current position), a
// trace file holds an aircraft's *entire day* of positions at high resolution
// (a new point at least every ~30s while airborne, plus on maneuvers). adsb.lol
// serves these publicly to render an aircraft's history, so scraping the
// full-day trace gives dense flight paths and never misses a flight.
//
// Format (see wiedehopf/readsb README-json.md, "trace jsons"):
//   { icao, r, t, timestamp, trace: [ [ offsetSec, lat, lon,
//       alt("ground"|ft|null), gs, track, flags, vertRate, details|null,
//       type, geomAlt, ... ], ... ] }
// Each entry's absolute time is `timestamp + offsetSec`. `flags` is a bitfield;
// bit 1 = stale position, bit 2 = start of a new leg (takeoff/landing split).

const FLAG_STALE = 1;
const FLAG_NEW_LEG = 2;

/**
 * Convert a parsed trace JSON object into an array of samples.
 * @param {object} trace readsb trace file contents
 * @returns {Array} samples: {hex,r,flight,t,lat,lon,alt,gs,track,ground,leg}
 */
export function parseTrace(trace) {
  if (!trace || !Array.isArray(trace.trace)) return [];
  const base = Number(trace.timestamp);
  if (!Number.isFinite(base)) return [];

  const hex = String(trace.icao || trace.hex || "").toUpperCase();
  const reg = trace.r ? String(trace.r).trim() : null;

  const samples = [];
  for (const entry of trace.trace) {
    if (!Array.isArray(entry) || entry.length < 3) continue;
    const lat = num(entry[1]);
    const lon = num(entry[2]);
    if (lat == null || lon == null) continue;

    const altRaw = entry[3];
    const ground = altRaw === "ground";
    const alt = typeof altRaw === "number" ? altRaw : null;
    const flags = Number.isFinite(entry[6]) ? entry[6] : 0;
    const details = entry[8] && typeof entry[8] === "object" ? entry[8] : null;

    samples.push({
      hex,
      r: reg || (details && details.r ? String(details.r).trim() : null),
      flight: details && details.flight ? String(details.flight).trim() : null,
      t: Math.round(base + Number(entry[0] || 0)),
      lat,
      lon,
      alt,
      gs: num(entry[4]),
      track: num(entry[5]),
      ground,
      leg: (flags & FLAG_NEW_LEG) > 0,
    });
  }
  return samples;
}

/** Last two lowercase hex characters — the trace file's shard directory. */
export function traceShard(hex) {
  const h = String(hex || "").toLowerCase();
  return h.slice(-2);
}

/** Path segment for an aircraft's full-day trace, relative to a trace host. */
export function traceFullPath(hex) {
  const h = String(hex || "").toLowerCase();
  return `data/traces/${traceShard(h)}/trace_full_${h}.json`;
}

export { FLAG_STALE, FLAG_NEW_LEG };

function num(v) {
  return typeof v === "number" && Number.isFinite(v) ? v : null;
}

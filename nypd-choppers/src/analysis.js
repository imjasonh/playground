// Pure, DOM-free analysis of scraped ADS-B samples.
//
// The scraper records at most one position sample per aircraft per hourly run,
// and only when the aircraft is airborne and being tracked. From those sparse
// samples we reconstruct approximate flights and estimate, per day:
//   - how long each helicopter was airborne,
//   - the ground track it flew,
//   - how much Jet-A it likely burned, and
//   - what that fuel cost.
//
// Everything here is an ESTIMATE derived from ~hourly sampling. See
// estimateFlightSeconds() for the (transparent) time model.

export const DEFAULTS = {
  // A helicopter is "airborne" above this barometric altitude (feet)...
  minAltFt: 200,
  // ...or, when altitude is unavailable, above this ground speed (knots).
  minGroundSpeedKt: 30,
  // Consecutive airborne samples farther apart than this (seconds) are treated
  // as separate flights rather than one continuous track.
  maxFlightGapSec: 5400, // 90 minutes
  // Nominal spacing between scrapes (seconds). Each airborne detection is
  // credited with roughly this much flight time (see estimateFlightSeconds).
  sampleIntervalSec: 3600, // 1 hour
  // Jet-A price used when the caller does not override it (US$/gallon).
  pricePerGallon: 6.5,
};

const EARTH_RADIUS_KM = 6371;
const KM_PER_MILE = 1.609344;

/** Great-circle distance between two {lat, lon} points, in kilometres. */
export function haversineKm(a, b) {
  if (!a || !b) return 0;
  const toRad = (d) => (d * Math.PI) / 180;
  const dLat = toRad(b.lat - a.lat);
  const dLon = toRad(b.lon - a.lon);
  const lat1 = toRad(a.lat);
  const lat2 = toRad(b.lat);
  const h =
    Math.sin(dLat / 2) ** 2 +
    Math.cos(lat1) * Math.cos(lat2) * Math.sin(dLon / 2) ** 2;
  return 2 * EARTH_RADIUS_KM * Math.asin(Math.min(1, Math.sqrt(h)));
}

export function kmToMiles(km) {
  return km / KM_PER_MILE;
}

/** Was the aircraft flying (as opposed to parked/taxiing) in this sample? */
export function isAirborne(sample, opts = {}) {
  const { minAltFt, minGroundSpeedKt } = { ...DEFAULTS, ...opts };
  if (!sample || sample.lat == null || sample.lon == null) return false;
  if (sample.ground) return false;
  if (sample.alt != null) return sample.alt >= minAltFt;
  if (sample.gs != null) return sample.gs >= minGroundSpeedKt;
  // Position present, no altitude/speed hint: assume tracked because airborne.
  return true;
}

/**
 * Estimated airborne seconds for a single flight.
 *
 * With ~hourly sampling, a flight's true duration is unknown; we credit the
 * observed span plus one sampling interval, so a flight seen once (span 0) is
 * credited ~one interval and a flight seen over N evenly spaced samples is
 * credited ~N intervals. This intentionally avoids under-counting short
 * flights that happen to be caught by a single scrape.
 */
export function estimateFlightSeconds(spanSeconds, opts = {}) {
  const { sampleIntervalSec } = { ...DEFAULTS, ...opts };
  return Math.max(0, spanSeconds) + sampleIntervalSec;
}

/**
 * Split one aircraft's samples into approximate flights.
 * @returns {Array<{startT,endT,spanSeconds,estimatedSeconds,distanceKm,points}>}
 */
export function segmentFlights(samples, opts = {}) {
  const cfg = { ...DEFAULTS, ...opts };
  const airborne = (samples || [])
    .filter((s) => isAirborne(s, cfg))
    .slice()
    .sort((a, b) => a.t - b.t);

  const flights = [];
  let current = null;
  for (const s of airborne) {
    if (current && s.t - current.points[current.points.length - 1].t > cfg.maxFlightGapSec) {
      flights.push(finalizeFlight(current, cfg));
      current = null;
    }
    if (!current) current = { points: [] };
    current.points.push(s);
  }
  if (current) flights.push(finalizeFlight(current, cfg));
  return flights;
}

function finalizeFlight(flight, cfg) {
  const points = flight.points;
  const startT = points[0].t;
  const endT = points[points.length - 1].t;
  const spanSeconds = endT - startT;
  let distanceKm = 0;
  for (let i = 1; i < points.length; i++) {
    distanceKm += haversineKm(points[i - 1], points[i]);
  }
  return {
    startT,
    endT,
    spanSeconds,
    estimatedSeconds: estimateFlightSeconds(spanSeconds, cfg),
    distanceKm,
    sampleCount: points.length,
    points,
  };
}

/** Analyse one aircraft's samples into flights plus rolled-up estimates. */
export function analyzeAircraft(member, samples, opts = {}) {
  const cfg = { ...DEFAULTS, ...opts };
  const flights = segmentFlights(samples, cfg);
  const estimatedSeconds = flights.reduce((s, f) => s + f.estimatedSeconds, 0);
  const distanceKm = flights.reduce((s, f) => s + f.distanceKm, 0);
  const detections = flights.reduce((s, f) => s + f.sampleCount, 0);
  const fuelGph = member?.fuelGph ?? 0;
  const estimatedGallons = (estimatedSeconds / 3600) * fuelGph;
  const estimatedCost = estimatedGallons * cfg.pricePerGallon;
  return {
    hex: member?.hex ?? (samples[0] && samples[0].hex) ?? null,
    tail: member?.tail ?? (samples[0] && samples[0].r) ?? null,
    model: member?.model ?? null,
    color: member?.color ?? "#666",
    fuelGph,
    flights,
    flightCount: flights.length,
    detections,
    estimatedSeconds,
    distanceKm,
    estimatedGallons,
    estimatedCost,
  };
}

/**
 * Analyse a set of samples (typically one day) across the whole fleet.
 * @param {Array} samples flat list of scraped samples
 * @param {{fleet: Array, fleetByHex?: Map}} ctx fleet metadata
 * @param {object} opts overrides for DEFAULTS
 */
export function analyzeDay(samples, ctx, opts = {}) {
  const cfg = { ...DEFAULTS, ...opts };
  const fleet = ctx?.fleet ?? [];
  const byHex =
    ctx?.fleetByHex ?? new Map(fleet.map((m) => [m.hex.toUpperCase(), m]));

  const grouped = new Map();
  for (const s of samples || []) {
    const key = String(s.hex || "").toUpperCase();
    if (!grouped.has(key)) grouped.set(key, []);
    grouped.get(key).push(s);
  }

  const perAircraft = [];
  for (const member of fleet) {
    const key = member.hex.toUpperCase();
    const group = grouped.get(key) || [];
    const result = analyzeAircraft(member, group, cfg);
    if (result.flightCount > 0) perAircraft.push(result);
  }
  // Any tracked aircraft not in the known roster (e.g. a new tail number).
  for (const [key, group] of grouped) {
    if (byHex.has(key)) continue;
    const result = analyzeAircraft(null, group, cfg);
    if (result.flightCount > 0) perAircraft.push(result);
  }

  perAircraft.sort((a, b) => b.estimatedSeconds - a.estimatedSeconds);

  const totals = perAircraft.reduce(
    (acc, a) => {
      acc.estimatedSeconds += a.estimatedSeconds;
      acc.distanceKm += a.distanceKm;
      acc.estimatedGallons += a.estimatedGallons;
      acc.estimatedCost += a.estimatedCost;
      acc.flightCount += a.flightCount;
      return acc;
    },
    { estimatedSeconds: 0, distanceKm: 0, estimatedGallons: 0, estimatedCost: 0, flightCount: 0 },
  );
  totals.activeAircraft = perAircraft.length;
  totals.estimatedHours = totals.estimatedSeconds / 3600;

  return { perAircraft, totals };
}

/** Aggregate several already-analysed days into one summary. */
export function aggregateDays(dayResults) {
  const perTail = new Map();
  const totals = {
    estimatedSeconds: 0,
    distanceKm: 0,
    estimatedGallons: 0,
    estimatedCost: 0,
    flightCount: 0,
    days: 0,
  };
  for (const day of dayResults) {
    totals.days += 1;
    for (const a of day.perAircraft) {
      const key = a.hex || a.tail;
      const entry = perTail.get(key) || {
        hex: a.hex,
        tail: a.tail,
        model: a.model,
        color: a.color,
        estimatedSeconds: 0,
        distanceKm: 0,
        estimatedGallons: 0,
        estimatedCost: 0,
        flightCount: 0,
        activeDays: 0,
      };
      entry.estimatedSeconds += a.estimatedSeconds;
      entry.distanceKm += a.distanceKm;
      entry.estimatedGallons += a.estimatedGallons;
      entry.estimatedCost += a.estimatedCost;
      entry.flightCount += a.flightCount;
      entry.activeDays += 1;
      perTail.set(key, entry);

      totals.estimatedSeconds += a.estimatedSeconds;
      totals.distanceKm += a.distanceKm;
      totals.estimatedGallons += a.estimatedGallons;
      totals.estimatedCost += a.estimatedCost;
      totals.flightCount += a.flightCount;
    }
  }
  const perAircraft = [...perTail.values()].sort(
    (a, b) => b.estimatedSeconds - a.estimatedSeconds,
  );
  totals.estimatedHours = totals.estimatedSeconds / 3600;
  return { perAircraft, totals };
}

/** Format a duration in seconds as "Hh Mm" (or "Mm" under an hour). */
export function formatDuration(seconds) {
  const total = Math.max(0, Math.round(seconds / 60));
  const h = Math.floor(total / 60);
  const m = total % 60;
  return h > 0 ? `${h}h ${m}m` : `${m}m`;
}

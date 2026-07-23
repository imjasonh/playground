/** Geodesy helpers for short corridor rays on WGS84. */

const EARTH_RADIUS_M = 6371008.8;
const DEG = Math.PI / 180;
const FT_TO_M = 0.3048;

export function feetToMeters(ft) {
  return ft * FT_TO_M;
}

export function metersToFeet(m) {
  return m / FT_TO_M;
}

export function metersToMiles(m) {
  return m / 1609.344;
}

export function milesToMeters(mi) {
  return mi * 1609.344;
}

/** Destination point given start, bearing° clockwise from north, and distance meters. */
export function destination(lat, lon, bearingDeg, distanceM) {
  const δ = distanceM / EARTH_RADIUS_M;
  const θ = bearingDeg * DEG;
  const φ1 = lat * DEG;
  const λ1 = lon * DEG;
  const sinφ1 = Math.sin(φ1);
  const cosφ1 = Math.cos(φ1);
  const sinδ = Math.sin(δ);
  const cosδ = Math.cos(δ);
  const sinφ2 = sinφ1 * cosδ + cosφ1 * sinδ * Math.cos(θ);
  const φ2 = Math.asin(sinφ2);
  const y = Math.sin(θ) * sinδ * cosφ1;
  const x = cosδ - sinφ1 * sinφ2;
  const λ2 = λ1 + Math.atan2(y, x);
  return {
    lat: φ2 / DEG,
    lon: ((λ2 / DEG + 540) % 360) - 180,
  };
}

/** Approximate meters per degree of latitude / longitude at a latitude. */
export function metersPerDegree(lat) {
  const φ = lat * DEG;
  const mPerDegLat =
    111132.92 - 559.82 * Math.cos(2 * φ) + 1.175 * Math.cos(4 * φ);
  const mPerDegLon = 111412.84 * Math.cos(φ) - 93.5 * Math.cos(3 * φ);
  return { lat: mPerDegLat, lon: Math.max(mPerDegLon, 1e-6) };
}

export function cellAreaM2(lat, cellDeg) {
  const { lat: mLat, lon: mLon } = metersPerDegree(lat);
  return Math.abs(mLat * cellDeg * mLon * cellDeg);
}

export function formatPeople(n) {
  if (!Number.isFinite(n)) return "—";
  const abs = Math.abs(n);
  if (abs >= 1e6) {
    const s = (n / 1e6).toFixed(2);
    return `${s.replace(/\.?0+$/, "")}M`;
  }
  if (abs >= 1e3) {
    const s = (n / 1e3).toFixed(abs >= 1e5 ? 0 : 1);
    return `${s.replace(/\.0$/, "")}k`;
  }
  return Math.round(n).toLocaleString("en-US");
}

export function formatDistance(m) {
  if (!Number.isFinite(m)) return "—";
  const miles = metersToMiles(m);
  if (miles >= 100) return `${miles.toFixed(0)} mi`;
  if (miles >= 10) return `${miles.toFixed(1)} mi`;
  if (miles >= 1) return `${miles.toFixed(2)} mi`;
  return `${Math.round(metersToFeet(m))} ft`;
}

/** Format a corridor width given in feet. */
export function formatWidth(ft) {
  if (!Number.isFinite(ft)) return "—";
  if (ft >= 5280) {
    const mi = ft / 5280;
    const rounded = Math.round(mi * 10) / 10;
    return `${Number.isInteger(rounded) ? rounded.toFixed(0) : rounded.toFixed(1)} mi`;
  }
  if (ft >= 1000) {
    const mi = ft / 5280;
    return `${mi.toFixed(2)} mi`;
  }
  return `${Math.round(ft)} ft`;
}

export function bearingLabel(bearingDeg) {
  const dirs = ["N", "NE", "E", "SE", "S", "SW", "W", "NW"];
  const idx = Math.round((((bearingDeg % 360) + 360) % 360) / 45) % 8;
  return dirs[idx];
}

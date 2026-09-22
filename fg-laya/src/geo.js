/** Earth helpers. Distances are nautical miles. Angles are degrees. */

export const NM_PER_DEG_LAT = 60;

export function clamp(value, lo, hi) {
  return Math.min(hi, Math.max(lo, value));
}

export function wrap360(deg) {
  const x = deg % 360;
  return x < 0 ? x + 360 : x;
}

/** Smallest signed heading error in (-180, 180]. Positive means the target is to the right. */
export function wrap180(deg) {
  const x = wrap360(deg);
  return x > 180 ? x - 360 : x;
}

export function degToRad(deg) {
  return (deg * Math.PI) / 180;
}

export function radToDeg(rad) {
  return (rad * 180) / Math.PI;
}

export function haversineNm(a, b) {
  const rNm = 3440.065;
  const dLat = degToRad(b.lat - a.lat);
  const dLon = degToRad(b.lon - a.lon);
  const lat1 = degToRad(a.lat);
  const lat2 = degToRad(b.lat);
  const h =
    Math.sin(dLat / 2) ** 2 + Math.cos(lat1) * Math.cos(lat2) * Math.sin(dLon / 2) ** 2;
  return 2 * rNm * Math.asin(Math.min(1, Math.sqrt(h)));
}

/** Initial bearing from a to b, 0-360, true north. */
export function bearingDeg(a, b) {
  const lat1 = degToRad(a.lat);
  const lat2 = degToRad(b.lat);
  const dLon = degToRad(b.lon - a.lon);
  const y = Math.sin(dLon) * Math.cos(lat2);
  const x = Math.cos(lat1) * Math.sin(lat2) - Math.sin(lat1) * Math.cos(lat2) * Math.cos(dLon);
  return wrap360(radToDeg(Math.atan2(y, x)));
}

export function offsetNm(origin, bearing, distanceNm) {
  const rNm = 3440.065;
  const ang = distanceNm / rNm;
  const brg = degToRad(bearing);
  const lat1 = degToRad(origin.lat);
  const lon1 = degToRad(origin.lon);
  const lat2 = Math.asin(
    Math.sin(lat1) * Math.cos(ang) + Math.cos(lat1) * Math.sin(ang) * Math.cos(brg),
  );
  const lon2 =
    lon1 +
    Math.atan2(
      Math.sin(brg) * Math.sin(ang) * Math.cos(lat1),
      Math.cos(ang) - Math.sin(lat1) * Math.sin(lat2),
    );
  return { lat: radToDeg(lat2), lon: radToDeg(lon2) };
}

export function headingErrorDeg(heading, desired) {
  return wrap180(desired - heading);
}

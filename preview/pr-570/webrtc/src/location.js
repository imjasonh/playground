// Location-sharing protocol + formatting helpers for the WebRTC app.
//
// A peer can share their position over the WebRTC data channel, either once or
// continuously ("live"). Positions come from the browser's Geolocation API,
// which is permission-gated: the browser prompts before the first read and the
// Permissions API lets us reflect the current grant state in the UI.
//
// The functions here are pure and DOM-free so they can be unit tested under
// Node and reused unchanged in the browser.

// Control-message kinds exchanged over the data channel for location.
export const LOCATION_KIND = "location";
export const LOCATION_STOP_KIND = "location-stop";

// Build the JSON message announcing a position. Accepts a GeolocationPosition
// (or a plain object shaped like one) and extracts just the safe, useful bits.
// `live` marks updates that are part of a continuous share so the receiver can
// label them differently from a one-shot drop.
export function createLocationMessage(position, { live = false } = {}) {
  const coords = position && position.coords;
  if (!coords || !Number.isFinite(coords.latitude) || !Number.isFinite(coords.longitude)) {
    throw new TypeError("createLocationMessage expects a position with numeric coords");
  }
  const msg = {
    kind: LOCATION_KIND,
    lat: coords.latitude,
    lon: coords.longitude,
    live: Boolean(live),
    ts: Number.isFinite(position.timestamp) ? position.timestamp : Date.now(),
  };
  if (Number.isFinite(coords.accuracy)) msg.accuracy = coords.accuracy;
  if (Number.isFinite(coords.heading)) msg.heading = coords.heading;
  if (Number.isFinite(coords.speed)) msg.speed = coords.speed;
  return msg;
}

// The trailer message telling the peer a live share has stopped.
export function createLocationStop() {
  return { kind: LOCATION_STOP_KIND };
}

// Validate + normalize an incoming location message. Returns a clean object or
// null when the payload isn't a usable location.
export function parseLocationMessage(msg) {
  if (!msg || msg.kind !== LOCATION_KIND) return null;
  const { lat, lon } = msg;
  if (!isValidLat(lat) || !isValidLon(lon)) return null;
  const out = { lat, lon, live: Boolean(msg.live), ts: Number.isFinite(msg.ts) ? msg.ts : null };
  if (Number.isFinite(msg.accuracy)) out.accuracy = msg.accuracy;
  if (Number.isFinite(msg.heading)) out.heading = msg.heading;
  if (Number.isFinite(msg.speed)) out.speed = msg.speed;
  return out;
}

export function isValidLat(lat) {
  return Number.isFinite(lat) && lat >= -90 && lat <= 90;
}

export function isValidLon(lon) {
  return Number.isFinite(lon) && lon >= -180 && lon <= 180;
}

// Format a coordinate pair for display, e.g. "40.71280, -74.00600".
export function formatCoords(lat, lon, digits = 5) {
  if (!isValidLat(lat) || !isValidLon(lon)) return "";
  return `${lat.toFixed(digits)}, ${lon.toFixed(digits)}`;
}

// Human-friendly accuracy, e.g. "±12 m" or "±1.3 km".
export function formatAccuracy(meters) {
  if (!Number.isFinite(meters) || meters < 0) return "";
  if (meters >= 1000) return `±${Math.round(meters / 100) / 10} km`;
  return `±${Math.round(meters)} m`;
}

// Build a provider-neutral map URL for a coordinate. OpenStreetMap needs no API
// key and works without a backend of ours.
export function mapsLink(lat, lon, zoom = 16) {
  if (!isValidLat(lat) || !isValidLon(lon)) return "";
  const z = Number.isFinite(zoom) ? zoom : 16;
  return `https://www.openstreetmap.org/?mlat=${lat}&mlon=${lon}#map=${z}/${lat}/${lon}`;
}

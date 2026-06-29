/**
 * Helpers over the bundled station registry: fast id lookup, transfer-complex
 * grouping, direction handling, and a small search used by the station picker.
 *
 * Realtime `stop_id`s are a station id plus an N/S direction suffix
 * ("R16N"); {@link splitStopId} undoes that. Several platforms can share one
 * transfer complex (Times Sq), so the picker and arrival board operate on
 * {@link COMPLEXES} rather than raw platforms.
 */

import { STATIONS } from './stationsData.js';
import { sortRoutes } from './routes.js';

/** @type {Map<string, import('./stationsData.js').Station>} */
export const STATION_BY_ID = new Map(STATIONS.map((station) => [station.id, station]));

/**
 * Split a realtime stop id into its station id and direction.
 * @param {string} stopId
 * @returns {{stationId: string, direction: ('N'|'S'|'')}}
 */
export function splitStopId(stopId) {
  if (!stopId) return { stationId: '', direction: '' };
  const id = String(stopId);
  const match = /^(.*?)([NS])$/.exec(id);
  if (match) {
    // Prefer the stripped id when it's a real station; otherwise the suffix was
    // part of the id itself (defensive — current data has no such ids).
    if (STATION_BY_ID.has(match[1])) return { stationId: match[1], direction: match[2] };
    if (STATION_BY_ID.has(id)) return { stationId: id, direction: '' };
    return { stationId: match[1], direction: match[2] };
  }
  return { stationId: id, direction: '' };
}

function mostCommon(values) {
  const counts = new Map();
  let best = '';
  let bestCount = 0;
  for (const value of values) {
    if (!value) continue;
    const next = (counts.get(value) || 0) + 1;
    counts.set(value, next);
    if (next > bestCount) {
      bestCount = next;
      best = value;
    }
  }
  return best;
}

function buildComplexes() {
  const groups = new Map();
  for (const station of STATIONS) {
    if (!groups.has(station.complex)) groups.set(station.complex, []);
    groups.get(station.complex).push(station);
  }

  const complexes = [];
  for (const [id, members] of groups) {
    const routes = sortRoutes(new Set(members.flatMap((m) => m.routes)));
    const boroughs = [...new Set(members.map((m) => m.borough))];
    const lat = members.reduce((sum, m) => sum + m.lat, 0) / members.length;
    const lon = members.reduce((sum, m) => sum + m.lon, 0) / members.length;
    complexes.push({
      id,
      name: mostCommon(members.map((m) => m.name)) || members[0].name,
      names: [...new Set(members.map((m) => m.name))],
      routes,
      boroughs,
      borough: boroughs.length === 1 ? boroughs[0] : 'Multiple boroughs',
      lat: Math.round(lat * 1e5) / 1e5,
      lon: Math.round(lon * 1e5) / 1e5,
      north: mostCommon(members.map((m) => m.north)) || 'Northbound',
      south: mostCommon(members.map((m) => m.south)) || 'Southbound',
      stationIds: members.map((m) => m.id),
      memberIds: new Set(members.map((m) => m.id)),
      stations: members,
    });
  }
  complexes.sort((a, b) => a.name.localeCompare(b.name));
  return complexes;
}

/** Every transfer complex, sorted by name. */
export const COMPLEXES = buildComplexes();

/** @type {Map<string, (typeof COMPLEXES)[number]>} */
export const COMPLEX_BY_ID = new Map(COMPLEXES.map((complex) => [complex.id, complex]));

/** Index from a member station id to its complex (so a stop id finds its hub). */
const COMPLEX_BY_STATION = new Map();
for (const complex of COMPLEXES) {
  for (const stationId of complex.stationIds) COMPLEX_BY_STATION.set(stationId, complex);
}

export function complexById(id) {
  return COMPLEX_BY_ID.get(String(id)) || null;
}

export function complexForStation(stationId) {
  return COMPLEX_BY_STATION.get(stationId) || null;
}

/** Direction labels for a complex, keyed by the N/S suffix. */
export function directionLabels(complex) {
  return { N: complex.north, S: complex.south };
}

/**
 * The destination station name for a trip — the name of the last stop in its
 * stop-time-update list. '' when unknown.
 * @param {{stopId?: string}[]} stopTimeUpdates
 */
export function terminusName(stopTimeUpdates) {
  if (!stopTimeUpdates || !stopTimeUpdates.length) return '';
  const last = stopTimeUpdates[stopTimeUpdates.length - 1];
  const { stationId } = splitStopId(last.stopId || '');
  const station = STATION_BY_ID.get(stationId);
  return station ? station.name : '';
}

/**
 * Rank complexes against a free-text query. Matches on name (best when the name
 * starts with the query), borough, and exact route labels (so "L" surfaces L
 * stops). Returns at most `limit` results; an empty query yields a stable,
 * popularity-ish default list (busiest hubs first, then alphabetical).
 *
 * @param {string} query
 * @param {number} [limit]
 */
export function searchComplexes(query, limit = 25) {
  const q = String(query || '').trim().toLowerCase();
  if (!q) {
    return [...COMPLEXES]
      .sort((a, b) => b.routes.length - a.routes.length || a.name.localeCompare(b.name))
      .slice(0, limit);
  }

  const scored = [];
  for (const complex of COMPLEXES) {
    const name = complex.name.toLowerCase();
    let score = 0;
    if (name === q) score = 100;
    else if (name.startsWith(q)) score = 80;
    else if (name.includes(q)) score = 50;
    else if (complex.names.some((n) => n.toLowerCase().includes(q))) score = 45;
    else if (complex.borough.toLowerCase().includes(q)) score = 20;

    const upper = q.toUpperCase();
    if (complex.routes.includes(upper)) score = Math.max(score, q.length <= 3 ? 60 : 40);

    if (score > 0) scored.push({ complex, score });
  }

  scored.sort(
    (a, b) => b.score - a.score || b.complex.routes.length - a.complex.routes.length
      || a.complex.name.localeCompare(b.complex.name),
  );
  return scored.slice(0, limit).map((entry) => entry.complex);
}

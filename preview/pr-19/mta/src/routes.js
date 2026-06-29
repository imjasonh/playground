/**
 * Subway route presentation metadata: the official MTA "bullet" colors and the
 * trunk-line each service runs on. Keyed by the display label (the same strings
 * the station dataset uses, e.g. "1", "A", "SIR").
 *
 * Realtime feeds occasionally use variant route ids — express diamonds carry a
 * trailing "X" (e.g. "6X"), Staten Island is "SI", and the shuttles come through
 * as "GS"/"FS"/"H". {@link normalizeRouteId} folds those onto the labels below.
 *
 * Colors: MTA "Subway Line Colors" standard (https://www.mta.info).
 */

const RED = '#ee352e';
const GREEN = '#00933c';
const PURPLE = '#b933ad';
const BLUE = '#0039a6';
const ORANGE = '#ff6319';
const LIGHT_GREEN = '#6cbe45';
const BROWN = '#996633';
const GREY = '#a7a9ac';
const YELLOW = '#fccc0a';
const SHUTTLE = '#808183';
const SIR_BLUE = '#003986';

const WHITE = '#ffffff';
const BLACK = '#000000';

/** @type {Record<string, {color: string, text: string, trunk: string}>} */
export const ROUTES = {
  '1': { color: RED, text: WHITE, trunk: 'Broadway–7 Av' },
  '2': { color: RED, text: WHITE, trunk: '7 Av Express' },
  '3': { color: RED, text: WHITE, trunk: '7 Av Express' },
  '4': { color: GREEN, text: WHITE, trunk: 'Lexington Av Express' },
  '5': { color: GREEN, text: WHITE, trunk: 'Lexington Av Express' },
  '6': { color: GREEN, text: WHITE, trunk: 'Lexington Av Local' },
  '7': { color: PURPLE, text: WHITE, trunk: 'Flushing' },
  A: { color: BLUE, text: WHITE, trunk: '8 Av Express' },
  C: { color: BLUE, text: WHITE, trunk: '8 Av Local' },
  E: { color: BLUE, text: WHITE, trunk: '8 Av Local' },
  B: { color: ORANGE, text: WHITE, trunk: '6 Av Express' },
  D: { color: ORANGE, text: WHITE, trunk: '6 Av Express' },
  F: { color: ORANGE, text: WHITE, trunk: '6 Av Local' },
  M: { color: ORANGE, text: WHITE, trunk: '6 Av Local' },
  G: { color: LIGHT_GREEN, text: WHITE, trunk: 'Crosstown' },
  J: { color: BROWN, text: WHITE, trunk: 'Nassau St' },
  Z: { color: BROWN, text: WHITE, trunk: 'Nassau St' },
  L: { color: GREY, text: WHITE, trunk: '14 St–Canarsie' },
  N: { color: YELLOW, text: BLACK, trunk: 'Broadway' },
  Q: { color: YELLOW, text: BLACK, trunk: 'Broadway' },
  R: { color: YELLOW, text: BLACK, trunk: 'Broadway Local' },
  W: { color: YELLOW, text: BLACK, trunk: 'Broadway Local' },
  S: { color: SHUTTLE, text: WHITE, trunk: 'Shuttle' },
  SIR: { color: SIR_BLUE, text: WHITE, trunk: 'Staten Island Railway' },
};

/**
 * Map a raw realtime/static route id onto a display label present in
 * {@link ROUTES}. Returns the trimmed id unchanged when it has no special form.
 *
 * @param {string} routeId
 * @returns {string}
 */
export function normalizeRouteId(routeId) {
  if (!routeId) return '';
  let id = String(routeId).trim();
  if (id === 'SI' || id === 'SIR') return 'SIR';
  if (id === 'GS' || id === 'FS' || id === 'H' || id === 'S') return 'S';
  // Express diamonds ("6X") share the local bullet.
  if (/^\d+X$/.test(id)) id = id.slice(0, -1);
  return id;
}

/**
 * Presentation for a route id. Unknown ids get a neutral grey bullet so the UI
 * never crashes on a route the dataset doesn't know about.
 *
 * @param {string} routeId
 * @returns {{label: string, color: string, text: string, trunk: string}}
 */
export function routeStyle(routeId) {
  const label = normalizeRouteId(routeId);
  const meta = ROUTES[label];
  if (!meta) return { label: label || '?', color: SHUTTLE, text: WHITE, trunk: '' };
  return { label, ...meta };
}

/** All known display labels, in railfan/canonical order. */
export const ROUTE_ORDER = [
  '1', '2', '3', '4', '5', '6', '7',
  'A', 'C', 'E', 'B', 'D', 'F', 'M',
  'G', 'J', 'Z', 'L', 'N', 'Q', 'R', 'W', 'S', 'SIR',
];

/** Sort a set/array of route labels into {@link ROUTE_ORDER}. */
export function sortRoutes(routes) {
  const rank = (r) => {
    const index = ROUTE_ORDER.indexOf(normalizeRouteId(r));
    return index === -1 ? ROUTE_ORDER.length : index;
  };
  return [...routes].sort((a, b) => rank(a) - rank(b) || String(a).localeCompare(String(b)));
}

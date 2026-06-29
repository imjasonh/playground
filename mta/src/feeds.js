/**
 * The MTA's public GTFS-realtime subway feeds.
 *
 * As of 2023 these require **no API key**, but they are protobuf-encoded and are
 * served *without* CORS headers, so a browser on another origin must route them
 * through a proxy (see proxy.js) — or use the app's bundled sample data.
 *
 * Feed groupings + URLs: https://api.mta.info/#/subwayRealTimeFeeds
 */

import { normalizeRouteId } from './routes.js';

export const BASE_URL = 'https://api-endpoint.mta.info/Dataservice/mtagtfsfeeds/';

/**
 * @typedef {Object} Feed
 * @property {string} key     stable internal id
 * @property {string} label   short human label
 * @property {string} path    path segment under {@link BASE_URL}
 * @property {string[]} routes display labels carried by this feed
 */

/** @type {Feed[]} */
export const FEEDS = [
  { key: 'numbered', label: '1 2 3 4 5 6 7 S', path: 'nyct%2Fgtfs', routes: ['1', '2', '3', '4', '5', '6', '7', 'S'] },
  { key: 'ace', label: 'A C E', path: 'nyct%2Fgtfs-ace', routes: ['A', 'C', 'E', 'S'] },
  { key: 'bdfm', label: 'B D F M', path: 'nyct%2Fgtfs-bdfm', routes: ['B', 'D', 'F', 'M'] },
  { key: 'g', label: 'G', path: 'nyct%2Fgtfs-g', routes: ['G'] },
  { key: 'jz', label: 'J Z', path: 'nyct%2Fgtfs-jz', routes: ['J', 'Z'] },
  { key: 'nqrw', label: 'N Q R W', path: 'nyct%2Fgtfs-nqrw', routes: ['N', 'Q', 'R', 'W'] },
  { key: 'l', label: 'L', path: 'nyct%2Fgtfs-l', routes: ['L'] },
  { key: 'si', label: 'SIR', path: 'nyct%2Fgtfs-si', routes: ['SIR'] },
];

/** The system-wide service alerts feed (GTFS-realtime, alerts only). */
export const ALERTS_FEED = {
  key: 'alerts',
  label: 'Service alerts',
  path: 'camsys%2Fall-alerts',
  routes: [],
};

/** Full upstream URL for a feed. */
export function feedUrl(feed) {
  return BASE_URL + feed.path;
}

/** Look up a feed (line feeds + alerts) by its key. */
export function feedByKey(key) {
  if (key === ALERTS_FEED.key) return ALERTS_FEED;
  return FEEDS.find((feed) => feed.key === key) || null;
}

/**
 * The line feeds needed to cover a set of routes. A station served by N/Q/R and
 * the S shuttle, say, resolves to just the feeds carrying those routes.
 *
 * @param {Iterable<string>} routes
 * @returns {Feed[]}
 */
export function feedsForRoutes(routes) {
  const labels = new Set([...routes].map(normalizeRouteId));
  return FEEDS.filter((feed) => feed.routes.some((route) => labels.has(route)));
}

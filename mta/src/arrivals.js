/**
 * Turn a decoded line feed into an arrival board for one station complex:
 * upcoming trains split by direction (N/S), each with a countdown and the
 * destination terminal, soonest first.
 *
 * A trip's stop-time-update list only contains *upcoming* stops, so a train that
 * already left the station simply isn't in the feed for it — we additionally
 * drop anything whose predicted time is already comfortably in the past.
 */

import { normalizeRouteId } from './routes.js';
import { splitStopId, directionLabels, terminusName } from './stations.js';
import { minutesUntil, formatCountdown, clockTime } from './format.js';

/**
 * @param {{entities: object[]}} feedMessage  decoded FeedMessage (line feed)
 * @param {object} complex                    a complex from stations.js
 * @param {{now?: number, perDirection?: number}} [options]
 * @returns {{
 *   complexId: string, name: string, totalUpcoming: number,
 *   directions: {dir: 'N'|'S', label: string, trains: object[]}[]
 * }}
 */
export function buildArrivals(feedMessage, complex, { now = Date.now(), perDirection = 6 } = {}) {
  const lanes = { N: [], S: [] };

  if (feedMessage && complex) {
    for (const entity of feedMessage.entities) {
      const tripUpdate = entity.tripUpdate;
      if (!tripUpdate || !tripUpdate.trip) continue;

      const route = normalizeRouteId(tripUpdate.trip.routeId);
      const destination = terminusName(tripUpdate.stopTimeUpdates);

      for (const update of tripUpdate.stopTimeUpdates || []) {
        const { stationId, direction } = splitStopId(update.stopId);
        if (!complex.memberIds.has(stationId)) continue;
        if (direction !== 'N' && direction !== 'S') continue;

        const time = (update.arrival && update.arrival.time) || (update.departure && update.departure.time);
        if (!Number.isFinite(time)) continue;

        const eta = minutesUntil(time, now);
        if (eta < -0.75) continue;

        lanes[direction].push({
          route,
          time,
          tripId: tripUpdate.trip.tripId || '',
          destination,
          stationId,
          etaMinutes: eta,
          minutes: Math.max(0, Math.round(eta)),
          countdown: formatCountdown(time, now),
          clock: clockTime(time),
        });
      }
    }
  }

  for (const dir of ['N', 'S']) {
    lanes[dir].sort((a, b) => a.time - b.time);
    lanes[dir] = lanes[dir].slice(0, perDirection);
  }

  const labels = complex ? directionLabels(complex) : { N: 'Northbound', S: 'Southbound' };
  return {
    complexId: complex ? complex.id : '',
    name: complex ? complex.name : '',
    directions: [
      { dir: 'N', label: labels.N || 'Northbound', trains: lanes.N },
      { dir: 'S', label: labels.S || 'Southbound', trains: lanes.S },
    ],
    totalUpcoming: lanes.N.length + lanes.S.length,
  };
}

/**
 * Turn the vehicle-position entities in a decoded feed into a human list of
 * "where the trains are right now": one row per train with a plain-English
 * location ("Stopped at …", "Approaching …", "En route to …"), its direction,
 * destination, and coordinates.
 */

import { normalizeRouteId, routeStyle, sortRoutes } from './routes.js';
import { VEHICLE_STATUS } from './gtfsRealtime.js';
import { splitStopId, STATION_BY_ID, complexForStation, terminusName } from './stations.js';
import { freshness } from './format.js';

const STATUS_KIND = {
  [VEHICLE_STATUS.STOPPED_AT]: 'stopped',
  [VEHICLE_STATUS.INCOMING_AT]: 'incoming',
  [VEHICLE_STATUS.IN_TRANSIT_TO]: 'transit',
};

const STATUS_VERB = {
  stopped: 'Stopped at',
  incoming: 'Approaching',
  transit: 'En route to',
};

// Trains that are stopped read first, then approaching, then in transit.
const KIND_SORT = { stopped: 0, incoming: 1, transit: 2 };

function directionLabelFor(stationId, direction) {
  const complex = complexForStation(stationId);
  if (complex && direction === 'N') return complex.north;
  if (complex && direction === 'S') return complex.south;
  if (direction === 'N') return 'Northbound';
  if (direction === 'S') return 'Southbound';
  return '';
}

/**
 * @param {{entities: object[]}} feedMessage
 * @param {{now?: number, routes?: Iterable<string>, complex?: object, limit?: number}} [options]
 */
export function buildTrains(feedMessage, { now = Date.now(), routes, complex, limit = 200 } = {}) {
  const routeFilter = routes ? new Set([...routes].map(normalizeRouteId)) : null;

  // Map trip id -> destination terminal, harvested from trip updates, so a
  // vehicle (which carries no stop list) can still show where it's headed.
  const destinations = new Map();
  for (const entity of feedMessage ? feedMessage.entities : []) {
    const tripUpdate = entity.tripUpdate;
    if (tripUpdate && tripUpdate.trip && tripUpdate.trip.tripId) {
      const name = terminusName(tripUpdate.stopTimeUpdates);
      if (name) destinations.set(tripUpdate.trip.tripId, name);
    }
  }

  const trains = [];
  const counts = new Map();

  for (const entity of feedMessage ? feedMessage.entities : []) {
    const vehicle = entity.vehicle;
    if (!vehicle || !vehicle.trip) continue;

    const route = normalizeRouteId(vehicle.trip.routeId);
    if (routeFilter && !routeFilter.has(route)) continue;

    const { stationId, direction } = splitStopId(vehicle.stopId || '');
    const station = STATION_BY_ID.get(stationId);
    const stationName = station ? station.name : vehicle.stopId || 'the line';

    const status = vehicle.currentStatus ?? VEHICLE_STATUS.IN_TRANSIT_TO;
    const kind = STATUS_KIND[status] || 'transit';

    counts.set(route, (counts.get(route) || 0) + 1);

    trains.push({
      ...routeStyle(route),
      tripId: vehicle.trip.tripId || '',
      statusKind: kind,
      statusText: `${STATUS_VERB[kind]} ${stationName}`,
      stationId,
      stationName,
      direction,
      directionLabel: directionLabelFor(stationId, direction),
      destination: destinations.get(vehicle.trip.tripId) || '',
      lat: vehicle.position ? vehicle.position.latitude : undefined,
      lon: vehicle.position ? vehicle.position.longitude : undefined,
      bearing: vehicle.position ? vehicle.position.bearing : undefined,
      updatedText: Number.isFinite(vehicle.timestamp) ? freshness(vehicle.timestamp, now) : '',
      atSelected: Boolean(complex && complex.memberIds.has(stationId)),
    });
  }

  trains.sort(
    (a, b) => Number(b.atSelected) - Number(a.atSelected)
      || KIND_SORT[a.statusKind] - KIND_SORT[b.statusKind]
      || a.label.localeCompare(b.label),
  );

  const byRoute = sortRoutes([...counts.keys()]).map((labelKey) => ({
    ...routeStyle(labelKey),
    count: counts.get(labelKey),
  }));

  return {
    trains: trains.slice(0, limit),
    total: trains.length,
    byRoute,
  };
}

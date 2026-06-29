/**
 * Generate realistic GTFS-realtime feeds for offline "Sample data" mode (and as
 * fixtures for tests). Everything is encoded to real protobuf bytes with the
 * {@link Writer} and then runs back through the normal decode pipeline, so
 * sample mode exercises exactly the same code path as live mode — just without
 * the network and CORS proxy.
 *
 * Times are anchored to the supplied `now`, so countdowns tick down naturally on
 * each refresh and the demo feels alive.
 */

import { Writer } from './protobuf.js';
import { VEHICLE_STATUS } from './gtfsRealtime.js';
import { STATIONS } from './stationsData.js';

const ALERT_EFFECT = {
  NO_SERVICE: 1,
  REDUCED_SERVICE: 2,
  SIGNIFICANT_DELAYS: 3,
  MODIFIED_SERVICE: 6,
};

/** Stable 32-bit hash for deterministic-but-varied sample values. */
function hash(str) {
  let h = 2166136261;
  for (let i = 0; i < str.length; i += 1) {
    h ^= str.charCodeAt(i);
    h = Math.imul(h, 16777619);
  }
  return h >>> 0;
}

function encTranslated(text) {
  return new Writer().message(1, new Writer().string(1, text));
}

function encTrip(trip) {
  const w = new Writer();
  if (trip.tripId != null) w.string(1, trip.tripId);
  if (trip.startTime != null) w.string(2, trip.startTime);
  if (trip.startDate != null) w.string(3, trip.startDate);
  if (trip.routeId != null) w.string(5, trip.routeId);
  if (trip.directionId != null) w.varint(6, trip.directionId);
  return w;
}

function encStopTimeUpdate(update) {
  const w = new Writer();
  if (update.arrival != null) w.message(2, new Writer().varint(2, update.arrival));
  if (update.departure != null) w.message(3, new Writer().varint(2, update.departure));
  if (update.stopId != null) w.string(4, update.stopId);
  return w;
}

function encTripUpdate(tripUpdate) {
  const w = new Writer().message(1, encTrip(tripUpdate.trip));
  for (const update of tripUpdate.stopTimeUpdates || []) w.message(2, encStopTimeUpdate(update));
  if (tripUpdate.timestamp != null) w.varint(4, tripUpdate.timestamp);
  return w;
}

function encPosition(position) {
  const w = new Writer();
  if (position.latitude != null) w.float(1, position.latitude);
  if (position.longitude != null) w.float(2, position.longitude);
  if (position.bearing != null) w.float(3, position.bearing);
  return w;
}

function encVehicle(vehicle) {
  const w = new Writer().message(1, encTrip(vehicle.trip));
  if (vehicle.position) w.message(2, encPosition(vehicle.position));
  if (vehicle.currentStopSequence != null) w.varint(3, vehicle.currentStopSequence);
  if (vehicle.currentStatus != null) w.varint(4, vehicle.currentStatus);
  if (vehicle.timestamp != null) w.varint(5, vehicle.timestamp);
  if (vehicle.stopId != null) w.string(7, vehicle.stopId);
  return w;
}

function encAlert(alert) {
  const w = new Writer();
  for (const period of alert.activePeriods || []) {
    const range = new Writer();
    if (period.start != null) range.varint(1, period.start);
    if (period.end != null) range.varint(2, period.end);
    w.message(1, range);
  }
  for (const sel of alert.informedEntities || []) {
    const selector = new Writer();
    if (sel.routeId != null) selector.string(2, sel.routeId);
    if (sel.stopId != null) selector.string(5, sel.stopId);
    w.message(5, selector);
  }
  if (alert.cause != null) w.varint(6, alert.cause);
  if (alert.effect != null) w.varint(7, alert.effect);
  if (alert.url != null) w.message(8, encTranslated(alert.url));
  if (alert.headerText != null) w.message(10, encTranslated(alert.headerText));
  if (alert.descriptionText != null) w.message(11, encTranslated(alert.descriptionText));
  return w;
}

function encEntity(entity) {
  const w = new Writer();
  if (entity.id != null) w.string(1, entity.id);
  if (entity.tripUpdate) w.message(3, encTripUpdate(entity.tripUpdate));
  if (entity.vehicle) w.message(4, encVehicle(entity.vehicle));
  if (entity.alert) w.message(5, encAlert(entity.alert));
  return w;
}

/**
 * Encode a feed described as plain objects into GTFS-realtime bytes. Mirrors the
 * decoder in gtfsRealtime.js and is the workhorse for tests.
 *
 * @param {{header?: {version?: string, timestamp?: number}, entities?: object[]}} feed
 * @returns {Uint8Array}
 */
export function encodeFeedMessage({ header = {}, entities = [] } = {}) {
  const headerWriter = new Writer().string(1, header.version || '2.0');
  if (header.timestamp != null) headerWriter.varint(3, header.timestamp);
  const w = new Writer().message(1, headerWriter);
  for (const entity of entities) w.message(2, encEntity(entity));
  return w.finish();
}

function dateStamp(date) {
  const y = date.getFullYear();
  const m = String(date.getMonth() + 1).padStart(2, '0');
  const d = String(date.getDate()).padStart(2, '0');
  return `${y}${m}${d}`;
}

/** North/south terminal stations for a route (by latitude extremes). */
function terminalsForRoute(route) {
  const serving = STATIONS.filter((s) => s.routes.includes(route));
  if (!serving.length) return { N: null, S: null };
  return {
    N: serving.reduce((a, b) => (b.lat > a.lat ? b : a)),
    S: serving.reduce((a, b) => (b.lat < a.lat ? b : a)),
  };
}

const STATUSES = [VEHICLE_STATUS.STOPPED_AT, VEHICLE_STATUS.INCOMING_AT, VEHICLE_STATUS.IN_TRANSIT_TO];

/**
 * A line feed (trip updates + vehicle positions) populated for the routes that
 * serve `complex`, so whatever station the user picks, sample mode shows a full
 * arrival board and live trains.
 *
 * @param {{now?: number, complex?: object}} [options]
 * @returns {Uint8Array}
 */
export function buildSampleLineFeed({ now = Date.now(), complex } = {}) {
  const nowSec = Math.floor(now / 1000);
  const startDate = dateStamp(new Date(now));
  const entities = [];

  if (complex) {
    for (const route of complex.routes) {
      const station = complex.stations.find((s) => s.routes.includes(route)) || complex.stations[0];
      const terminals = terminalsForRoute(route);

      for (const dir of ['N', 'S']) {
        const terminal = terminals[dir];
        const seed = hash(`${route}${dir}${complex.id}`);
        const base = 60 + (seed % 5) * 45; // first train 1–4.5 min out
        const gap = 180 + (seed % 4) * 60; // 3–6 min headways

        for (let i = 0; i < 3; i += 1) {
          const arrive = nowSec + base + i * gap;
          const tripId = `${route}_${dir}_${i}_sample`;
          const stopTimeUpdates = [{ stopId: `${station.id}${dir}`, arrival: arrive, departure: arrive + 30 }];
          if (terminal && terminal.id !== station.id) {
            stopTimeUpdates.push({ stopId: `${terminal.id}${dir}`, arrival: arrive + 600 + i * 90 });
          }
          entities.push({
            id: `tu_${tripId}`,
            tripUpdate: {
              trip: { tripId, routeId: route, startDate, directionId: dir === 'N' ? 0 : 1 },
              stopTimeUpdates,
              timestamp: nowSec,
            },
          });
        }

        entities.push({
          id: `v_${route}_${dir}`,
          vehicle: {
            trip: { tripId: `${route}_${dir}_0_sample`, routeId: route, startDate },
            stopId: `${station.id}${dir}`,
            currentStatus: STATUSES[seed % STATUSES.length],
            currentStopSequence: 1 + (seed % 20),
            timestamp: nowSec - (seed % 25),
            position: {
              latitude: station.lat,
              longitude: station.lon,
              bearing: dir === 'N' ? 0 : 180,
            },
          },
        });
      }
    }
  }

  return encodeFeedMessage({ header: { version: '2.0', timestamp: nowSec }, entities });
}

/**
 * A system-wide alerts feed: a spread of active and planned conditions so the
 * status board shows the full range of states (delays, no service, planned
 * work, service change) and leaves the rest on "Good Service".
 *
 * @param {{now?: number}} [options]
 * @returns {Uint8Array}
 */
export function buildSampleAlertsFeed({ now = Date.now() } = {}) {
  const nowSec = Math.floor(now / 1000);
  const activeNow = [{ start: nowSec - 3600, end: nowSec + 3600 }];
  const thisWeekend = [{ start: nowSec + 2 * 86400, end: nowSec + 3 * 86400 }];

  const alerts = [
    {
      id: 'alert_a_delays',
      effect: ALERT_EFFECT.SIGNIFICANT_DELAYS,
      routes: ['A'],
      header: 'Southbound A trains are delayed',
      description:
        'Southbound A trains are running with delays while crews address a signal problem at Jay St-MetroTech.',
      activePeriods: activeNow,
    },
    {
      id: 'alert_g_noservice',
      effect: ALERT_EFFECT.NO_SERVICE,
      routes: ['G'],
      header: 'No G train service between Court Sq and Bedford-Nostrand Avs',
      description: 'Shuttle buses replace G trains while track work is underway. Allow extra travel time.',
      activePeriods: activeNow,
    },
    {
      id: 'alert_7_change',
      effect: ALERT_EFFECT.MODIFIED_SERVICE,
      routes: ['7'],
      header: '7 trains run express in Queens',
      description: 'For faster service, 7 trains skip 33 St through 40 St in the Manhattan-bound direction.',
      activePeriods: activeNow,
    },
    {
      id: 'alert_f_planned',
      effect: ALERT_EFFECT.MODIFIED_SERVICE,
      routes: ['F'],
      header: 'Planned Work: F trains run local in Brooklyn this weekend',
      description: 'Planned work means F trains make all local stops between Jay St-MetroTech and Church Av.',
      activePeriods: thisWeekend,
    },
    {
      id: 'alert_2_delays',
      effect: ALERT_EFFECT.SIGNIFICANT_DELAYS,
      routes: ['2', '3'],
      header: 'Delays on 2 and 3 trains',
      description: 'We are delaying some 2 and 3 trains while we assist a passenger who took ill.',
      activePeriods: activeNow,
    },
  ];

  const entities = alerts.map((alert) => ({
    id: alert.id,
    alert: {
      effect: alert.effect,
      headerText: alert.header,
      descriptionText: alert.description,
      activePeriods: alert.activePeriods,
      informedEntities: alert.routes.map((routeId) => ({ routeId })),
    },
  }));

  return encodeFeedMessage({ header: { version: '2.0', timestamp: nowSec }, entities });
}

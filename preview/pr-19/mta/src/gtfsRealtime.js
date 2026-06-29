/**
 * Decode a GTFS-realtime `FeedMessage` into plain JS objects.
 *
 * Field numbers below come straight from the canonical `gtfs-realtime.proto`
 * (the same schema the MTA serves). We only pull out the fields this app uses —
 * trip updates (arrival predictions), vehicle positions (where trains are), and
 * service alerts — and ignore everything else. The NYCT proto extensions
 * (scheduled track, train id, ...) live in extension field numbers we simply
 * skip; direction is recovered from the stop_id suffix instead, which needs no
 * extension.
 *
 * Spec: https://gtfs.org/realtime/reference/
 */

import { eachField } from './protobuf.js';

/** VehiclePosition.current_status enum. */
export const VEHICLE_STATUS = {
  INCOMING_AT: 0,
  STOPPED_AT: 1,
  IN_TRANSIT_TO: 2,
};

/** Pick the best text out of a TranslatedString (prefers English). */
function decodeTranslatedString(reader) {
  const translations = [];
  eachField(reader, (field, r) => {
    if (field !== 1) return;
    const t = { text: '', language: '' };
    eachField(r.readMessage(), (f, rr) => {
      if (f === 1) t.text = rr.readString();
      else if (f === 2) t.language = rr.readString();
    });
    translations.push(t);
  });
  const english = translations.find((t) => /^en/i.test(t.language) || t.language === '');
  return (english || translations[0] || { text: '' }).text;
}

function decodeTrip(reader) {
  const trip = {};
  eachField(reader, (field, r) => {
    if (field === 1) trip.tripId = r.readString();
    else if (field === 2) trip.startTime = r.readString();
    else if (field === 3) trip.startDate = r.readString();
    else if (field === 5) trip.routeId = r.readString();
    else if (field === 6) trip.directionId = r.readVarint();
  });
  return trip;
}

function decodeStopTimeEvent(reader) {
  const event = {};
  eachField(reader, (field, r) => {
    if (field === 1) event.delay = r.readVarint();
    else if (field === 2) event.time = r.readVarint();
  });
  return event;
}

function decodeStopTimeUpdate(reader) {
  const update = {};
  eachField(reader, (field, r) => {
    if (field === 1) update.stopSequence = r.readVarint();
    else if (field === 2) update.arrival = decodeStopTimeEvent(r.readMessage());
    else if (field === 3) update.departure = decodeStopTimeEvent(r.readMessage());
    else if (field === 4) update.stopId = r.readString();
  });
  return update;
}

function decodeTripUpdate(reader) {
  const tripUpdate = { stopTimeUpdates: [] };
  eachField(reader, (field, r) => {
    if (field === 1) tripUpdate.trip = decodeTrip(r.readMessage());
    else if (field === 2) tripUpdate.stopTimeUpdates.push(decodeStopTimeUpdate(r.readMessage()));
    else if (field === 4) tripUpdate.timestamp = r.readVarint();
  });
  return tripUpdate;
}

function decodePosition(reader) {
  const position = {};
  eachField(reader, (field, r, wireType) => {
    const read = () => (wireType === 1 ? r.readDouble() : r.readFloat());
    if (field === 1) position.latitude = read();
    else if (field === 2) position.longitude = read();
    else if (field === 3) position.bearing = read();
  });
  return position;
}

function decodeVehicle(reader) {
  const vehicle = {};
  eachField(reader, (field, r) => {
    if (field === 1) vehicle.trip = decodeTrip(r.readMessage());
    else if (field === 2) vehicle.position = decodePosition(r.readMessage());
    else if (field === 3) vehicle.currentStopSequence = r.readVarint();
    else if (field === 4) vehicle.currentStatus = r.readVarint();
    else if (field === 5) vehicle.timestamp = r.readVarint();
    else if (field === 7) vehicle.stopId = r.readString();
  });
  return vehicle;
}

function decodeEntitySelector(reader) {
  const selector = {};
  eachField(reader, (field, r) => {
    if (field === 2) selector.routeId = r.readString();
    else if (field === 4) selector.trip = decodeTrip(r.readMessage());
    else if (field === 5) selector.stopId = r.readString();
  });
  return selector;
}

function decodeTimeRange(reader) {
  const range = {};
  eachField(reader, (field, r) => {
    if (field === 1) range.start = r.readVarint();
    else if (field === 2) range.end = r.readVarint();
  });
  return range;
}

function decodeAlert(reader) {
  const alert = { informedEntities: [], activePeriods: [] };
  eachField(reader, (field, r) => {
    if (field === 1) alert.activePeriods.push(decodeTimeRange(r.readMessage()));
    else if (field === 5) alert.informedEntities.push(decodeEntitySelector(r.readMessage()));
    else if (field === 6) alert.cause = r.readVarint();
    else if (field === 7) alert.effect = r.readVarint();
    else if (field === 8) alert.url = decodeTranslatedString(r.readMessage());
    else if (field === 10) alert.headerText = decodeTranslatedString(r.readMessage());
    else if (field === 11) alert.descriptionText = decodeTranslatedString(r.readMessage());
  });
  return alert;
}

function decodeEntity(reader) {
  const entity = {};
  eachField(reader, (field, r) => {
    if (field === 1) entity.id = r.readString();
    else if (field === 2) entity.isDeleted = Boolean(r.readVarint());
    else if (field === 3) entity.tripUpdate = decodeTripUpdate(r.readMessage());
    else if (field === 4) entity.vehicle = decodeVehicle(r.readMessage());
    else if (field === 5) entity.alert = decodeAlert(r.readMessage());
  });
  return entity;
}

function decodeFeedHeader(reader) {
  const header = {};
  eachField(reader, (field, r) => {
    if (field === 1) header.version = r.readString();
    else if (field === 3) header.timestamp = r.readVarint();
  });
  return header;
}

/**
 * @param {Uint8Array} bytes  raw GTFS-realtime FeedMessage
 * @returns {{header: {version?: string, timestamp?: number}, entities: object[]}}
 */
export function decodeFeedMessage(bytes) {
  const message = { header: {}, entities: [] };
  eachField(bytes, (field, r) => {
    if (field === 1) message.header = decodeFeedHeader(r.readMessage());
    else if (field === 2) message.entities.push(decodeEntity(r.readMessage()));
  });
  return message;
}

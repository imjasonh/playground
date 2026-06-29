import { encodeFeedMessage } from '../src/sampleFeed.js';
import { decodeFeedMessage, VEHICLE_STATUS } from '../src/gtfsRealtime.js';

describe('decodeFeedMessage', () => {
  const bytes = encodeFeedMessage({
    header: { version: '2.0', timestamp: 1700000000 },
    entities: [
      {
        id: 't1',
        tripUpdate: {
          trip: { tripId: 'A_trip', routeId: 'A', startDate: '20260629', directionId: 0 },
          stopTimeUpdates: [
            { stopId: 'A27N', arrival: 1700000600, departure: 1700000620 },
            { stopId: 'A09N', arrival: 1700001200 },
          ],
          timestamp: 1700000000,
        },
      },
      {
        id: 'v1',
        vehicle: {
          trip: { tripId: 'A_trip', routeId: 'A' },
          stopId: 'A27N',
          currentStatus: VEHICLE_STATUS.STOPPED_AT,
          currentStopSequence: 7,
          timestamp: 1700000000,
          position: { latitude: 40.7559, longitude: -73.9871, bearing: 90 },
        },
      },
      {
        id: 'al1',
        alert: {
          effect: 3,
          headerText: 'Delays',
          descriptionText: 'Signal problems',
          informedEntities: [{ routeId: 'A' }, { routeId: 'C' }],
          activePeriods: [{ start: 100, end: 200 }],
        },
      },
    ],
  });

  const feed = decodeFeedMessage(bytes);

  test('decodes the header', () => {
    expect(feed.header.version).toBe('2.0');
    expect(feed.header.timestamp).toBe(1700000000);
    expect(feed.entities).toHaveLength(3);
  });

  test('decodes a trip update with ordered stop-time updates', () => {
    const tu = feed.entities[0].tripUpdate;
    expect(tu.trip.routeId).toBe('A');
    expect(tu.trip.tripId).toBe('A_trip');
    expect(tu.trip.startDate).toBe('20260629');
    expect(tu.stopTimeUpdates).toHaveLength(2);
    expect(tu.stopTimeUpdates[0].stopId).toBe('A27N');
    expect(tu.stopTimeUpdates[0].arrival.time).toBe(1700000600);
    expect(tu.stopTimeUpdates[0].departure.time).toBe(1700000620);
    expect(tu.stopTimeUpdates[1].arrival.time).toBe(1700001200);
  });

  test('decodes a vehicle position', () => {
    const v = feed.entities[1].vehicle;
    expect(v.trip.routeId).toBe('A');
    expect(v.stopId).toBe('A27N');
    expect(v.currentStatus).toBe(VEHICLE_STATUS.STOPPED_AT);
    expect(v.position.latitude).toBeCloseTo(40.7559, 3);
    expect(v.position.longitude).toBeCloseTo(-73.9871, 3);
  });

  test('decodes an alert with informed routes and a period', () => {
    const a = feed.entities[2].alert;
    expect(a.effect).toBe(3);
    expect(a.headerText).toBe('Delays');
    expect(a.descriptionText).toBe('Signal problems');
    expect(a.informedEntities.map((e) => e.routeId)).toEqual(['A', 'C']);
    expect(a.activePeriods[0]).toEqual({ start: 100, end: 200 });
  });
});

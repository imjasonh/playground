import { encodeFeedMessage } from '../src/sampleFeed.js';
import { decodeFeedMessage, VEHICLE_STATUS } from '../src/gtfsRealtime.js';
import { complexById } from '../src/stations.js';
import { buildTrains } from '../src/trains.js';

const NOW_MS = 1700000000000;
const NOW_SEC = NOW_MS / 1000;

describe('buildTrains', () => {
  const complex = complexById('611'); // Times Sq
  const feed = decodeFeedMessage(
    encodeFeedMessage({
      header: { timestamp: NOW_SEC },
      entities: [
        {
          id: 'tuA',
          tripUpdate: {
            trip: { tripId: 'A1', routeId: 'A' },
            stopTimeUpdates: [
              { stopId: '127N', arrival: NOW_SEC + 120 },
              { stopId: 'A09N', arrival: NOW_SEC + 600 },
            ],
          },
        },
        {
          id: 'vA',
          vehicle: {
            trip: { tripId: 'A1', routeId: 'A' },
            stopId: '127N', // Times Sq member -> atSelected
            currentStatus: VEHICLE_STATUS.STOPPED_AT,
            timestamp: NOW_SEC - 5,
            position: { latitude: 40.7559, longitude: -73.9871, bearing: 0 },
          },
        },
        {
          id: 'vN',
          vehicle: {
            trip: { tripId: 'N1', routeId: 'N' },
            stopId: 'R20N', // Union Sq, not in this complex
            currentStatus: VEHICLE_STATUS.IN_TRANSIT_TO,
            timestamp: NOW_SEC - 10,
          },
        },
      ],
    }),
  );

  const result = buildTrains(feed, { now: NOW_MS, complex, routes: complex.routes });

  test('counts vehicles and ignores routes outside the filter', () => {
    expect(result.total).toBe(2);
    const labels = result.byRoute.map((r) => r.label).sort();
    expect(labels).toEqual(['A', 'N']);
  });

  test('describes location in plain English and flags the selected stop', () => {
    const stopped = result.trains[0];
    expect(stopped.label).toBe('A');
    expect(stopped.statusKind).toBe('stopped');
    expect(stopped.statusText).toBe('Stopped at Times Sq - 42 St');
    expect(stopped.atSelected).toBe(true);
    expect(stopped.directionLabel.length).toBeGreaterThan(0);
  });

  test('joins the destination from trip updates', () => {
    const stopped = result.trains.find((t) => t.tripId === 'A1');
    expect(stopped.destination).toBeTruthy();
  });

  test('sorts trains at the selected complex first', () => {
    expect(result.trains[0].atSelected).toBe(true);
    expect(result.trains[result.trains.length - 1].atSelected).toBe(false);
  });

  test('route filter can exclude everything', () => {
    const none = buildTrains(feed, { now: NOW_MS, routes: ['L'] });
    expect(none.total).toBe(0);
  });
});

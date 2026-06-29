import { encodeFeedMessage } from '../src/sampleFeed.js';
import { decodeFeedMessage } from '../src/gtfsRealtime.js';
import { complexById } from '../src/stations.js';
import { buildArrivals } from '../src/arrivals.js';

const NOW_MS = 1700000000000;
const NOW_SEC = NOW_MS / 1000;

function tripEntity(route, stopId, time) {
  return {
    id: `${route}-${stopId}-${time}`,
    tripUpdate: {
      trip: { tripId: `${route}-${time}`, routeId: route },
      stopTimeUpdates: [{ stopId, arrival: time }],
      timestamp: NOW_SEC,
    },
  };
}

describe('buildArrivals', () => {
  const complex = complexById('611'); // Times Sq
  const feed = decodeFeedMessage(
    encodeFeedMessage({
      header: { timestamp: NOW_SEC },
      entities: [
        tripEntity('1', '127N', NOW_SEC + 120),
        tripEntity('1', '127N', NOW_SEC + 360),
        tripEntity('2', '127S', NOW_SEC + 60),
        tripEntity('3', '127N', NOW_SEC - 120), // already departed -> dropped
      ],
    }),
  );

  const board = buildArrivals(feed, complex, { now: NOW_MS });

  test('splits into north and south lanes', () => {
    expect(board.directions.map((d) => d.dir)).toEqual(['N', 'S']);
    expect(board.complexId).toBe('611');
    expect(board.name).toBe('Times Sq - 42 St');
  });

  test('sorts each lane soonest-first and computes countdowns', () => {
    const north = board.directions[0].trains;
    expect(north).toHaveLength(2);
    expect(north[0].route).toBe('1');
    expect(north[0].minutes).toBe(2);
    expect(north[0].countdown).toBe('2 min');
    expect(north[1].minutes).toBe(6);
  });

  test('drops past trains and totals upcoming', () => {
    const south = board.directions[1].trains;
    expect(south).toHaveLength(1);
    expect(south[0].route).toBe('2');
    expect(south[0].minutes).toBe(1);
    expect(board.totalUpcoming).toBe(3);
  });

  test('respects perDirection cap', () => {
    const many = decodeFeedMessage(
      encodeFeedMessage({
        header: { timestamp: NOW_SEC },
        entities: Array.from({ length: 10 }, (_, i) => tripEntity('1', '127N', NOW_SEC + 60 * (i + 1))),
      }),
    );
    const capped = buildArrivals(many, complex, { now: NOW_MS, perDirection: 3 });
    expect(capped.directions[0].trains).toHaveLength(3);
  });

  test('null feed yields empty lanes without throwing', () => {
    const empty = buildArrivals(null, complex, { now: NOW_MS });
    expect(empty.totalUpcoming).toBe(0);
  });
});

import { buildSampleLineFeed, buildSampleAlertsFeed } from '../src/sampleFeed.js';
import { decodeFeedMessage } from '../src/gtfsRealtime.js';
import { complexById } from '../src/stations.js';
import { buildArrivals } from '../src/arrivals.js';
import { buildTrains } from '../src/trains.js';
import { buildServiceStatus } from '../src/status.js';

const NOW_MS = 1700000000000;

describe('buildSampleLineFeed', () => {
  const complex = complexById('611');
  const feed = decodeFeedMessage(buildSampleLineFeed({ now: NOW_MS, complex }));

  test('produces trip updates and vehicles for the complex routes', () => {
    expect(feed.entities.length).toBeGreaterThan(0);
    expect(feed.entities.some((e) => e.tripUpdate)).toBe(true);
    expect(feed.entities.some((e) => e.vehicle)).toBe(true);
  });

  test('feeds the arrival board for the selected complex', () => {
    const board = buildArrivals(feed, complex, { now: NOW_MS });
    expect(board.totalUpcoming).toBeGreaterThan(0);
    expect(board.directions[0].trains.length).toBeGreaterThan(0);
    expect(board.directions[1].trains.length).toBeGreaterThan(0);
  });

  test('feeds the trains panel', () => {
    const trains = buildTrains(feed, { now: NOW_MS, complex, routes: complex.routes });
    expect(trains.total).toBeGreaterThan(0);
  });

  test('is deterministic for a given now', () => {
    const a = buildSampleLineFeed({ now: NOW_MS, complex });
    const b = buildSampleLineFeed({ now: NOW_MS, complex });
    expect(Array.from(a)).toEqual(Array.from(b));
  });
});

describe('buildSampleAlertsFeed', () => {
  const status = buildServiceStatus(decodeFeedMessage(buildSampleAlertsFeed({ now: NOW_MS })), { now: NOW_MS });

  test('has active disruptions and planned work', () => {
    expect(status.activeCount).toBeGreaterThanOrEqual(1);
    expect(status.plannedCount).toBeGreaterThanOrEqual(1);
  });

  test('A shows delays and G shows no service', () => {
    expect(status.routes.find((r) => r.label === 'A').kind).toBe('warn');
    expect(status.routes.find((r) => r.label === 'G').kind).toBe('bad');
  });

  test('an unaffected route stays Good Service', () => {
    expect(status.routes.find((r) => r.label === 'L').level).toBe('GOOD');
  });
});

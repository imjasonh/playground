import { encodeFeedMessage } from '../src/sampleFeed.js';
import { decodeFeedMessage } from '../src/gtfsRealtime.js';
import { buildServiceStatus, classifyAlert, LEVELS } from '../src/status.js';

const NOW_MS = 1700000000000;
const NOW_SEC = NOW_MS / 1000;

describe('classifyAlert', () => {
  test('maps effects to levels', () => {
    expect(classifyAlert({ effect: 3 }).level).toBe('DELAYS');
    expect(classifyAlert({ effect: 1 })).toEqual({ level: 'DISRUPTION', label: 'No Service' });
    expect(classifyAlert({ effect: 2 })).toEqual({ level: 'DISRUPTION', label: 'Reduced Service' });
  });

  test('detects planned work from text', () => {
    expect(classifyAlert({ effect: 6, headerText: 'Planned Work this weekend' }).level).toBe('PLANNED');
  });

  test('falls back to text keywords', () => {
    expect(classifyAlert({ headerText: 'Northbound 4 trains are delayed' }).level).toBe('DELAYS');
    expect(classifyAlert({ effect: 6, headerText: 'Trains skip 23 St' })).toEqual({
      level: 'INFO',
      label: 'Service Change',
    });
  });
});

describe('buildServiceStatus', () => {
  const feed = decodeFeedMessage(
    encodeFeedMessage({
      header: { timestamp: NOW_SEC },
      entities: [
        {
          id: 'a1',
          alert: {
            effect: 3,
            headerText: 'A delays',
            informedEntities: [{ routeId: 'A' }],
            activePeriods: [{ start: NOW_SEC - 100, end: NOW_SEC + 100 }],
          },
        },
        {
          id: 'a2',
          alert: {
            effect: 6,
            headerText: 'Planned Work: F runs local',
            informedEntities: [{ routeId: 'F' }],
            activePeriods: [{ start: NOW_SEC + 1000, end: NOW_SEC + 2000 }],
          },
        },
        {
          id: 'a3',
          alert: {
            effect: 1,
            headerText: 'No C service (expired)',
            informedEntities: [{ routeId: 'C' }],
            activePeriods: [{ start: NOW_SEC - 2000, end: NOW_SEC - 1000 }],
          },
        },
      ],
    }),
  );

  const status = buildServiceStatus(feed, { now: NOW_MS });
  const byLabel = (label) => status.routes.find((r) => r.label === label);

  test('active delays elevate the route', () => {
    const a = byLabel('A');
    expect(a.level).toBe('DELAYS');
    expect(a.kind).toBe('warn');
    expect(a.statusLabel).toBe('Delays');
  });

  test('planned (future) work does not elevate but is attached', () => {
    const f = byLabel('F');
    expect(f.level).toBe('GOOD');
    expect(f.statusLabel).toBe('Good Service');
    expect(f.alerts).toHaveLength(1);
  });

  test('expired alerts are excluded entirely', () => {
    const c = byLabel('C');
    expect(c.level).toBe('GOOD');
    expect(c.alerts).toHaveLength(0);
  });

  test('routes with no alerts read Good Service', () => {
    expect(byLabel('7').level).toBe('GOOD');
    expect(byLabel('7').kind).toBe('good');
  });

  test('counts and ordering', () => {
    expect(status.activeCount).toBe(1);
    expect(status.plannedCount).toBe(1);
    expect(status.alerts[0].rank).toBe(LEVELS.DELAYS.rank);
  });
});

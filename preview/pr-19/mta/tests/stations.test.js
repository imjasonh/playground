import {
  splitStopId,
  COMPLEXES,
  complexById,
  complexForStation,
  terminusName,
  searchComplexes,
  STATION_BY_ID,
} from '../src/stations.js';

describe('splitStopId', () => {
  test('splits a known station + direction', () => {
    expect(splitStopId('R16N')).toEqual({ stationId: 'R16', direction: 'N' });
    expect(splitStopId('127S')).toEqual({ stationId: '127', direction: 'S' });
  });

  test('handles a bare station id (no direction)', () => {
    expect(splitStopId('A27')).toEqual({ stationId: 'A27', direction: '' });
  });

  test('empty input is safe', () => {
    expect(splitStopId('')).toEqual({ stationId: '', direction: '' });
  });
});

describe('complexes', () => {
  test('every station resolves to a complex', () => {
    for (const station of STATION_BY_ID.values()) {
      expect(complexForStation(station.id)).not.toBeNull();
    }
  });

  test('Times Sq complex (611) merges all its platforms and routes', () => {
    const complex = complexById('611');
    expect(complex).not.toBeNull();
    expect(complex.name).toBe('Times Sq - 42 St');
    for (const id of ['R16', '127', '725', '902', 'A27']) {
      expect(complex.memberIds.has(id)).toBe(true);
    }
    for (const route of ['1', '2', '3', '7', 'N', 'Q', 'R', 'W', 'A', 'C', 'E', 'S']) {
      expect(complex.routes).toContain(route);
    }
  });

  test('direction labels are present', () => {
    const complex = complexById('611');
    expect(typeof complex.north).toBe('string');
    expect(complex.north.length).toBeGreaterThan(0);
  });
});

describe('terminusName', () => {
  test('returns the last stop name', () => {
    expect(terminusName([{ stopId: 'A27N' }, { stopId: '127N' }])).toBe('Times Sq - 42 St');
  });

  test('empty list -> empty string', () => {
    expect(terminusName([])).toBe('');
  });
});

describe('searchComplexes', () => {
  test('empty query returns busiest hubs first', () => {
    const results = searchComplexes('');
    expect(results.length).toBeGreaterThan(0);
    // Times Sq (the biggest complex) should be at/near the top.
    expect(results.slice(0, 3).some((c) => c.id === '611')).toBe(true);
  });

  test('name query finds Times Sq', () => {
    const results = searchComplexes('times sq');
    expect(results.some((c) => c.id === '611')).toBe(true);
  });

  test('a single-letter line query surfaces that line', () => {
    const results = searchComplexes('L');
    expect(results.length).toBeGreaterThan(0);
    expect(results.some((c) => c.routes.includes('L'))).toBe(true);
  });

  test('respects the limit', () => {
    expect(searchComplexes('st', 5).length).toBeLessThanOrEqual(5);
  });
});

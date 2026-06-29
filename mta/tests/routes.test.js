import { normalizeRouteId, routeStyle, sortRoutes, ROUTE_ORDER } from '../src/routes.js';

describe('normalizeRouteId', () => {
  test('folds SI/SIR onto SIR', () => {
    expect(normalizeRouteId('SI')).toBe('SIR');
    expect(normalizeRouteId('SIR')).toBe('SIR');
  });

  test('folds shuttle ids onto S', () => {
    for (const id of ['GS', 'FS', 'H', 'S']) expect(normalizeRouteId(id)).toBe('S');
  });

  test('strips express diamond suffix', () => {
    expect(normalizeRouteId('6X')).toBe('6');
    expect(normalizeRouteId('7X')).toBe('7');
  });

  test('trims and passes through normal ids', () => {
    expect(normalizeRouteId(' 1 ')).toBe('1');
    expect(normalizeRouteId('Q')).toBe('Q');
  });
});

describe('routeStyle', () => {
  test('N/Q/R/W use black text on yellow', () => {
    const n = routeStyle('N');
    expect(n.color.toLowerCase()).toBe('#fccc0a');
    expect(n.text).toBe('#000000');
  });

  test('1 is red, A is blue', () => {
    expect(routeStyle('1').color).toBe('#ee352e');
    expect(routeStyle('A').color).toBe('#0039a6');
  });

  test('unknown route gets a neutral bullet but keeps its label', () => {
    const style = routeStyle('ZZ');
    expect(style.label).toBe('ZZ');
    expect(style.color).toBeTruthy();
  });
});

describe('sortRoutes', () => {
  test('orders by ROUTE_ORDER', () => {
    expect(sortRoutes(['SIR', 'A', '1', 'N'])).toEqual(['1', 'A', 'N', 'SIR']);
  });

  test('orders by canonical rank while preserving the original tokens', () => {
    // '6X' ranks with '6' and 'SI' ranks with 'SIR', but the input strings are kept.
    expect(sortRoutes(new Set(['SI', '6X', '1']))).toEqual(['1', '6X', 'SI']);
  });

  test('ROUTE_ORDER has no duplicates', () => {
    expect(new Set(ROUTE_ORDER).size).toBe(ROUTE_ORDER.length);
  });
});

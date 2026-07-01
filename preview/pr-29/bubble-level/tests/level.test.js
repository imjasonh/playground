import {
  DEFAULT_SENSITIVITY_DEG,
  applyCalibration,
  axisOffsets,
  bubbleOffset,
  bubbleVector,
  clamp,
  isLevel,
  normalizeAngle,
  tiltAngle,
  tiltComponents,
} from '../src/level.js';

describe('clamp', () => {
  test('bounds values and rejects non-finite input', () => {
    expect(clamp(5, 0, 10)).toBe(5);
    expect(clamp(-3, 0, 10)).toBe(0);
    expect(clamp(42, 0, 10)).toBe(10);
    expect(clamp(Number.NaN, -1, 1)).toBe(-1);
  });
});

describe('normalizeAngle', () => {
  test('wraps into [-180, 180)', () => {
    expect(normalizeAngle(0)).toBe(0);
    expect(normalizeAngle(190)).toBe(-170);
    expect(normalizeAngle(-190)).toBe(170);
    expect(normalizeAngle(360)).toBe(0);
    expect(normalizeAngle(540)).toBe(-180);
  });

  test('treats non-finite as zero', () => {
    expect(normalizeAngle(Number.NaN)).toBe(0);
    expect(normalizeAngle(undefined)).toBe(0);
  });
});

describe('bubbleOffset direction (bubble floats to the high side)', () => {
  test('is centered when the surface is flat', () => {
    const { x, y } = bubbleOffset(0, 0);
    expect(x).toBeCloseTo(0, 6);
    expect(y).toBeCloseTo(0, 6);
    expect(isLevel(0, 0)).toBe(true);
  });

  test('raising the right edge (gamma < 0) sends the bubble right', () => {
    expect(bubbleOffset(0, -10).x).toBeGreaterThan(0);
  });

  test('dropping the right edge (gamma > 0) sends the bubble left', () => {
    expect(bubbleOffset(0, 10).x).toBeLessThan(0);
  });

  test('raising the top edge (beta > 0) sends the bubble up the screen', () => {
    expect(bubbleOffset(10, 0).y).toBeLessThan(0);
  });

  test('dropping the top edge (beta < 0) sends the bubble down the screen', () => {
    expect(bubbleOffset(-10, 0).y).toBeGreaterThan(0);
  });
});

describe('bubbleOffset magnitude', () => {
  test('reaches the vial edge at the sensitivity angle', () => {
    const { x } = bubbleOffset(0, DEFAULT_SENSITIVITY_DEG);
    expect(Math.abs(x)).toBeCloseTo(1, 5);
  });

  test('never leaves the unit disk, even for extreme tilt', () => {
    for (const beta of [-170, -90, -45, 45, 90, 170]) {
      for (const gamma of [-90, -45, 45, 90]) {
        const { x, y } = bubbleOffset(beta, gamma);
        expect(Math.hypot(x, y)).toBeLessThanOrEqual(1 + 1e-9);
      }
    }
  });

  test('a smaller sensitivity produces a larger deflection for the same tilt', () => {
    const gentle = Math.abs(bubbleOffset(0, 5, 45).x);
    const sensitive = Math.abs(bubbleOffset(0, 5, 15).x);
    expect(sensitive).toBeGreaterThan(gentle);
  });
});

describe('tiltAngle', () => {
  test('is zero when flat and grows with tilt', () => {
    expect(tiltAngle(0, 0)).toBeCloseTo(0, 6);
    expect(tiltAngle(0, 10)).toBeGreaterThan(tiltAngle(0, 5));
  });

  test('matches the single-axis angle when only one axis tilts', () => {
    expect(tiltAngle(0, 12)).toBeCloseTo(12, 4);
    expect(tiltAngle(20, 0)).toBeCloseTo(20, 4);
  });

  test('is symmetric for opposite tilts', () => {
    expect(tiltAngle(0, 15)).toBeCloseTo(tiltAngle(0, -15), 6);
    expect(tiltAngle(15, 0)).toBeCloseTo(tiltAngle(-15, 0), 6);
  });

  test('reads 90 degrees when the screen is vertical', () => {
    expect(tiltAngle(90, 0)).toBeCloseTo(90, 4);
  });
});

describe('tiltComponents', () => {
  test('reports zero on all axes when flat', () => {
    const c = tiltComponents(0, 0);
    expect(c.x).toBeCloseTo(0, 6);
    expect(c.y).toBeCloseTo(0, 6);
    expect(c.total).toBeCloseTo(0, 6);
  });

  test('x is positive when the right edge is raised', () => {
    expect(tiltComponents(0, -8).x).toBeGreaterThan(0);
    expect(tiltComponents(0, 8).x).toBeLessThan(0);
  });

  test('y is positive when the top/back edge is raised', () => {
    expect(tiltComponents(8, 0).y).toBeGreaterThan(0);
    expect(tiltComponents(-8, 0).y).toBeLessThan(0);
  });

  test('total is never negative', () => {
    expect(tiltComponents(-20, -20).total).toBeGreaterThanOrEqual(0);
  });
});

describe('axisOffsets', () => {
  test('clamps each axis independently', () => {
    const { x, y } = axisOffsets(2, 80);
    expect(Math.abs(x)).toBeCloseTo(1, 5);
    expect(Math.abs(y)).toBeLessThan(1);
  });

  test('is centered when flat', () => {
    const { x, y } = axisOffsets(0, 0);
    expect(x).toBeCloseTo(0, 6);
    expect(y).toBeCloseTo(0, 6);
  });
});

describe('isLevel', () => {
  test('respects the tolerance', () => {
    expect(isLevel(0, 0.5, 1)).toBe(true);
    expect(isLevel(0, 0.5, 0.1)).toBe(false);
    expect(isLevel(0, 3, 1)).toBe(false);
  });
});

describe('applyCalibration', () => {
  test('subtracts the stored zero-offset', () => {
    const adjusted = applyCalibration({ beta: 5, gamma: -3 }, { beta: 2, gamma: -1 });
    expect(adjusted.beta).toBeCloseTo(3, 6);
    expect(adjusted.gamma).toBeCloseTo(-2, 6);
  });

  test('normalizes the result and tolerates missing fields', () => {
    expect(applyCalibration({ beta: 179 }, { beta: -5 }).beta).toBeCloseTo(-176, 6);
    expect(applyCalibration(null, null)).toEqual({ beta: 0, gamma: 0 });
  });

  test('calibrating against the current reading yields a level result', () => {
    const reading = { beta: 4, gamma: 7 };
    const adjusted = applyCalibration(reading, reading);
    expect(isLevel(adjusted.beta, adjusted.gamma)).toBe(true);
  });
});

describe('bubbleVector', () => {
  test('handles non-finite inputs as zero', () => {
    const v = bubbleVector(Number.NaN, undefined);
    expect(v.x).toBeCloseTo(0, 6);
    expect(v.y).toBeCloseTo(0, 6);
  });
});
